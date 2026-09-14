"""Cube Shooter multiplayer server.

Small on purpose: it hands out 4-digit lobby codes, lets up to 4 players join a lobby, checks every player's
login with Supabase, and passes game messages between the players in a lobby. The host's game runs the match.

Messages are JSON over a WebSocket. From a game:
    {"t": "hello", "token": <Supabase access token>}     must be first; the server looks up the username
    {"t": "create"}                                      new lobby, you are the host
    {"t": "join", "code": "4829"}
    {"t": "leave"}
    {"t": "settings", "mode": "Waves", "map": "Grass"}   host only: shown to everyone in the lobby
    {"t": "start"}                                        host only
    {"t": "end"}                                          host only: match over, back to the lobby
    {"t": "relay", "d": {...}, "to": "name"}              game data; "to" is optional (default: everyone else)
To a game:
    {"t": "welcome", "name": "..."}
    {"t": "lobby", "code": "4829", "host": "...", "players": [...], "mode": ..., "map": ..., "started": false}
    {"t": "start", "mode": ..., "map": ..., "players": [...], "host": "..."}
    {"t": "end"}
    {"t": "relay", "from": "name", "d": {...}}
    {"t": "error", "msg": "..."}
"""
import asyncio
import json
import os
import secrets
import time
import urllib.request

import websockets

SUPABASE_URL = os.environ.get("SUPABASE_URL", "https://ahjhfwucsivhzhqcjyau.supabase.co")
PUBLISHABLE_KEY = os.environ.get("SUPABASE_KEY", "sb_publishable_MUfA7Qcl32e-XmzP9mYYGg_7AKqOzBf")
PORT = int(os.environ.get("PORT", "8765"))
MAX_PLAYERS = 4
NO_SOLO_MODES = ("Tutorial", "Sandbox")
MAX_MESSAGE = 256 * 1024
RELAY_PER_SECOND = 120      # Per player; a game sends ~20-30 a second, this just stops floods

lobbies = {}                # code -> Lobby


class Lobby(object):
    def __init__(self, code, host):
        self.code = code
        self.host = host
        self.players = [host]  # Clients, in join order
        self.mode = "Waves"
        self.map = "Grass"
        self.started = False

    def names(self):
        return [p.name for p in self.players]

    def info(self):
        return {"t": "lobby", "code": self.code, "host": self.host.name, "players": self.names(),
                "mode": self.mode, "map": self.map, "started": self.started}


class Client(object):
    def __init__(self, ws):
        self.ws = ws
        self.name = None
        self.lobby = None
        self.window_start = time.monotonic()
        self.window_count = 0


def lookup_username(token):
    """Ask Supabase who this token belongs to (with the player's own token, so only their row is visible)."""
    req = urllib.request.Request(SUPABASE_URL + "/rest/v1/players?select=username",
                                 headers={"apikey": PUBLISHABLE_KEY, "Authorization": "Bearer " + token})
    with urllib.request.urlopen(req, timeout=8) as resp:
        rows = json.loads(resp.read())
    return rows[0]["username"] if rows else None


async def send(client, message):
    try:
        await client.ws.send(json.dumps(message))
    except websockets.ConnectionClosed:
        pass


async def broadcast(lobby, message, skip=None):
    await asyncio.gather(*(send(p, message) for p in lobby.players if p is not skip))


def new_code():
    for _ in range(1000):
        code = "%04d" % secrets.randbelow(10000)
        if code not in lobbies:
            return code
    raise RuntimeError("no free lobby codes")


async def leave_lobby(client):
    lobby = client.lobby
    if lobby is None:
        return
    client.lobby = None
    if client in lobby.players:
        lobby.players.remove(client)
    if not lobby.players:
        lobbies.pop(lobby.code, None)
        return
    if lobby.host is client:
        lobby.host = lobby.players[0]  # Next player in line becomes the host
        if lobby.started:
            lobby.started = False      # The match lived on the old host's game, so it ends
            await broadcast(lobby, {"t": "end", "reason": "The host left"})
    await broadcast(lobby, lobby.info())


async def handle(client, msg):
    kind = msg.get("t")
    if client.name is None:
        if kind != "hello":
            return await send(client, {"t": "error", "msg": "Log in first"})
        try:
            name = await asyncio.to_thread(lookup_username, str(msg.get("token", "")))
        except Exception:
            name = None
        if not name:
            await send(client, {"t": "error", "msg": "Login expired - log in again", "fatal": True})
            return await client.ws.close()
        client.name = name
        return await send(client, {"t": "welcome", "name": name})

    lobby = client.lobby
    if kind == "create":
        await leave_lobby(client)
        client.lobby = Lobby(new_code(), client)
        lobbies[client.lobby.code] = client.lobby
        await send(client, client.lobby.info())
    elif kind == "join":
        code = str(msg.get("code", "")).strip()
        target = lobbies.get(code)
        if target is None:
            return await send(client, {"t": "error", "msg": "No lobby with code %s" % code})
        if target is lobby:
            return await send(client, lobby.info())
        if len(target.players) >= MAX_PLAYERS:
            return await send(client, {"t": "error", "msg": "That lobby is full (4 players)"})
        if target.started:
            return await send(client, {"t": "error", "msg": "That game has already started"})
        if any(p.name.lower() == client.name.lower() for p in target.players):
            return await send(client, {"t": "error", "msg": "You're already in that lobby"})
        await leave_lobby(client)
        target.players.append(client)
        client.lobby = target
        await broadcast(target, target.info())
    elif kind == "leave":
        await leave_lobby(client)
        await send(client, {"t": "lobby", "code": None, "players": [], "host": None})
    elif lobby is None:
        await send(client, {"t": "error", "msg": "You're not in a lobby"})
    elif kind == "settings":
        if client is lobby.host and not lobby.started:
            lobby.mode = str(msg.get("mode", lobby.mode))[:32]
            lobby.map = str(msg.get("map", lobby.map))[:32]
            await broadcast(lobby, lobby.info())
    elif kind == "start":
        if client is not lobby.host or lobby.started:
            return
        if lobby.mode in NO_SOLO_MODES:
            return await send(client, {"t": "error", "msg": "%s is solo only" % lobby.mode})
        lobby.started = True
        await broadcast(lobby, {"t": "start", "mode": lobby.mode, "map": lobby.map,
                                "players": lobby.names(), "host": lobby.host.name})
        await broadcast(lobby, lobby.info())
    elif kind == "end":
        if client is lobby.host and lobby.started:
            lobby.started = False
            await broadcast(lobby, {"t": "end"})
            await broadcast(lobby, lobby.info())
    elif kind == "relay":
        now = time.monotonic()
        if now - client.window_start >= 1.0:
            client.window_start, client.window_count = now, 0
        client.window_count += 1
        if client.window_count > RELAY_PER_SECOND:
            return
        out = {"t": "relay", "from": client.name, "d": msg.get("d")}
        to = msg.get("to")
        if to:
            target = next((p for p in lobby.players if p.name == to), None)
            if target:
                await send(target, out)
        else:
            await broadcast(lobby, out, skip=client)


async def connection(ws):
    client = Client(ws)
    try:
        async for raw in ws:
            try:
                msg = json.loads(raw)
            except ValueError:
                continue
            if isinstance(msg, dict):
                await handle(client, msg)
    except websockets.ConnectionClosed:
        pass
    finally:
        await leave_lobby(client)


async def health(connection, request):
    """Plain HTTP GET / answers "ok" (Fly.io's health check); WebSocket upgrades go through."""
    if request.headers.get("Upgrade", "").lower() != "websocket":
        return connection.respond(200, "Cube Shooter server ok (2)\n")


async def main():
    async with websockets.serve(connection, "0.0.0.0", PORT, max_size=MAX_MESSAGE, process_request=health,
                                ping_interval=20, ping_timeout=20, close_timeout=2):
        print("Cube Shooter server listening on port", PORT, flush=True)
        await asyncio.Future()


if __name__ == "__main__":
    asyncio.run(main())
