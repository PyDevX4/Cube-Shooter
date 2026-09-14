"""The game's connection to the Cube Shooter multiplayer server (see server/server.py).

The network runs on its own thread so the game never waits on it. The game calls the send methods, and
once a frame calls poll() to get whatever arrived. Plain fields (status, lobby, error) are safe to read any time.
"""
import asyncio
import json
import os
import queue
import threading
import time

import websockets

SERVER_URL = os.environ.get("CUBE_SHOOTER_SERVER", "wss://cube-shooter-server.onrender.com")


class Net(object):
    def __init__(self, url=SERVER_URL):
        self.url = url
        self.status = "offline"   # offline, connecting, online
        self.name = None          # Our username, once the server has checked our login
        self.lobby = None         # Latest lobby info from the server, or None
        self.error = ""
        self.inbox = queue.Queue()
        self._loop = None
        self._ws = None
        self._thread = None
        self.connect_started = 0.0

    @property
    def waking_up(self):
        """Still connecting after a few seconds: the free server was asleep and is starting up."""
        return self.status == "connecting" and time.monotonic() - self.connect_started > 3

    # ---- connection ----
    def connect(self, token):
        if self.status != "offline":
            return
        self.status, self.error = "connecting", ""
        self.connect_started = time.monotonic()
        self._thread = threading.Thread(target=self._run, args=(token,), name="cube-net", daemon=True)
        self._thread.start()

    def close(self):
        loop, ws = self._loop, self._ws
        if loop and ws:
            async def go():
                try:
                    # Say we're leaving first: a hosting proxy can hold up the close itself for many seconds
                    await ws.send(json.dumps({"t": "leave"}))
                except websockets.ConnectionClosed:
                    pass
                await ws.close()
            asyncio.run_coroutine_threadsafe(go(), loop)
        self.lobby = None

    def _run(self, token):
        self._loop = asyncio.new_event_loop()
        try:
            self._loop.run_until_complete(self._main(token))
        finally:
            self._loop.close()
            self._loop = self._ws = None
            self.status, self.lobby = "offline", None
            self.inbox.put({"t": "disconnected"})

    async def _main(self, token):
        try:
            async with websockets.connect(self.url, open_timeout=90, close_timeout=2, max_size=1024 * 1024) as ws:
                self._ws = ws
                await ws.send(json.dumps({"t": "hello", "token": token}))
                async for raw in ws:
                    try:
                        msg = json.loads(raw)
                    except ValueError:
                        continue
                    kind = msg.get("t")
                    if kind == "welcome":
                        self.name, self.status = msg["name"], "online"
                    elif kind == "lobby":
                        self.lobby = msg if msg.get("code") else None
                    elif kind == "error":
                        self.error = msg.get("msg", "")
                        if msg.get("fatal"):
                            break  # The server turned us away (bad login)
                    self.inbox.put(msg)
        except (OSError, websockets.InvalidURI, websockets.InvalidHandshake, asyncio.TimeoutError) as err:
            self.error = "Can't reach the multiplayer server"
        except websockets.ConnectionClosed:
            if not self.error:
                self.error = "Disconnected from the multiplayer server"

    def _send(self, message):
        loop, ws = self._loop, self._ws
        if loop is None or ws is None:
            return False
        data = json.dumps(message)

        async def go():
            try:
                await ws.send(data)
            except websockets.ConnectionClosed:
                pass
        asyncio.run_coroutine_threadsafe(go(), loop)
        return True

    # ---- what the game calls ----
    def poll(self):
        """Everything received since the last call, oldest first."""
        out = []
        while True:
            try:
                out.append(self.inbox.get_nowait())
            except queue.Empty:
                return out

    def create_lobby(self):
        self._send({"t": "create"})

    def join_lobby(self, code):
        self.error = ""
        self._send({"t": "join", "code": code})

    def leave_lobby(self):
        self.lobby = None
        self._send({"t": "leave"})

    def send_settings(self, mode, map_name):
        self._send({"t": "settings", "mode": mode, "map": map_name})

    def start_match(self):
        self._send({"t": "start"})

    def end_match(self):
        self._send({"t": "end"})

    def relay(self, data, to=None):
        message = {"t": "relay", "d": data}
        if to:
            message["to"] = to
        self._send(message)

    @property
    def is_host(self):
        return bool(self.lobby and self.name and self.lobby.get("host") == self.name)
