"""
Sound effects for Cube Shooter.

Drop audio files into the "sounds" folder (next to the game, or next to the .exe). A file plays when its event
happens - the file name (without extension) picks the event. Any of the names listed for an event work, so
"shoot.wav", "Shot.mp3" and "gun.ogg" all play when you shoot. Missing files are simply silent.

Files are looked up again every couple of seconds, so new sounds work without restarting the game.
"""

import os
import sys
import time

import pygame

EXTENSIONS = (".wav", ".ogg", ".mp3", ".flac")

# event -> file names that count for it (lower case, no extension)
EVENTS = {
    "shoot":              ["shoot", "shot", "gun", "fire", "player_shoot"],
    "enemy_death":        ["enemy_death", "enemy_and_player_die", "enemy_die", "kill", "enemy_killed", "pop", "explode_enemy"],
    "coin":               ["coin", "coin_pickup", "pickup", "collect"],
    "player_death":       ["player_death", "enemy_and_player_die", "death", "die", "game_over", "gameover", "lose"],
    "wave_complete":      ["wave_complete", "wave", "wave_clear", "win"],
    "boss_wave_complete": ["boss_wave_complete", "boss_complete", "boss_win", "victory"],
    "boss_spawn":         ["boss_spawn", "boss_start", "boss"],
    "boss_hit":           ["boss_hit", "boss_damage", "hit"],
    "boss_death":         ["boss_death", "boss_die", "boss_defeated"],
    "shield_block":       ["shield_block", "shield_hit", "boss_shield", "block_shot"],
    "shot_clash":         ["shot_clash", "2_lasers_hit", "lasers_hit", "clash", "bullet_break", "break"],
    "teal_explode":       ["teal_explode", "explosion", "explode", "boom"],
    "block_damage":       ["block_damage", "block_hit"],
    "buy":                ["buy", "buy_something", "purchase", "repair", "upgrade", "shop"],
    "shield":             ["shield", "shield_on", "player_shield"],
    "violet_grab":        ["violet_grab", "grab", "tentacle_grab"],
    "tentacle_cut":       ["tentacle_cut", "tentacle_hit", "cut"],
}

MIN_GAP = 0.04       # The same sound can't restart faster than this (a 30-enemy wipe shouldn't be deafening)
RESCAN_EVERY = 2.0

_ready = False
_files = {}          # event -> path
_cache = {}          # path -> Sound
_last_play = {}
_last_scan = -99.0


def folders():
    """Next to the .exe/.py first (the player's own sounds), then sounds bundled inside the .exe."""
    here = (os.path.dirname(os.path.abspath(sys.executable)) if getattr(sys, "frozen", False)
            else os.path.dirname(os.path.abspath(__file__)))
    found = [os.path.join(here, "sounds")]
    bundled = getattr(sys, "_MEIPASS", None)
    if bundled:
        found.append(os.path.join(bundled, "sounds"))
    return found


def _init():
    global _ready
    if _ready:
        return True
    try:
        if not pygame.mixer.get_init():
            pygame.mixer.init()
        pygame.mixer.set_num_channels(32)
        _ready = True
    except pygame.error:
        pass
    return _ready


def _scan():
    global _last_scan
    _last_scan = time.monotonic()
    names = {}
    for folder in reversed(folders()):  # Later wins, so the folder next to the game beats the bundled one
        try:
            for entry in os.listdir(folder):
                stem, ext = os.path.splitext(entry)
                if ext.lower() in EXTENSIONS:
                    names[_key(stem)] = os.path.join(folder, entry)
        except OSError:
            continue
    _files.clear()
    for event, aliases in EVENTS.items():
        for alias in [event] + aliases:
            if _key(alias) in names:
                _files[event] = names[_key(alias)]
                break


def _key(name):
    """CoinPickup, coin_pickup and "coin pickup" all count as the same name."""
    return "".join(ch for ch in name.lower() if ch.isalnum())


def play(event, volume=1.0):
    if not _init():
        return
    now = time.monotonic()
    if now - _last_scan > RESCAN_EVERY:
        _scan()
    path = _files.get(event)
    if not path or now - _last_play.get(event, -1) < MIN_GAP:
        return
    sound = _cache.get(path)
    if sound is None:
        try:
            sound = _cache[path] = pygame.mixer.Sound(path)
        except (pygame.error, OSError, FileNotFoundError):
            _files.pop(event, None)
            return
    sound.set_volume(volume)
    sound.play()
    _last_play[event] = now


# ---- Music: one song at a time, looked up by name like the sound effects ----
SONGS = {
    "barrier_shrink": ["barrier_shrink", "barier_shrink", "storm", "barrier_shrink_music"],
}
_song = None       # (name, run) currently loaded
_song_paused = False


def _song_path(name):
    if time.monotonic() - _last_scan > RESCAN_EVERY:
        _scan()
    for folder in folders():
        try:
            entries = os.listdir(folder)
        except OSError:
            continue
        for alias in [name] + SONGS.get(name, []):
            for entry in entries:
                stem, ext = os.path.splitext(entry)
                if ext.lower() in EXTENSIONS and _key(stem) == _key(alias):
                    return os.path.join(folder, entry)
    return None


def update_music(name, run=0, paused=False, volume=0.7):
    """Call every frame with the song that should be playing (or None). A new `run` restarts it from the top."""
    global _song, _song_paused
    if not _init():
        return
    wanted = (name, run) if name else None
    if wanted != _song:
        pygame.mixer.music.stop()
        _song, _song_paused = wanted, False
        if name:
            path = _song_path(name)
            if path:
                try:
                    pygame.mixer.music.load(path)
                    pygame.mixer.music.set_volume(volume)
                    pygame.mixer.music.play()
                except pygame.error:
                    pass
    if _song and paused != _song_paused:
        (pygame.mixer.music.pause if paused else pygame.mixer.music.unpause)()
        _song_paused = paused
