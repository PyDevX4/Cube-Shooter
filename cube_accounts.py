"""Local player accounts for Cube Shooter.

Accounts (username + hashed password + saved progress) live in a JSON file next to the game.
Passwords are never stored: only a salted PBKDF2 hash, so nobody can read them from the save file.
This module also picks the daily Shop items, which are the same for every account on a given day.
"""
import datetime
import hashlib
import json
import os
import random
import secrets

import sys

# Next to the game. For a built .exe that means next to the .exe itself - not the temporary folder a one-file
# build unpacks into, which is deleted when the game closes (accounts would vanish every time).
_GAME_DIR = (os.path.dirname(os.path.abspath(sys.executable)) if getattr(sys, "frozen", False)
             else os.path.dirname(os.path.abspath(__file__)))
SAVE_PATH = os.environ.get("CUBE_SHOOTER_SAVE") or os.path.join(_GAME_DIR, "cube_shooter_save.json")
HASH_ROUNDS = 120_000  # Slow on purpose, so guessing passwords from a copied save file is impractical


def load_save():
    """Read the save file (or start an empty one if it's missing or unreadable)."""
    try:
        with open(SAVE_PATH, encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, ValueError):
        data = {}
    data.setdefault("accounts", {})
    data.setdefault("last_user", "")
    return data


def write_save(data):
    """Write to a temp file first and then swap it in, so a crash mid-save can't corrupt the save."""
    tmp_path = SAVE_PATH + ".tmp"
    with open(tmp_path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2)
    os.replace(tmp_path, SAVE_PATH)


# "Remember me" lives outside the game folder, so it stays on this device even if the game and its
# save file are copied somewhere else. The save file only ever holds a hash of the token.
REMEMBER_PATH = os.environ.get("CUBE_SHOOTER_REMEMBER") or os.path.join(
    os.environ.get("LOCALAPPDATA") or os.path.expanduser("~"), "CubeShooter", "remember_me.json")


def remember_account(data, name):
    """Remember this account on this device, so the game logs straight in next time."""
    account = data["accounts"][name.lower()]
    token = secrets.token_hex(32)
    account["remember_hash"] = hashlib.sha256(token.encode("utf-8")).hexdigest()
    write_save(data)
    os.makedirs(os.path.dirname(REMEMBER_PATH), exist_ok=True)
    with open(REMEMBER_PATH, "w", encoding="utf-8") as f:
        json.dump({"username": account["name"], "token": token}, f)


def forget_remembered(data, name=None):
    """Stop remembering: delete this device's token, and the account's matching hash if a name is given."""
    try:
        os.remove(REMEMBER_PATH)
    except OSError:
        pass
    account = data["accounts"].get(name.lower()) if name else None
    if account is not None and account.pop("remember_hash", None) is not None:
        write_save(data)


def remembered_account(data):
    """The account this device remembers, if its token still matches (otherwise None)."""
    try:
        with open(REMEMBER_PATH, encoding="utf-8") as f:
            remembered = json.load(f)
        account = data["accounts"].get(str(remembered["username"]).lower())
        token = str(remembered["token"])
    except (OSError, ValueError, KeyError, TypeError):
        return None
    if account is None or not account.get("remember_hash"):
        return None
    if not secrets.compare_digest(account["remember_hash"], hashlib.sha256(token.encode("utf-8")).hexdigest()):
        return None
    return account


def _hash_password(password, salt_hex):
    return hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), bytes.fromhex(salt_hex), HASH_ROUNDS).hex()


def account_names(data):
    return [account["name"] for account in data["accounts"].values()]


def create_account(data, name, password):
    """Create a new account. Returns (account or None, message). Usernames ignore upper/lower case."""
    name = name.strip()
    if not 3 <= len(name) <= 16:
        return None, "Username must be 3-16 characters"
    if len(password) < 4:
        return None, "Password must be at least 4 characters"
    key = name.lower()
    if key in data["accounts"]:
        return None, "That username is taken"
    salt = secrets.token_hex(16)
    account = {"name": name, "salt": salt, "password_hash": _hash_password(password, salt), "progress": {}}
    data["accounts"][key] = account
    data["last_user"] = name
    write_save(data)
    return account, f"Welcome, {name}!"


def check_login(data, name, password):
    """Check a username and password. Returns (account or None, message)."""
    account = data["accounts"].get(name.strip().lower())
    if account is None or not secrets.compare_digest(account["password_hash"], _hash_password(password, account["salt"])):
        return None, "Wrong username or password"
    data["last_user"] = account["name"]
    write_save(data)
    return account, f"Welcome back, {account['name']}!"


def save_progress(data, name, progress):
    """Store an account's progress and write the save file."""
    account = data["accounts"].get(name.lower())
    if account is not None:
        account["progress"] = progress
        write_save(data)


def delete_account(data, name):
    """Delete an account and everything saved in it. Returns True if it existed."""
    existed = data["accounts"].pop(name.lower(), None) is not None
    if data.get("last_user", "").lower() == name.lower():
        data["last_user"] = ""
    write_save(data)
    return existed


def daily_seed(data, today=None):
    """Seed for today's Shop: normally the date, unless an admin rerolled it today."""
    today = today or datetime.date.today()
    override = data.get("daily_override") or {}
    if override.get("date") == today.isoformat():
        return int(override["seed"])
    return today.toordinal()


def reroll_daily(data, today=None):
    """Admin: pick fresh Shop items for everyone on this PC. The override is stamped with today's
    date, so at midnight the Shop goes back to the normal date-based items."""
    today = today or datetime.date.today()
    data["daily_override"] = {"date": today.isoformat(), "seed": secrets.randbelow(10 ** 9)}
    write_save(data)
    return data["daily_override"]["seed"]


def daily_items(skin_pool, today=None, seed=None, count=4):
    """Today's Shop skins: `count` different ones, the same for everyone all day."""
    if seed is None:
        seed = (today or datetime.date.today()).toordinal()
    rng = random.Random(seed)
    return rng.sample(skin_pool, min(count, len(skin_pool)))


def seconds_until_midnight(now=None):
    now = now or datetime.datetime.now()
    tomorrow = datetime.datetime.combine(now.date() + datetime.timedelta(days=1), datetime.time())
    return int((tomorrow - now).total_seconds())
