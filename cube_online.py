"""Online accounts for Cube Shooter, stored in Supabase, so the same account works on every computer.

* Login uses Supabase Auth. Players only pick a username, so each one gets a stand-in email
  (<username>@players.cubeshooter.game) that nobody ever sees. Supabase stores the password hashed.
* Progress lives in the "players" table (see supabase_setup.sql). Row Level Security means a player's
  login can only read and change their own row.
* The key below is the *publishable* key: it is meant to ship inside apps and gives no access by itself.

Only the standard library is used, so the built .exe needs nothing extra.
"""
import json
import threading
import time
import urllib.error
import urllib.request

SUPABASE_URL = "https://ahjhfwucsivhzhqcjyau.supabase.co"
PUBLISHABLE_KEY = "sb_publishable_MUfA7Qcl32e-XmzP9mYYGg_7AKqOzBf"
EMAIL_DOMAIN = "players.cubeshooter.game"
TIMEOUT = 8.0


class OfflineError(Exception):
    """The server couldn't be reached (no internet, or Supabase is down)."""


class ServerError(Exception):
    def __init__(self, status, message):
        super().__init__(message)
        self.status = status


def email_for(username):
    return "%s@%s" % (username.strip().lower(), EMAIL_DOMAIN)


def online_password(password):
    # Supabase needs at least 6 characters and the game allows 4, so every password gets the same prefix.
    return "cube-shooter:" + password


def _request(method, path, body=None, token=None, extra_headers=None):
    headers = {"apikey": PUBLISHABLE_KEY, "Content-Type": "application/json"}
    if token:
        headers["Authorization"] = "Bearer " + token
    headers.update(extra_headers or {})
    data = json.dumps(body).encode("utf-8") if body is not None else None
    req = urllib.request.Request(SUPABASE_URL + path, data=data, headers=headers, method=method)
    try:
        with urllib.request.urlopen(req, timeout=TIMEOUT) as resp:
            raw = resp.read()
            return json.loads(raw) if raw else None
    except urllib.error.HTTPError as err:
        try:
            info = json.loads(err.read() or b"{}")
        except ValueError:
            info = {}
        message = info.get("msg") or info.get("message") or info.get("error_description") or info.get("error") or str(err)
        raise ServerError(err.code, str(message))
    except (urllib.error.URLError, OSError, TimeoutError) as err:
        raise OfflineError(str(err))


class Session(object):
    """A logged-in player: their tokens, id and name. Refreshes its token when it runs out."""

    def __init__(self, auth):
        self.user_id = auth["user"]["id"]
        self.access_token = auth["access_token"]
        self.refresh_token = auth["refresh_token"]
        self.expires_at = time.time() + int(auth.get("expires_in", 3600)) - 60
        self.name = ""
        self.is_admin = False  # Set in Supabase (players.is_admin) - players can't change it themselves
        self.lock = threading.Lock()
        self.on_new_refresh_token = None  # Called with the new token each time it changes (for "Remember me")

    def token(self):
        with self.lock:
            if time.time() >= self.expires_at:
                auth = _request("POST", "/auth/v1/token?grant_type=refresh_token", {"refresh_token": self.refresh_token})
                self.access_token, self.refresh_token = auth["access_token"], auth["refresh_token"]
                self.expires_at = time.time() + int(auth.get("expires_in", 3600)) - 60
                if self.on_new_refresh_token:
                    self.on_new_refresh_token(self.refresh_token)
            return self.access_token


def username_taken(username):
    return bool(_request("POST", "/rest/v1/rpc/username_taken", {"name": username.strip()}))


def _load_row(session):
    try:
        rows = _request("GET", "/rest/v1/players?id=eq.%s&select=username,progress,is_admin" % session.user_id, token=session.token())
    except ServerError:  # The is_admin column hasn't been added yet (supabase_setup.sql): nobody is an admin
        rows = _request("GET", "/rest/v1/players?id=eq.%s&select=username,progress" % session.user_id, token=session.token())
    return rows[0] if rows else None


def sign_up(username, password, progress=None):
    """Create an online account. Returns (Session, progress). Raises ServerError("That username is taken") etc."""
    username = username.strip()
    if username_taken(username):
        raise ServerError(409, "That username is taken")
    try:
        auth = _request("POST", "/auth/v1/signup", {"email": email_for(username), "password": online_password(password)})
    except ServerError as err:
        if "already" in str(err).lower():
            raise ServerError(409, "That username is taken")
        raise
    if not auth or not auth.get("access_token"):
        raise ServerError(500, "The server didn't log the new account in")
    session = Session(auth)
    session.name = username
    progress = progress or {}
    _request("POST", "/rest/v1/players", {"id": session.user_id, "username": username, "progress": progress},
             token=session.token(), extra_headers={"Prefer": "return=minimal"})
    return session, progress


def log_in(username, password):
    """Returns (Session, progress). Raises ServerError(400, ...) for a wrong username or password."""
    auth = _request("POST", "/auth/v1/token?grant_type=password",
                    {"email": email_for(username), "password": online_password(password)})
    return _open(Session(auth), username.strip())


def resume(refresh_token):
    """Log back in with a remembered refresh token. Returns (Session, progress)."""
    auth = _request("POST", "/auth/v1/token?grant_type=refresh_token", {"refresh_token": refresh_token})
    return _open(Session(auth), "")


def _open(session, typed_name):
    row = _load_row(session)
    if row is None:  # Signed up but the row never got written (e.g. the connection dropped): make it now
        name = typed_name or auth_name(session)
        _request("POST", "/rest/v1/players", {"id": session.user_id, "username": name, "progress": {}},
                 token=session.token(), extra_headers={"Prefer": "return=minimal"})
        row = {"username": name, "progress": {}}
    session.name = row["username"]
    session.is_admin = bool(row.get("is_admin"))
    return session, row.get("progress") or {}


def auth_name(session):
    user = _request("GET", "/auth/v1/user", token=session.token())
    return str(user.get("email", "player@")).split("@")[0]


def save_progress(session, progress):
    _request("PATCH", "/rest/v1/players?id=eq.%s" % session.user_id,
             {"progress": progress, "updated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())},
             token=session.token(), extra_headers={"Prefer": "return=minimal"})


def delete_account(session):
    """Delete the login and its progress (uses the delete_my_account function from supabase_setup.sql)."""
    _request("POST", "/rest/v1/rpc/delete_my_account", {}, token=session.token())


def log_out(session):
    try:
        _request("POST", "/auth/v1/logout", {}, token=session.token())
    except (OfflineError, ServerError):
        pass


class Saver(object):
    """Uploads progress in the background so the game never freezes waiting on the internet.
    Only the newest progress matters: a waiting save is replaced by a newer one, and an older save can
    never land on top of a newer one."""

    def __init__(self):
        self.pending = None
        self.failed = False        # Last upload didn't make it (retried every few seconds)
        self.cond = threading.Condition()
        self.upload_lock = threading.Lock()
        self.seq = 0
        self.uploaded_seq = 0
        threading.Thread(target=self._run, name="cube-cloud-save", daemon=True).start()

    def queue(self, session, progress):
        with self.cond:
            self.seq += 1
            self.pending = (self.seq, session, progress)
            self.cond.notify()

    def _upload(self, seq, session, progress):
        with self.upload_lock:
            if seq <= self.uploaded_seq:
                return True  # Something newer already went up
            try:
                save_progress(session, progress)
            except (OfflineError, ServerError):
                self.failed = True
                return False
            self.uploaded_seq = seq
            self.failed = False
            return True

    def _run(self):
        while True:
            with self.cond:
                while self.pending is None:
                    self.cond.wait()
                seq, session, progress = self.pending
                self.pending = None
            if not self._upload(seq, session, progress):
                with self.cond:
                    if self.pending is None:
                        self.pending = (seq, session, progress)
                time.sleep(5)

    def flush(self, session, progress):
        """Save right now (logging out, closing the game). True if it reached the server."""
        with self.cond:
            self.seq += 1
            seq = self.seq
            self.pending = None
        return self._upload(seq, session, progress)