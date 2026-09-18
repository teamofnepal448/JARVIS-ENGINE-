# -*- coding: utf-8 -*-
"""
JARVIS - Autonomous Telegram Operations Core (fresh build, zero legacy).

Source files of the whole project:
    main.py          (this file - backend: brain, engines, telegram, web api)
    index.html       (web control center)
    requirements.txt

Runtime JSON state lives in ./data/ (created automatically).

Pipeline:
    USER MESSAGE
      -> Input Layer (Telegram Saved Messages / Web goal endpoint)
      -> Goal / Intent Engine        (MiniBrain)
      -> Context Engine              (short-term, expiring)
      -> Planner + Validation        (allowlisted plans only)
      -> Confirmation Engine         (single-use, expiring, bound)
      -> Task Engine / Scheduler / Monitors / Cross
      -> Telegram Tool Execution     (structured ToolResult)
      -> Verification
      -> Memory / State update
      -> Clean user response
"""
from __future__ import annotations

import asyncio
import json
import logging
import os
import re
import shutil
import sys
import time
import uuid
from collections import deque
from contextlib import asynccontextmanager
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Awaitable, Callable, Optional

# ----------------------------------------------------------------------------
# 0. ENV / CONSTANTS
# ----------------------------------------------------------------------------

ROOT = Path(__file__).resolve().parent
DATA_DIR = ROOT / "data"
DATA_DIR.mkdir(parents=True, exist_ok=True)

HOST = os.environ.get("JARVIS_HOST") or "0.0.0.0"
PORT = int(os.environ.get("PORT") or os.environ.get("JARVIS_PORT") or "8090")
ENV_API_ID = (os.environ.get("JARVIS_API_ID") or "").strip()
ENV_API_HASH = (os.environ.get("JARVIS_API_HASH") or "").strip()
OPENAI_BASE_URL = (os.environ.get("OPENAI_BASE_URL") or "https://api.openai.com/v1").rstrip("/")
OPENAI_API_KEY = (os.environ.get("OPENAI_API_KEY") or "").strip()
OPENAI_MODEL = os.environ.get("OPENAI_MODEL") or "gpt-4o-mini"

SCHEMA_VERSION = 1
CONTEXT_TTL = 30 * 60                # short-term context lives 30 minutes
CONFIRM_TTL = 75                     # confirmation lifetime (seconds)
MAX_ACCOUNTS = 6
MAX_ACTIVE_TASKS = 25
MAX_MONITORS = 25
MAX_SCHEDULES = 50
MAX_TARGETS = 50
MAX_ERRORS_PER_TASK = 6
CROSS_TICK_SECONDS = 45              # backfill safety net, events are primary
DIAG_BUFFER = 300

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)-5s | %(name)s | %(message)s",
)
log = logging.getLogger("jarvis")

# ----------------------------------------------------------------------------
# Optional dependencies (validated at startup)
# ----------------------------------------------------------------------------

TELETHON_OK = True
TELETHON_ERR = ""
try:
    from telethon import TelegramClient, events, utils
    from telethon.sessions import StringSession
    from telethon.errors import (
        FloodWaitError, SessionPasswordNeededError, ChatAdminRequiredError,
        PhoneCodeInvalidError, PhoneNumberInvalidError, RPCError,
        ChannelPrivateError, UserNotParticipantError,
    )
    try:
        from telethon.errors import ChatForwardsRestrictedError
    except Exception:  # older telethon
        class ChatForwardsRestrictedError(RPCError):  # type: ignore
            pass
    from telethon.tl import types as tl
except Exception as exc:  # pragma: no cover
    TELETHON_OK = False
    TELETHON_ERR = str(exc)
    TelegramClient = None  # type: ignore

try:
    from fastapi import FastAPI, Request
    from fastapi.responses import FileResponse, JSONResponse
    import uvicorn
    import httpx
    WEB_OK = True
except Exception as exc:  # pragma: no cover
    WEB_OK = False
    log.error("fastapi/uvicorn/httpx missing: %s", exc)


# ----------------------------------------------------------------------------
# 1. SMALL UTILITIES
# ----------------------------------------------------------------------------

def utc_now() -> float:
    return time.time()


def iso(ts: Optional[float] = None) -> str:
    return datetime.fromtimestamp(ts or utc_now(), tz=timezone.utc).isoformat(timespec="seconds")


def new_id(prefix: str) -> str:
    return f"{prefix}_{uuid.uuid4().hex[:10]}"


def human_delta(seconds: float) -> str:
    seconds = int(seconds)
    if seconds < 60:
        return f"{seconds}s"
    if seconds < 3600:
        return f"{seconds // 60}m"
    if seconds < 86400:
        return f"{seconds // 3600}h {seconds % 3600 // 60}m"
    return f"{seconds // 86400}d {seconds % 86400 // 3600}h"


def mask_phone(phone: str) -> str:
    d = re.sub(r"\D", "", phone or "")
    if len(d) < 5:
        return "***"
    return f"+{d[:2]}...{d[-3:]}"


AFFIRM = {"yes", "y", "haan", "ha", "han", "ok", "okay", "theek", "theek hai",
          "confirm", "kar do", "karo", "haan karo", "proceed", "go", "go ahead", "sure"}
DENY = {"no", "n", "nahi", "nhi", "nope", "cancel", "mat karo", "rehne do", "ruk", "ruko", "stop that"}

DURATION_PATTERNS = [
    (r"(\d+)\s*(?:seconds?|secs?|sec)\b", 1),
    (r"(\d+)\s*(?:minutes?|mins?|min|minute)\b", 60),
    (r"(\d+)\s*(?:hours?|hrs?|hr|ghante?|ghanta)\b", 3600),
    (r"(\d+)\s*(?:days?|din|day)\b", 86400),
]


def parse_duration(text: str) -> Optional[int]:
    t = text.lower()
    if "kal tak" in t or "pura din" in t:
        return 86400
    for pat, mult in DURATION_PATTERNS:
        m = re.search(pat, t)
        if m:
            return min(int(m.group(1)) * mult, 7 * 86400)
    return None


def extract_ids(text: str) -> list[str]:
    """Numeric entity ids: long numbers (>=7 digits), optional -100 prefix."""
    out = re.findall(r"-?\d{7,}", text)
    return [x.lstrip("+") for x in out]


def extract_usernames(text: str) -> list[str]:
    return re.findall(r"@[\w_]{5,}", text)


def strip_command(text: str) -> str:
    return re.sub(r"^/(?:ai|jarvis|cross)\b[:\s]*", "", text.strip(), flags=re.I)


def looks_like_command(text: str) -> bool:
    return bool(re.match(r"^/(ai|jarvis|cross)\b", text.strip(), flags=re.I))


def short(text: str, n: int = 120) -> str:
    text = " ".join((text or "").split())
    return text if len(text) <= n else text[: n - 1] + "…"


# ----------------------------------------------------------------------------
# 2. PERSISTENCE - versioned JSON store with safe recovery
# ----------------------------------------------------------------------------

class JSONStore:
    """Single-file JSON persistence with schema versioning + corruption quarantine."""

    def __init__(self, path: Path, default_factory: Callable[[], dict]):
        self.path = path
        self.default_factory = default_factory
        self.data: dict = {}
        self.load()

    def load(self) -> None:
        if not self.path.exists():
            self.data = self.default_factory()
            self.save()
            return
        try:
            raw = json.loads(self.path.read_text(encoding="utf-8"))
            if not isinstance(raw, dict):
                raise ValueError("top-level is not an object")
            self.data = self._migrate(raw)
        except Exception as exc:
            bad = self.path.with_suffix(f".corrupt-{int(utc_now())}.json")
            try:
                shutil.copy2(self.path, bad)
            except Exception:
                pass
            log.warning("store %s malformed (%s) -> quarantined to %s", self.path.name, exc, bad.name)
            self.data = self.default_factory()
            self.save()

    def _migrate(self, raw: dict) -> dict:
        ver = raw.get("schema_version")
        base = self.default_factory()
        if not isinstance(ver, int):
            raw["schema_version"] = SCHEMA_VERSION
        for k, v in base.items():
            raw.setdefault(k, v)
        raw["schema_version"] = SCHEMA_VERSION
        return raw

    def save(self) -> None:
        self.data["updated_at"] = iso()
        tmp = self.path.with_suffix(".tmp")
        tmp.write_text(json.dumps(self.data, ensure_ascii=False, indent=1), encoding="utf-8")
        os.replace(tmp, self.path)

    def touch(self) -> None:
        self.save()


def store_defaults(section_key: str) -> Callable[[], dict]:
    def make() -> dict:
        return {"schema_version": SCHEMA_VERSION, "created_at": iso(), "updated_at": iso(), section_key: {}}
    return make


# ----------------------------------------------------------------------------
# 3. DIAGNOSTICS / OBSERVABILITY (never contains secrets)
# ----------------------------------------------------------------------------

class Diagnostics:
    def __init__(self, store: JSONStore):
        self.store = store
        self.started_at = utc_now()
        self.events: deque[dict] = deque(maxlen=DIAG_BUFFER)
        saved = store.data.get("diag", {}).get("events") or []
        for e in saved[-100:]:
            self.events.append(e)
        self.last_success: Optional[dict] = None
        self.last_failure: Optional[dict] = None

    def record(self, level: str, component: str, operation: str, message: str,
               account_id: Optional[str] = None, task_id: Optional[str] = None) -> None:
        e = {
            "ts": iso(), "level": level, "component": component, "operation": operation,
            "message": short(str(message), 300), "account_id": account_id, "task_id": task_id,
        }
        self.events.append(e)
        if level == "SUCCESS":
            self.last_success = e
        elif level in ("ERROR", "WARN"):
            self.last_failure = e
        fn = log.warning if level in ("WARN", "ERROR") else log.info
        fn("[%s.%s] %s (acc=%s task=%s)", component, operation, e["message"], account_id or "-", task_id or "-")

    def ok(self, component: str, operation: str, message: str, **kw) -> None:
        self.record("SUCCESS", component, operation, message, **kw)

    def info(self, component: str, operation: str, message: str, **kw) -> None:
        self.record("INFO", component, operation, message, **kw)

    def warn(self, component: str, operation: str, message: str, **kw) -> None:
        self.record("WARN", component, operation, message, **kw)

    def err(self, component: str, operation: str, message: str, **kw) -> None:
        self.record("ERROR", component, operation, message, **kw)

    def persist(self) -> None:
        self.store.data["diag"] = {"events": list(self.events)[-100:]}
        self.store.save()

    def snapshot(self) -> dict:
        return {
            "uptime_sec": int(utc_now() - self.started_at),
            "started_at": iso(self.started_at),
            "events": list(self.events)[-60:],
            "last_success": self.last_success,
            "last_failure": self.last_failure,
        }


# ----------------------------------------------------------------------------
# 4. TOOL RESULT STANDARD + CLASSIFIED ERRORS
# ----------------------------------------------------------------------------

@dataclass
class ToolResult:
    ok: bool
    status: str                 # SUCCESS / FAILED / WAITING / PERMISSION_REQUIRED / MISSING_CONTEXT
    data: Optional[dict] = None
    error: Optional[str] = None
    retryable: bool = False
    verification: Optional[dict] = None

    @staticmethod
    def success(data: Optional[dict] = None, verification: Optional[dict] = None) -> "ToolResult":
        return ToolResult(True, "SUCCESS", data or {}, None, False, verification)

    @staticmethod
    def failure(error: str, retryable: bool = False, status: str = "FAILED") -> "ToolResult":
        return ToolResult(False, status, None, error, retryable, None)

    def to_dict(self) -> dict:
        return {"ok": self.ok, "status": self.status, "data": self.data,
                "error": self.error, "retryable": self.retryable, "verification": self.verification}


class EntityResolutionError(Exception):
    pass


class PermissionMissing(Exception):
    pass


class ValidationError(Exception):
    def __init__(self, missing: list[str]):
        super().__init__("; ".join(missing))
        self.missing = missing


class AmbiguityError(Exception):
    def __init__(self, question: str, options: Optional[list[str]] = None):
        super().__init__(question)
        self.question = question
        self.options = options or []


# ----------------------------------------------------------------------------
# 5. MEMORY (long-term, structured) + CONTEXT (short-term, expiring)
# ----------------------------------------------------------------------------

class MemoryStore:
    def __init__(self, store: JSONStore):
        self.store = store

    def _acc(self, account_id: str) -> dict:
        mem = self.store.data["memory"]
        return mem.setdefault(account_id, {"aliases": {}, "notes": [], "known_channels": {}})

    def learn_channel(self, account_id: str, ent_id: str, title: str, username: str = "") -> None:
        acc = self._acc(account_id)
        acc["known_channels"][str(ent_id)] = {"title": title, "username": username, "seen_at": iso()}
        if len(acc["known_channels"]) > 500:
            acc["known_channels"] = dict(list(acc["known_channels"].items())[-500:])
        if title:
            key = title.strip().lower()
            acc["aliases"].setdefault(key, str(ent_id))
        self.store.save()

    def alias_lookup(self, account_id: str, name: str) -> Optional[str]:
        acc = self._acc(account_id)
        key = name.strip().lower()
        if key in acc["aliases"]:
            return acc["aliases"][key]
        for k, v in acc["aliases"].items():
            if key and (key in k or k in key):
                return v
        return None

    def known(self, account_id: str) -> dict:
        return self._acc(account_id)["known_channels"]

    def add_note(self, account_id: str, note: str) -> None:
        acc = self._acc(account_id)
        acc["notes"].append({"ts": iso(), "note": short(note, 200)})
        acc["notes"] = acc["notes"][-200:]
        self.store.save()

    def public(self, account_id: str) -> dict:
        acc = self._acc(account_id)
        return {"aliases": acc["aliases"], "notes": acc["notes"][-20:],
                "known_channels_count": len(acc["known_channels"])}


class ContextEngine:
    """Short-term conversational context; expires safely after CONTEXT_TTL."""

    def __init__(self, store: JSONStore):
        self.store = store

    def _raw(self, account_id: str) -> dict:
        return self.store.data["context"].setdefault(account_id, {})

    def get(self, account_id: str) -> dict:
        raw = self._raw(account_id)
        ts = raw.get("ts", 0)
        if utc_now() - ts > CONTEXT_TTL:
            cleaned: dict = {}
            self.store.data["context"][account_id] = cleaned
            return cleaned
        return raw

    def update(self, account_id: str, **kv) -> None:
        raw = self._raw(account_id)
        for k, v in kv.items():
            if v is not None:
                raw[k] = v
        raw["ts"] = utc_now()
        self.store.save()

    def clear_choice(self, account_id: str) -> None:
        raw = self._raw(account_id)
        raw.pop("pending_choice", None)
        self.store.save()


# ----------------------------------------------------------------------------
# 6. ACCOUNT MANAGER - secure sessions, isolation, single source of channel config
# ----------------------------------------------------------------------------

@dataclass
class AccountRuntime:
    account_id: str
    client: Optional["TelegramClient"] = None
    self_id: Optional[int] = None
    self_name: str = ""
    authorized: bool = False
    connected: bool = False
    handlers_registered: bool = False
    pending_login: Optional[dict] = None     # {phone, phone_code_hash, ts} - in-memory only
    last_error: str = ""


class AccountManager:
    def __init__(self, store: JSONStore, session_store: JSONStore, diag: Diagnostics):
        self.store = store              # accounts.json  (config incl. main_channels - no session strings)
        self.sessions = session_store   # sessions.json  (secure mechanism, chmod 600, never exposed)
        self.diag = diag
        self.runtime: dict[str, AccountRuntime] = {}
        try:
            os.chmod(self.sessions.path, 0o600)
        except Exception:
            pass
        for aid in self.store.data["accounts"]:
            self.runtime[aid] = AccountRuntime(aid)

    # ---- CRUD -----------------------------------------------------------
    def create(self, label: str, api_id: str = "", api_hash: str = "") -> dict:
        if len(self.store.data["accounts"]) >= MAX_ACCOUNTS:
            raise ValidationError([f"account limit reached ({MAX_ACCOUNTS})"])
        aid = new_id("acc")
        cfg = {
            "account_id": aid, "label": label or f"Account {len(self.store.data['accounts']) + 1}",
            "phone": "", "api_id": str(api_id or "").strip(), "api_hash": str(api_hash or "").strip(),
            "main_channels": [],            # single source of truth for Cross targets
            "created_at": iso(), "updated_at": iso(),
        }
        self.store.data["accounts"][aid] = cfg
        self.runtime[aid] = AccountRuntime(aid)
        self.store.save()
        self.diag.ok("accounts", "create", f"{cfg['label']} created", account_id=aid)
        return cfg

    def delete(self, account_id: str) -> None:
        rt = self.runtime.get(account_id)
        if rt and rt.client:
            asyncio.create_task(self._safe_disconnect(rt))
        self.store.data["accounts"].pop(account_id, None)
        self.sessions.data["sessions"].pop(account_id, None)
        self.store.save(); self.sessions.save()
        self.runtime.pop(account_id, None)

    async def _safe_disconnect(self, rt: AccountRuntime) -> None:
        try:
            if rt.client:
                await rt.client.disconnect()
        except Exception:
            pass
        rt.connected = False; rt.authorized = False; rt.client = None

    def get(self, account_id: str) -> dict:
        cfg = self.store.data["accounts"].get(account_id)
        if not cfg:
            raise ValidationError([f"account not found: {account_id}"])
        return cfg

    def all(self) -> list[dict]:
        return list(self.store.data["accounts"].values())

    def resolve_ref(self, ref: Optional[str]) -> Optional[str]:
        accounts = self.all()
        if not accounts:
            return None
        if not ref:
            if len(accounts) == 1:
                return accounts[0]["account_id"]
            return None
        r = ref.strip().lower()
        m = re.search(r"(?:account|acc)\s*#?\s*(\d+)", r)
        if m:
            idx = int(m.group(1)) - 1
            if 0 <= idx < len(accounts):
                return accounts[idx]["account_id"]
        for cfg in accounts:
            if cfg["account_id"] == ref or cfg["label"].lower() == r:
                return cfg["account_id"]
        if r.isdigit():
            idx = int(r) - 1
            if 0 <= idx < len(accounts):
                return accounts[idx]["account_id"]
        return None

    def require_single_or(self, ref: Optional[str]) -> str:
        aid = self.resolve_ref(ref)
        if aid:
            return aid
        accounts = self.all()
        if not accounts:
            raise ValidationError(["no account exists - create one in Web Control or ask me to create it"])
        if not ref and len(accounts) > 1:
            names = ", ".join(f"{i+1}) {a['label']}" for i, a in enumerate(accounts))
            raise AmbiguityError(f"which account should I use?\n{names}", [a["account_id"] for a in accounts])
        raise ValidationError([f"unknown account reference: {ref}"])

    def creds(self, cfg: dict) -> tuple[int, str]:
        api_id = cfg.get("api_id") or ENV_API_ID
        api_hash = cfg.get("api_hash") or ENV_API_HASH
        if not api_id or not api_hash:
            raise ValidationError([
                "api_id/api_hash missing - set JARVIS_API_ID & JARVIS_API_HASH env, "
                "or provide them when creating the account"])
        return int(api_id), api_hash

    # ---- main channel config (single source of truth) -------------------
    def set_main_channels(self, account_id: str, channels: list[dict]) -> None:
        cfg = self.get(account_id)
        cfg["main_channels"] = channels[:MAX_TARGETS]
        cfg["updated_at"] = iso()
        self.store.save()

    def get_main_channels(self, account_id: str) -> list[dict]:
        return list(self.get(account_id).get("main_channels") or [])

    # ---- sessions (secure) ----------------------------------------------
    def save_session(self, account_id: str, session_string: str) -> None:
        self.sessions.data["sessions"][account_id] = session_string
        self.sessions.save()
        try:
            os.chmod(self.sessions.path, 0o600)
        except Exception:
            pass

    def load_session(self, account_id: str) -> str:
        return self.sessions.data["sessions"].get(account_id, "")

    # ---- connection ------------------------------------------------------
    async def connect(self, account_id: str) -> AccountRuntime:
        if not TELETHON_OK:
            raise ValidationError([f"telethon unavailable: {TELETHON_ERR}"])
        cfg = self.get(account_id)
        api_id, api_hash = self.creds(cfg)
        rt = self.runtime.setdefault(account_id, AccountRuntime(account_id))
        if rt.client and rt.connected:
            return rt
        client = TelegramClient(StringSession(self.load_session(account_id)), api_id, api_hash)
        rt.client = client
        try:
            await asyncio.wait_for(client.connect(), timeout=20)
            rt.connected = True
            rt.authorized = await client.is_user_authorized()
            if rt.authorized:
                me = await client.get_me()
                rt.self_id = me.id
                rt.self_name = f"{getattr(me, 'first_name', '') or ''} {getattr(me, 'last_name', '') or ''}".strip()
                cfg["phone"] = getattr(me, "phone", "") or cfg.get("phone", "")
                self.store.save()
                self.diag.ok("accounts", "connect", f"{cfg['label']} online as {rt.self_name or rt.self_id}",
                             account_id=account_id)
            else:
                self.diag.warn("accounts", "connect", f"{cfg['label']} connected but NOT authorized",
                               account_id=account_id)
        except Exception as exc:
            rt.last_error = str(exc)
            rt.connected = False
            self.diag.err("accounts", "connect", f"{cfg['label']}: {type(exc).__name__}", account_id=account_id)
            raise
        return rt

    async def disconnect(self, account_id: str) -> None:
        rt = self.runtime.get(account_id)
        if rt:
            await self._safe_disconnect(rt)
            self.diag.info("accounts", "disconnect", f"{account_id} disconnected", account_id=account_id)

    async def start_login(self, account_id: str, phone: str) -> dict:
        rt = await self.connect(account_id)
        if rt.authorized:
            return {"already": True}
        client = rt.client
        sent = await client.send_code_request(phone)
        rt.pending_login = {"phone": phone, "phone_code_hash": sent.phone_code_hash, "ts": utc_now()}
        self.diag.info("accounts", "login.start", f"code sent to {mask_phone(phone)}", account_id=account_id)
        return {"already": False, "code_sent": True, "phone": mask_phone(phone)}

    async def complete_login(self, account_id: str, code: str, password: str = "") -> dict:
        rt = await self.connect(account_id)
        if rt.authorized:
            return {"ok": True, "name": rt.self_name}
        pend = rt.pending_login
        if not pend:
            raise ValidationError(["no pending login - request a code first"])
        try:
            await rt.client.sign_in(phone=pend["phone"], code=code,
                                    phone_code_hash=pend["phone_code_hash"])
        except SessionPasswordNeededError:
            if not password:
                return {"ok": False, "need_password": True}
            await rt.client.sign_in(password=password)
        except PhoneCodeInvalidError:
            raise ValidationError(["invalid code - try again"])
        me = await rt.client.get_me()
        rt.self_id = me.id
        rt.self_name = f"{getattr(me, 'first_name', '') or ''}".strip()
        rt.authorized = True
        rt.pending_login = None
        cfg = self.get(account_id)
        cfg["phone"] = getattr(me, "phone", "") or cfg.get("phone", "")
        self.save_session(account_id, rt.client.session.save())
        self.store.save()
        self.diag.ok("accounts", "login.complete", f"{cfg['label']} authorized ({rt.self_name or rt.self_id})",
                     account_id=account_id)
        return {"ok": True, "name": rt.self_name}

    async def import_session(self, account_id: str, session_string: str) -> dict:
        if not session_string or len(session_string) < 40:
            raise ValidationError(["session string looks invalid"])
        cfg = self.get(account_id)
        api_id, api_hash = self.creds(cfg)
        client = TelegramClient(StringSession(session_string.strip()), api_id, api_hash)
        await asyncio.wait_for(client.connect(), timeout=20)
        if not await client.is_user_authorized():
            await client.disconnect()
            raise ValidationError(["session string is not authorized"])
        me = await client.get_me()
        rt = self.runtime.setdefault(account_id, AccountRuntime(account_id))
        if rt.client:
            await self._safe_disconnect(rt)
        rt.client = client
        rt.connected = True
        rt.authorized = True
        rt.self_id = me.id
        rt.self_name = f"{getattr(me, 'first_name', '') or ''}".strip()
        cfg["phone"] = getattr(me, "phone", "") or cfg.get("phone", "")
        self.save_session(account_id, session_string.strip())
        self.store.save()
        self.diag.ok("accounts", "session.import",
                     f"{cfg['label']} authorized via session ({rt.self_name or rt.self_id})",
                     account_id=account_id)
        return {"ok": True, "name": rt.self_name}

    # ---- public payloads (never secrets) ---------------------------------
    def public(self, account_id: str) -> dict:
        cfg = self.get(account_id)
        rt = self.runtime.get(account_id) or AccountRuntime(account_id)
        return {
            "account_id": account_id,
            "label": cfg.get("label"),
            "phone_masked": mask_phone(cfg.get("phone", "")) if cfg.get("phone") else "",
            "self_name": rt.self_name,
            "authorized": rt.authorized,
            "connected": rt.connected,
            "api_mode": "env" if not cfg.get("api_id") else "account",
            "pending_login": bool(rt.pending_login),
            "main_channels": cfg.get("main_channels") or [],
            "last_error": rt.last_error,
            "created_at": cfg.get("created_at"),
        }


# ----------------------------------------------------------------------------
# 7. ENTITY RESOLVER - one unified resolution path for everyone
# ----------------------------------------------------------------------------

@dataclass
class ResolvedEntity:
    id: int                    # marked id (-100... for channels)
    kind: str                  # channel / group / user
    title: str
    username: str = ""
    entity: Any = None

    def brief(self) -> str:
        uname = f" @{self.username}" if self.username else ""
        return f"{self.title or 'untitled'}{uname} [{self.id}]"


class EntityResolver:
    def __init__(self, accounts: AccountManager, memory: MemoryStore, diag: Diagnostics):
        self.accounts = accounts
        self.memory = memory
        self.diag = diag
        self._dialog_cache: dict[str, tuple[float, list]] = {}

    async def _client(self, account_id: str) -> "TelegramClient":
        rt = await self.accounts.connect(account_id)
        if not rt.authorized:
            raise ValidationError([f"{self.accounts.get(account_id)['label']} is not authorized - login required"])
        return rt.client

    async def _dialogs(self, account_id: str) -> list:
        ts, cache = self._dialog_cache.get(account_id, (0, []))
        if utc_now() - ts < 120 and cache:
            return cache
        client = await self._client(account_id)
        try:
            dialogs = await asyncio.wait_for(client.get_dialogs(limit=150), timeout=25)
        except Exception:
            dialogs = []
        out = []
        for d in dialogs:
            ent = d.entity
            eid = utils.get_peer_id(ent)
            out.append({"id": eid, "title": getattr(ent, "title", None) or
                        f"{getattr(ent, 'first_name', '') or ''} {getattr(ent, 'last_name', '') or ''}".strip(),
                        "username": getattr(ent, "username", "") or "",
                        "entity": ent})
        self._dialog_cache[account_id] = (utc_now(), out)
        return out

    async def resolve(self, account_id: str, ref: Any) -> ResolvedEntity:
        client = await self._client(account_id)
        raw_candidates: list[Any] = []
        ref_s = str(ref).strip()
        if ref_s.startswith("@") or (re.fullmatch(r"[A-Za-z][\w_]{4,}", ref_s) and not ref_s.isdigit()):
            raw_candidates.append(ref_s.lstrip("@"))
        m100 = re.fullmatch(r"-100(\d+)", ref_s)
        if m100:
            raw_candidates.append(int(m100.group(1)))
            raw_candidates.append(int(ref_s))
        elif ref_s.lstrip("-").isdigit():
            v = int(ref_s)
            raw_candidates.append(v)
            if v > 0 and not ref_s.startswith("-"):
                raw_candidates.append(-v)
                raw_candidates.append(-int(f"100{v}"))
                raw_candidates.append(int(f"100{v}"))
        last_exc: Optional[Exception] = None
        for cand in raw_candidates:
            try:
                ent = await client.get_entity(cand)
                resolved = self._wrap(ent)
                self.diag.info("resolver", "resolve", f"{ref_s} -> {resolved.id}", account_id=account_id)
                return resolved
            except Exception as exc:
                last_exc = exc
                continue
        # alias / known-channel memory
        aliased = self.memory.alias_lookup(account_id, ref_s)
        if aliased:
            return await self.resolve(account_id, aliased)
        # dialogs warm-cache + title search, then numeric retry
        dialogs = await self._dialogs(account_id)
        for d in dialogs:
            if ref_s.lstrip("-").isdigit():
                stripped = ref_s.lstrip("-")
                comp = {str(d["id"]), str(d["id"]).lstrip("-"),
                        str(d["id"]).lstrip("-").replace("100", "", 1)}
                if stripped in comp:
                    return self._wrap(d["entity"])
        lm = ref_s.strip().lower()
        for d in dialogs:
            if lm and (lm in (d["title"] or "").lower()):
                return self._wrap(d["entity"])
        if raw_candidates:
            for cand in raw_candidates:
                try:
                    ent = await client.get_entity(cand)
                    return self._wrap(ent)
                except Exception:
                    pass
        raise EntityResolutionError(
            f"cannot resolve '{short(ref_s, 40)}' - check the ID/username or open the chat once in Telegram")

    def _wrap(self, ent: Any) -> ResolvedEntity:
        eid = utils.get_peer_id(ent)
        if hasattr(ent, "megagroup") or hasattr(ent, "broadcast"):
            kind = "group" if getattr(ent, "megagroup", False) else "channel"
            title = getattr(ent, "title", "?")
        elif hasattr(ent, "title"):
            kind, title = "group", getattr(ent, "title", "?")
        else:
            kind = "user"
            title = f"{getattr(ent, 'first_name', '') or ''} {getattr(ent, 'last_name', '') or ''}".strip() or "?"
        return ResolvedEntity(eid, kind, title, getattr(ent, "username", "") or "", ent)

    async def from_reply(self, account_id: str, reply_msg: Any) -> Optional[ResolvedEntity]:
        """Extract an entity from a replied message (Saved Messages forward header)."""
        if reply_msg is None:
            return None
        fwd = getattr(reply_msg, "fwd_from", None)
        if fwd is not None:
            pid = getattr(fwd, "from_id", None)
            if pid is not None:
                try:
                    ent = await self._client(account_id)
                    entity = await ent.get_entity(pid)
                    return self._wrap(entity)
                except Exception:
                    marked = utils.get_peer_id(pid)
                    return ResolvedEntity(marked, "channel", getattr(fwd, "from_name", "") or "source", "")
        saved_peer = getattr(reply_msg, "peer_id", None)
        try:
            me_id = (self.accounts.runtime.get(account_id) or AccountRuntime(account_id)).self_id
            if saved_peer is not None and getattr(saved_peer, "user_id", None) not in (None, me_id):
                client = await self._client(account_id)
                return self._wrap(await client.get_entity(saved_peer))
        except Exception:
            pass
        return None


# ----------------------------------------------------------------------------
# 8. CONFIRMATION ENGINE - account/task bound, single use, short lived
# ----------------------------------------------------------------------------

class ConfirmationEngine:
    def __init__(self, context: ContextEngine, diag: Diagnostics):
        self.context = context
        self.diag = diag

    def require(self, account_id: str, action_desc: str, payload: dict, task_id: Optional[str] = None) -> str:
        token = new_id("cfm")
        self.context.update(account_id, pending_confirmation={
            "token": token, "desc": action_desc, "payload": payload, "task_id": task_id,
            "expires_at": utc_now() + CONFIRM_TTL})
        self.diag.info("confirm", "require", action_desc, account_id=account_id, task_id=task_id)
        return token

    def pending(self, account_id: str) -> Optional[dict]:
        ctx = self.context.get(account_id)
        p = ctx.get("pending_confirmation")
        if not p:
            return None
        if utc_now() > p.get("expires_at", 0):
            self.context.update(account_id)
            ctx.pop("pending_confirmation", None)
            self.context.store.save()
            self.diag.warn("confirm", "expire", f"confirmation expired for {account_id}", account_id=account_id)
            return None
        return p

    def matches(self, text: str) -> Optional[bool]:
        t = text.strip().lower()
        if t in AFFIRM:
            return True
        if t in DENY:
            return False
        return None

    def consume(self, account_id: str) -> Optional[dict]:
        p = self.pending(account_id)
        ctx = self.context.get(account_id)
        ctx.pop("pending_confirmation", None)
        self.context.store.save()
        return p

    def public(self, account_id: str) -> Optional[dict]:
        p = self.pending(account_id)
        if not p:
            return None
        return {"desc": p["desc"], "expires_in": max(0, int(p["expires_at"] - utc_now())), "task_id": p.get("task_id")}


# ----------------------------------------------------------------------------
# 9. TOOL REGISTRY - structured metadata + implementations
# ----------------------------------------------------------------------------

@dataclass
class ToolSpec:
    name: str
    category: str
    description: str
    required_inputs: list[str]
    optional_inputs: list[str]
    permissions: list[str]
    destructive: bool
    supports_accounts: bool
    supports_background: bool
    verification_method: str
    handler: Callable[..., Awaitable[ToolResult]] = None  # type: ignore


class ToolRegistry:
    def __init__(self) -> None:
        self.tools: dict[str, ToolSpec] = {}

    def register(self, spec: ToolSpec) -> None:
        self.tools[spec.name] = spec

    def get(self, name: str) -> ToolSpec:
        if name not in self.tools:
            raise ValidationError([f"tool not allowlisted: {name}"])
        return self.tools[name]

    def capabilities(self) -> list[dict]:
        return [{
            "name": t.name, "category": t.category, "description": t.description,
            "destructive": t.destructive, "supports_background": t.supports_background,
            "verification": t.verification_method,
        } for t in self.tools.values()]


# ----------------------------------------------------------------------------
# 10. TELEGRAM TOOLS (deterministic, verified, flood-aware)
# ----------------------------------------------------------------------------

class TelegramTools:
    def __init__(self, accounts: AccountManager, resolver: EntityResolver,
                 memory: MemoryStore, diag: Diagnostics):
        self.accounts = accounts
        self.resolver = resolver
        self.memory = memory
        self.diag = diag

    async def _client(self, account_id: str) -> "TelegramClient":
        return await self.resolver._client(account_id)

    async def _admin_rights(self, client: "TelegramClient", ent: ResolvedEntity) -> Optional[dict]:
        try:
            me = await client.get_me()
            from telethon.tl.types import ChannelParticipantsAdmins
            async for p in client.iter_participants(ent.entity, limit=100, filter=ChannelParticipantsAdmins()):
                if p.id == me.id:
                    ar = getattr(p.participant, "admin_rights", None)
                    if ar is None:
                        return {"is_admin": True, "is_creator": getattr(p.participant, "creator", False) or False}
                    return {
                        "is_admin": True,
                        "post": getattr(ar, "post_messages", True),
                        "edit": getattr(ar, "edit_messages", True),
                        "delete": getattr(ar, "delete_messages", True),
                        "ban": getattr(ar, "ban_users", True),
                        "is_creator": getattr(p.participant, "creator", False) or False,
                    }
            return {"is_admin": False}
        except Exception:
            return None

    async def _verify_message(self, client, entity, msg_id: int) -> bool:
        try:
            got = await client.get_messages(entity, ids=msg_id)
            return got is not None and getattr(got, "id", None) == msg_id
        except Exception:
            return False

    # ---- tools -----------------------------------------------------------
    async def inspect_channel(self, account_id: str, ref: Any) -> ToolResult:
        try:
            client = await self._client(account_id)
            ent = await self.resolver.resolve(account_id, ref)
            rights = await self._admin_rights(client, ent)
            msgs = []
            async for m in client.iter_messages(ent.entity, limit=20):
                if getattr(m, "id", None) is None:
                    continue
                sender = ""
                try:
                    if m.fwd_from:
                        sender = "forwarded"
                    elif m.sender_id and hasattr(m, "sender") and m.sender:
                        sender = getattr(m.sender, "title", None) or getattr(m.sender, "first_name", "") or str(m.sender_id)
                except Exception:
                    pass
                msgs.append({"id": m.id, "date": iso(m.date.timestamp()) if m.date else None,
                             "text": short(getattr(m, "raw_text", "") or getattr(m, "message", "") or
                                           (f"[{m.media.__class__.__name__}]" if m.media else ""), 90),
                             "sender": short(sender, 40), "views": getattr(m, "views", None)})
            full = None
            try:
                from telethon.tl.functions.channels import GetFullChannelRequest
                full = await client(GetFullChannelRequest(ent.entity))
                participants = full.full_chat.participants_count
            except Exception:
                participants = None
            self.memory.learn_channel(account_id, str(ent.id), ent.title, ent.username)
            data = {
                "id": ent.id, "title": ent.title, "username": ent.username, "kind": ent.kind,
                "participants": participants,
                "rights": rights, "message_count_sampled": len(msgs), "last_messages": msgs,
            }
            self.diag.ok("tool.inspect", "inspect_channel", f"{ent.title} [{ent.id}] sampled {len(msgs)}",
                         account_id=account_id)
            return ToolResult.success(data, verification={"fetched": True, "sampled": len(msgs)})
        except EntityResolutionError as exc:
            return ToolResult.failure(str(exc), retryable=False, status="MISSING_CONTEXT")
        except FloodWaitError as e:
            return ToolResult.failure(f"FloodWait {e.seconds}s", retryable=True)
        except Exception as exc:
            return ToolResult.failure(f"{type(exc).__name__}", retryable=True)

    async def list_channels(self, account_id: str) -> ToolResult:
        try:
            dialogs = await self.resolver._dialogs(account_id)
            chans = [{"id": d["id"], "title": d["title"], "username": d["username"]}
                     for d in dialogs if d["id"] and (str(d["id"]).startswith("-100") or str(d["id"]).startswith("-"))]
            for d in chans[:80]:
                self.memory.learn_channel(account_id, str(d["id"]), d["title"], d["username"])
            return ToolResult.success({"channels": chans[:80], "count": len(chans)})
        except Exception as exc:
            return ToolResult.failure(type(exc).__name__, retryable=True)

    async def list_admins(self, account_id: str, ref: Any) -> ToolResult:
        try:
            client = await self._client(account_id)
            ent = await self.resolver.resolve(account_id, ref)
            from telethon.tl.types import ChannelParticipantsAdmins
            admins = []
            async for p in client.iter_participants(ent.entity, limit=100, filter=ChannelParticipantsAdmins()):
                admins.append({"id": p.id,
                               "name": f"{getattr(p, 'first_name', '') or ''} {getattr(p, 'last_name', '') or ''}".strip(),
                               "username": getattr(p, "username", "") or "",
                               "creator": getattr(p.participant, "creator", False)})
            return ToolResult.success({"entity": ent.brief(), "admins": admins, "count": len(admins)})
        except ChatAdminRequiredError:
            return ToolResult.failure("admin list hidden - I am not an admin there",
                                      status="PERMISSION_REQUIRED")
        except EntityResolutionError as exc:
            return ToolResult.failure(str(exc), status="MISSING_CONTEXT")
        except Exception as exc:
            return ToolResult.failure(type(exc).__name__, retryable=True)

    async def forward_messages(self, account_id: str, source_ref: Any, target_ref: Any,
                               count: int = 1) -> ToolResult:
        """Cross/forward core: forward (or copy when restricted) recent messages."""
        try:
            client = await self._client(account_id)
            src = await self.resolver.resolve(account_id, source_ref)
            tgt = await self.resolver.resolve(account_id, target_ref)
            ids = []
            async for m in client.iter_messages(src.entity, limit=min(count, 100)):
                if getattr(m, "id", None) is not None:
                    ids.append(m.id)
            ids.reverse()
            sent, verified, failed = 0, 0, 0
            last_error = None
            for chunk_start in range(0, len(ids), 50):
                chunk = ids[chunk_start:chunk_start + 50]
                try:
                    res = await client.forward_messages(tgt.entity, chunk, from_peer=src.entity)
                    res_list = res if isinstance(res, list) else [res]
                    for r in res_list:
                        if r is not None:
                            sent += 1
                            if await self._verify_message(client, tgt.entity, r.id):
                                verified += 1
                except ChatForwardsRestrictedError:
                    for mid in chunk:
                        try:
                            m = await client.get_messages(src.entity, ids=mid)
                            if m:
                                r = await client.send_message(tgt.entity, m.message or "",
                                                              file=m.media)
                                sent += 1
                                if r and await self._verify_message(client, tgt.entity, r.id):
                                    verified += 1
                        except FloodWaitError as fe:
                            await asyncio.sleep(fe.seconds)
                        except Exception as fe:
                            failed += 1; last_error = type(fe).__name__
                except FloodWaitError as fe:
                    self.diag.warn("tool.forward", "floodwait", f"sleep {fe.seconds}s", account_id=account_id)
                    await asyncio.sleep(fe.seconds)
                    res = await client.forward_messages(tgt.entity, chunk, from_peer=src.entity)
                    res_list = res if isinstance(res, list) else [res]
                    for r in res_list:
                        if r is not None:
                            sent += 1
                except RPCError as re_:
                    failed += len(chunk); last_error = type(re_).__name__
            self.diag.ok("tool.forward", "forward_messages",
                         f"{sent}/{len(ids)} forwarded {src.title} -> {tgt.title} (verified {verified})",
                         account_id=account_id)
            return ToolResult.success(
                {"source": src.brief(), "target": tgt.brief(), "requested": len(ids),
                 "sent": sent, "failed": failed, "last_error": last_error},
                verification={"verified": verified})
        except EntityResolutionError as exc:
            return ToolResult.failure(str(exc), status="MISSING_CONTEXT")
        except ChatAdminRequiredError:
            return ToolResult.failure("no permission to post in target", status="PERMISSION_REQUIRED")
        except Exception as exc:
            return ToolResult.failure(type(exc).__name__, retryable=True)

    async def post_message(self, account_id: str, target_ref: Any, text: str) -> ToolResult:
        try:
            client = await self._client(account_id)
            tgt = await self.resolver.resolve(account_id, target_ref)
            m = await client.send_message(tgt.entity, text)
            verified = await self._verify_message(client, tgt.entity, m.id)
            self.diag.ok("tool.post", "post_message", f"posted to {tgt.title} msg {m.id} verified={verified}",
                         account_id=account_id)
            return ToolResult.success({"target": tgt.brief(), "message_id": m.id},
                                      verification={"verified": verified})
        except ChatAdminRequiredError:
            return ToolResult.failure("no permission to post there", status="PERMISSION_REQUIRED")
        except EntityResolutionError as exc:
            return ToolResult.failure(str(exc), status="MISSING_CONTEXT")
        except Exception as exc:
            return ToolResult.failure(type(exc).__name__, retryable=True)

    async def delete_messages(self, account_id: str, ref: Any, count: int,
                              only_ids: Optional[list[int]] = None,
                              progress_cb: Optional[Callable[[int, int], Awaitable[None]]] = None) -> ToolResult:
        try:
            client = await self._client(account_id)
            ent = await self.resolver.resolve(account_id, ref)
            rights = await self._admin_rights(client, ent)
            if rights is not None and rights.get("is_admin") is False and (count or only_ids):
                me = await client.get_me()
                if only_ids is None:
                    own = []
                    async for m in client.iter_messages(ent.entity, limit=count, from_user=me.id):
                        own.append(m.id)
                    if not own:
                        return ToolResult.failure(
                            f"I can access {ent.title} but I don't have permission to delete "
                            f"other people's messages there, and found no own messages to delete.",
                            status="PERMISSION_REQUIRED")
                    only_ids = own
            ids = only_ids or []
            if not only_ids:
                async for m in client.iter_messages(ent.entity, limit=count):
                    if getattr(m, "id", None) is not None:
                        ids.append(m.id)
            deleted, verified_gone, failed = 0, 0, 0
            for i in range(0, len(ids), 50):
                chunk = ids[i:i + 50]
                try:
                    await client.delete_messages(ent.entity, chunk)
                    deleted += len(chunk)
                    gone = await client.get_messages(ent.entity, ids=chunk)
                    gone_list = gone if isinstance(gone, list) else [gone]
                    verified_gone += sum(1 for g in gone_list if g is None)
                except FloodWaitError as fe:
                    await asyncio.sleep(fe.seconds)
                    try:
                        await client.delete_messages(ent.entity, chunk)
                        deleted += len(chunk)
                    except Exception as e2:
                        failed += len(chunk)
                        self.diag.err("tool.delete", "flood.retry", type(e2).__name__, account_id=account_id)
                except ChatAdminRequiredError:
                    return ToolResult.failure(
                        f"I can access {ent.title} but I don't have permission to delete messages there.",
                        status="PERMISSION_REQUIRED")
                except Exception as exc:
                    failed += len(chunk)
                    self.diag.err("tool.delete", "delete_messages", type(exc).__name__, account_id=account_id)
                if progress_cb:
                    await progress_cb(min(i + 50, len(ids)), len(ids))
            self.diag.ok("tool.delete", "delete_messages",
                         f"{deleted}/{len(ids)} deleted in {ent.title} (verified gone {verified_gone})",
                         account_id=account_id)
            return ToolResult.success({"entity": ent.brief(), "requested": len(ids),
                                       "deleted": deleted, "failed": failed},
                                      verification={"verified_gone": verified_gone})
        except EntityResolutionError as exc:
            return ToolResult.failure(str(exc), status="MISSING_CONTEXT")
        except Exception as exc:
            return ToolResult.failure(type(exc).__name__, retryable=True)

    async def send_note(self, account_id: str, text: str) -> ToolResult:
        try:
            client = await self._client(account_id)
            m = await client.send_message("me", text)
            return ToolResult.success({"message_id": m.id}, verification={"verified": True})
        except FloodWaitError as fe:
            await asyncio.sleep(fe.seconds)
            return ToolResult.failure(f"FloodWait {fe.seconds}s", retryable=True)
        except Exception as exc:
            return ToolResult.failure(type(exc).__name__, retryable=True)


# ----------------------------------------------------------------------------
# 11. TASK ENGINE - controlled execution loops, persisted state, resume-safe
# ----------------------------------------------------------------------------

TASK_ACTIVE = "ACTIVE"
TASK_PAUSED = "PAUSED"
TASK_STOPPED = "STOPPED"
TASK_COMPLETED = "COMPLETED"
TASK_FAILED = "FAILED"
TASK_WAITING = "WAITING"
TASK_EXPIRED = "EXPIRED"
RUNNING_STATUSES = {TASK_ACTIVE}


@dataclass
class Task:
    task_id: str
    account_id: str
    kind: str                       # cross / monitor / delete / post_workflow / forward_bulk
    status: str
    params: dict
    progress: dict = field(default_factory=dict)
    created_at: float = field(default_factory=utc_now)
    updated_at: float = field(default_factory=utc_now)
    expires_at: Optional[float] = None
    error_count: int = 0
    last_error: str = ""
    resumable: bool = True
    interval: int = CROSS_TICK_SECONDS

    def public(self) -> dict:
        return {
            "task_id": self.task_id, "short_id": self.task_id[:12], "account_id": self.account_id,
            "kind": self.kind, "status": self.status, "params": self.params, "progress": self.progress,
            "created_at": iso(self.created_at), "updated_at": iso(self.updated_at),
            "expires_at": iso(self.expires_at) if self.expires_at else None,
            "error_count": self.error_count, "last_error": self.last_error, "resumable": self.resumable,
        }


class TaskEngine:
    def __init__(self, store: JSONStore, diag: Diagnostics):
        self.store = store
        self.diag = diag
        self.runners: dict[str, asyncio.Task] = {}
        self.cancels: dict[str, asyncio.Event] = {}
        self.tick_handler: Optional[Callable[[Task], Awaitable[None]]] = None

    # ---- persistence -------------------------------------------------------
    def load_tasks(self) -> dict[str, Task]:
        out = {}
        for tid, raw in (self.store.data.get("tasks") or {}).items():
            try:
                out[tid] = Task(**{k: raw.get(k) for k in Task.__dataclass_fields__})
            except Exception:
                self.diag.warn("tasks", "load", f"malformed task skipped: {tid}")
        return out

    def save_task(self, task: Task) -> None:
        task.updated_at = utc_now()
        self.store.data["tasks"][task.task_id] = {
            "task_id": task.task_id, "account_id": task.account_id, "kind": task.kind,
            "status": task.status, "params": task.params, "progress": task.progress,
            "created_at": task.created_at, "updated_at": task.updated_at,
            "expires_at": task.expires_at, "error_count": task.error_count,
            "last_error": task.last_error, "resumable": task.resumable, "interval": task.interval,
        }
        self.store.save()

    def get(self, task_id: str) -> Optional[Task]:
        raw = (self.store.data.get("tasks") or {}).get(task_id)
        if not raw:
            matches = [t for t in self.load_tasks().values() if t.task_id.startswith(task_id)]
            if len(matches) == 1:
                return matches[0]
            return None
        return Task(**{k: raw.get(k) for k in Task.__dataclass_fields__})

    def list(self, account_id: Optional[str] = None) -> list[Task]:
        return [t for t in self.load_tasks().values() if not account_id or t.account_id == account_id]

    def counts_active(self, account_id: Optional[str] = None) -> int:
        return sum(1 for t in self.list(account_id) if t.status == TASK_ACTIVE)

    # ---- lifecycle -----------------------------------------------------------
    def create(self, account_id: str, kind: str, params: dict,
               expires_in: Optional[int] = None, resumable: bool = True,
               interval: int = CROSS_TICK_SECONDS, dedup_key: Optional[str] = None) -> Task:
        if dedup_key:
            for t in self.list(account_id):
                if t.status == TASK_ACTIVE and t.params.get("dedup") == dedup_key:
                    return t
        if self.counts_active() >= MAX_ACTIVE_TASKS:
            raise ValidationError([f"active task limit reached ({MAX_ACTIVE_TASKS}) - stop something first"])
        task = Task(task_id=new_id("task"), account_id=account_id, kind=kind, status=TASK_ACTIVE,
                    params={**params, **({"dedup": dedup_key} if dedup_key else {})},
                    expires_at=(utc_now() + expires_in) if expires_in else None,
                    resumable=resumable, interval=interval,
                    progress={"steps": {}, "counters": {}})
        self.save_task(task)
        self.diag.ok("tasks", "create", f"{kind} {task.task_id[:12]} created", account_id=account_id,
                     task_id=task.task_id)
        return task

    def start_runner(self, task: Task) -> None:
        if task.task_id in self.runners and not self.runners[task.task_id].done():
            return
        cancel = asyncio.Event()
        self.cancels[task.task_id] = cancel
        self.runners[task.task_id] = asyncio.create_task(self._loop(task.task_id, cancel))

    def set_status(self, task: Task, status: str, note: str = "") -> Task:
        task.status = status
        if note:
            task.last_error = note
        self.save_task(task)
        self.diag.info("tasks", "status", f"{task.kind} {task.task_id[:12]} -> {status} {note}",
                       account_id=task.account_id, task_id=task.task_id)
        if status in (TASK_STOPPED, TASK_COMPLETED, TASK_FAILED, TASK_EXPIRED, TASK_PAUSED):
            ev = self.cancels.get(task.task_id)
            if ev and status != TASK_PAUSED:
                ev.set()
        return task

    async def control(self, task_id: str, action: str) -> ToolResult:
        task = self.get(task_id)
        if task is None:
            return ToolResult.failure(f"task not found: {task_id}")
        if action == "stop":
            self.set_status(task, TASK_STOPPED, "stopped by user")
            return ToolResult.success({"task": task.public()})
        if action == "pause":
            if task.status != TASK_ACTIVE:
                return ToolResult.failure(f"task is {task.status}, not ACTIVE")
            self.set_status(task, TASK_PAUSED, "paused by user")
            return ToolResult.success({"task": task.public()})
        if action == "resume":
            if task.status != TASK_PAUSED:
                return ToolResult.failure(f"task is {task.status}, not PAUSED")
            self.set_status(task, TASK_ACTIVE, "resumed")
            self.start_runner(task)
            return ToolResult.success({"task": task.public()})
        if action == "retry":
            if task.status not in (TASK_FAILED, TASK_EXPIRED, TASK_WAITING, TASK_PAUSED):
                return ToolResult.failure(
                    f"task is {task.status} - retry applies to FAILED/WAITING/PAUSED work")
            task.error_count = 0
            task.last_error = ""
            if task.status == TASK_EXPIRED:
                task.expires_at = utc_now() + 6 * 3600
            task.status = TASK_ACTIVE
            self.save_task(task)
            self.start_runner(task)
            self.diag.ok("tasks", "retry", f"{task.kind} {task.task_id[:12]} retried",
                         account_id=task.account_id, task_id=task.task_id)
            return ToolResult.success({"task": task.public()})
        return ToolResult.failure(f"unknown action: {action}")

    async def _loop(self, task_id: str, cancel: asyncio.Event) -> None:
        errors = 0
        while True:
            task = self.get(task_id)
            if task is None:
                return
            if task.status in (TASK_STOPPED, TASK_COMPLETED, TASK_FAILED, TASK_EXPIRED, TASK_WAITING):
                self.diag.info("tasks", "loop.exit",
                               f"{task.kind} {task.task_id[:12]} reached {task.status}",
                               account_id=task.account_id, task_id=task.task_id)
                return
            if task.status != TASK_ACTIVE:
                backoff = 5
            else:
                if task.expires_at and utc_now() > task.expires_at:
                    self.set_status(task, TASK_EXPIRED, "expiry reached")
                    return
                try:
                    if self.tick_handler:
                        await self.tick_handler(task)
                    errors = 0
                    task.error_count = 0
                    self.save_task(task)
                except asyncio.CancelledError:
                    return
                except FloodWaitError as fe:
                    errors += 1
                    task.error_count = errors
                    task.last_error = f"FloodWait {fe.seconds}s (respected)"
                    self.save_task(task)
                    try:
                        await asyncio.wait_for(cancel.wait(), timeout=fe.seconds)
                        return
                    except asyncio.TimeoutError:
                        continue
                except Exception as exc:
                    errors += 1
                    task.error_count = errors
                    task.last_error = f"{type(exc).__name__}: {short(str(exc), 150)}"
                    self.save_task(task)
                    self.diag.err("tasks", "loop", task.last_error, account_id=task.account_id,
                                  task_id=task.task_id)
                    if errors >= MAX_ERRORS_PER_TASK:
                        self.set_status(task, TASK_FAILED, "error limit reached")
                        return
                backoff = min(5 * (2 ** max(errors, 0)), 300)
            interval = task.interval if task.status == TASK_ACTIVE else 10
            try:
                await asyncio.wait_for(cancel.wait(), timeout=max(3, interval if errors == 0 else backoff))
                return
            except asyncio.TimeoutError:
                continue

    def resume_all(self) -> None:
        for task in self.list():
            if task.status == TASK_ACTIVE and task.resumable:
                self.start_runner(task)

    async def shutdown(self) -> None:
        for ev in self.cancels.values():
            ev.set()
        for r in self.runners.values():
            r.cancel()
        await asyncio.sleep(0.3)


# ----------------------------------------------------------------------------
# 12. SCHEDULER - single-loop, persisted, due-execution
# ----------------------------------------------------------------------------

class Scheduler:
    def __init__(self, store: JSONStore, diag: Diagnostics):
        self.store = store
        self.diag = diag
        self.runner: Optional[asyncio.Task] = None
        self.execute_handler: Optional[Callable[[dict], Awaitable[ToolResult]]] = None

    def add(self, account_id: str, run_at: float, payload: dict) -> dict:
        items = self.store.data["schedules"]
        if len([i for i in items.values() if i.get("status") == "PENDING"]) >= MAX_SCHEDULES:
            raise ValidationError([f"schedule limit reached ({MAX_SCHEDULES})"])
        sid = new_id("sch")
        items[sid] = {"schedule_id": sid, "account_id": account_id, "run_at": run_at,
                      "payload": payload, "status": "PENDING", "created_at": iso(),
                      "error": None}
        self.store.save()
        self.diag.ok("scheduler", "add", f"{sid} at {iso(run_at)}", account_id=account_id)
        return items[sid]

    def cancel(self, sid: str) -> bool:
        item = self.store.data["schedules"].get(sid)
        if item and item.get("status") == "PENDING":
            item["status"] = "CANCELLED"
            self.store.save()
            return True
        return False

    def due(self) -> list[dict]:
        now = utc_now()
        return [i for i in self.store.data["schedules"].values()
                if i.get("status") == "PENDING" and i.get("run_at", 0) <= now]

    async def _loop(self) -> None:
        while True:
            try:
                for item in self.due():
                    item["status"] = "RUNNING"
                    self.store.save()
                    try:
                        if self.execute_handler:
                            res = await self.execute_handler(item)
                            item["status"] = "DONE" if res.ok else "FAILED"
                            item["error"] = None if res.ok else res.error
                        else:
                            item["status"] = "FAILED"
                            item["error"] = "no handler"
                    except Exception as exc:
                        item["status"] = "FAILED"
                        item["error"] = type(exc).__name__
                    self.store.save()
                    self.diag.info("scheduler", "execute",
                                   f"{item['schedule_id']} -> {item['status']}",
                                   account_id=item.get("account_id"))
            except Exception as exc:
                self.diag.err("scheduler", "loop", type(exc).__name__)
            await asyncio.sleep(4)

    def start(self) -> None:
        if self.runner is None or self.runner.done():
            self.runner = asyncio.create_task(self._loop())

    def list_pending(self, account_id: Optional[str] = None) -> list[dict]:
        return sorted(
            [dict(i, run_at_iso=iso(i["run_at"])) for i in self.store.data["schedules"].values()
             if i.get("status") == "PENDING" and (not account_id or i.get("account_id") == account_id)],
            key=lambda x: x["run_at"])


# ----------------------------------------------------------------------------
# 13. MONITOR ENGINE - event-driven watches with dedupe cursors
# ----------------------------------------------------------------------------

class MonitorEngine:
    def __init__(self, store: JSONStore, diag: Diagnostics):
        self.store = store
        self.diag = diag
        self.on_event: Optional[Callable[[dict, Any], Awaitable[None]]] = None

    def add(self, account_id: str, source: dict, condition: str, action: str,
            expires_in: Optional[int], task_id: Optional[str]) -> dict:
        items = self.store.data["monitors"]
        active = [m for m in items.values() if m.get("status") == "ACTIVE"]
        if len(active) >= MAX_MONITORS:
            raise ValidationError([f"monitor limit reached ({MAX_MONITORS})"])
        for m in active:
            if m["account_id"] == account_id and m["source"]["id"] == source["id"] \
                    and m["condition"] == condition:
                return m
        mid = new_id("mon")
        items[mid] = {
            "monitor_id": mid, "account_id": account_id, "source": source,
            "condition": condition, "action": action, "created_at": iso(),
            "expires_at": iso(utc_now() + expires_in) if expires_in else None,
            "expires_ts": (utc_now() + expires_in) if expires_in else None,
            "last_processed_id": 0, "status": "ACTIVE", "error_count": 0,
            "task_id": task_id, "hits": 0, "last_error": "",
        }
        self.store.save()
        self.diag.ok("monitors", "add", f"{mid} watching {source.get('title')} ({condition})",
                     account_id=account_id, task_id=task_id)
        return items[mid]

    def stop(self, monitor_id: str) -> bool:
        m = self.store.data["monitors"].get(monitor_id)
        if m and m.get("status") == "ACTIVE":
            m["status"] = "STOPPED"
            self.store.save()
            self.diag.info("monitors", "stop", monitor_id, account_id=m.get("account_id"))
            return True
        return False

    def stop_all(self, account_id: str) -> int:
        n = 0
        for m in self.store.data["monitors"].values():
            if m.get("account_id") == account_id and m.get("status") == "ACTIVE":
                m["status"] = "STOPPED"
                n += 1
        self.store.save()
        return n

    def active_for(self, account_id: str, chat_id: int) -> list[dict]:
        now = utc_now()
        out = []
        for m in self.store.data["monitors"].values():
            if m.get("status") != "ACTIVE":
                continue
            if m.get("expires_ts") and now > m["expires_ts"]:
                m["status"] = "EXPIRED"
                continue
            if m.get("account_id") == account_id and int(m["source"]["id"]) == int(chat_id):
                out.append(m)
        return out

    def active_all(self, account_id: Optional[str] = None) -> list[dict]:
        return [m for m in self.store.data["monitors"].values()
                if m.get("status") == "ACTIVE" and (not account_id or m.get("account_id") == account_id)]

    def mark_processed(self, monitor_id: str, msg_id: int, hit: bool = False) -> None:
        m = self.store.data["monitors"].get(monitor_id)
        if not m:
            return
        m["last_processed_id"] = max(m.get("last_processed_id", 0), msg_id)
        if hit:
            m["hits"] = m.get("hits", 0) + 1
        self.store.save()


# ----------------------------------------------------------------------------
# 14. MINI BRAIN - deterministic goal/intent understanding (EN + Hinglish)
# ----------------------------------------------------------------------------

@dataclass
class Decision:
    intent: str
    slots: dict = field(default_factory=dict)
    missing: list[str] = field(default_factory=list)
    note: str = ""

    def to_dict(self) -> dict:
        return {"intent": self.intent, "slots": {k: short(str(v), 60) for k, v in self.slots.items()},
                "missing": self.missing, "note": self.note}


CONTEXT_WORDS = re.compile(
    r"\b(is|isse|isko|isme|isliye|ye|yeh|yahi|us|usi|usko|usme|wo|woh|wahi|"
    r"is channel|us channel|is task|us task|this channel|that channel|this task|that task|"
    r"this|that|it)\b", re.I)


class MiniBrain:
    """Deterministic intent parser. AI (optional) only assists when UNMAPPED."""

    def __init__(self, context: ContextEngine):
        self.context = context

    # -- helpers -------------------------------------------------------------
    @staticmethod
    def _has(text: str, words: list[str]) -> bool:
        t = text.lower()
        return any(w in t for w in words)

    def _account_ref(self, text: str) -> Optional[str]:
        m = re.search(r"(?:account|acc)\s*#?\s*(\d+)", text.lower())
        return f"account {m.group(1)}" if m else None

    def _task_ref_from_ctx(self, account_id: str) -> Optional[str]:
        return self.context.get(account_id).get("last_task_id")

    def _channel_ref_from_ctx(self, account_id: str) -> Optional[dict]:
        ctx = self.context.get(account_id)
        ent = ctx.get("last_channel")
        if ent and ent.get("id"):
            return ent
        return None

    # -- main parse ------------------------------------------------------------
    def parse(self, account_id: str, text: str, reply_entity: Optional[ResolvedEntity] = None) -> Decision:
        t = strip_command(text).strip()
        low = t.lower()
        slots: dict = {"account_ref": self._account_ref(t)}

        ids = extract_ids(t)
        usernames = extract_usernames(t)
        entities = ids + usernames
        ctx_channel = self._channel_ref_from_ctx(account_id)
        ctx_task = self._task_ref_from_ctx(account_id)
        refers_ctx = bool(CONTEXT_WORDS.search(t))

        # ----- cross -----
        if re.search(r"\bcross\b", low) or text.strip().lower().startswith("/cross"):
            if self._has(low, ["stop", "band", "off", "ruk"]):
                return Decision("CROSS_STOP", slots)
            if self._has(low, ["start", "shuru", "chalu", "chala", "on", "lagao", "karo"]):
                dur = parse_duration(low)
                if reply_entity:
                    slots["source"] = {"id": reply_entity.id, "title": reply_entity.title,
                                       "via": "reply"}
                elif entities:
                    slots["source"] = entities[0]
                elif ctx_channel:
                    slots["source"] = {"id": ctx_channel["id"], "title": ctx_channel.get("title", ""),
                                       "via": "context"}
                else:
                    return Decision("CROSS_START", slots, missing=["source channel"])
                if dur:
                    slots["duration_sec"] = dur
                return Decision("CROSS_START", slots)

        # ----- confirmations handled elsewhere; choices -----
        choice = self._choice(account_id, low)
        if choice:
            return choice

        # ----- monitor -----
        if self._has(low, ["monitor", "monitoring", "nazar", "dhyan rakh", "dhyan", "watch",
                           "nigrani", "dekh te reh", "dekhte raho", "keep an eye"]):
            if self._has(low, ["band", "stop", "hatana", "hatao", "ruk"]) and self._has(low, ["sab", "sb", "all", "saari"]):
                return Decision("STOP_ALL_MONITORS", slots)
            if self._has(low, ["band", "stop", "ruk", "hata"]):
                return self._task_control(slots, account_id, "stop", prefer_kind="monitor")
            dur = parse_duration(low) or 86400
            slots["duration_sec"] = dur
            slots["condition"] = "unknown" if ("unknown" in low or "anjaan" in low or "anjan" in low) else "all"
            if reply_entity:
                slots["source"] = {"id": reply_entity.id, "title": reply_entity.title, "via": "reply"}
            elif entities:
                slots["source"] = entities[0]
            elif refers_ctx and ctx_channel:
                slots["source"] = {"id": ctx_channel["id"], "title": ctx_channel.get("title", ""), "via": "context"}
            elif ctx_channel:
                slots["source"] = {"id": ctx_channel["id"], "title": ctx_channel.get("title", ""), "via": "context"}
            else:
                return Decision("MONITOR_START", slots, missing=["source channel"])
            return Decision("MONITOR_START", slots)

        # ----- main channel configuration -----
        mentions_main = self._has(low, ["main channel", "main chennal", "mainchannel", "cross target", "target channel"])
        if mentions_main:
            if self._has(low, ["dikhao", "show", "batao", "kya hai", "list", "dikha", "bata"]) and not entities:
                return Decision("LIST_MAIN_CHANNELS", slots)
            if self._has(low, ["hata", "remove", "nikal", "delete"]):
                if entities:
                    slots["targets"] = entities
                    return Decision("REMOVE_MAIN_CHANNELS", slots)
                if refers_ctx and ctx_channel:
                    slots["targets"] = [str(ctx_channel["id"])]
                    return Decision("REMOVE_MAIN_CHANNELS", slots)
                return Decision("REMOVE_MAIN_CHANNELS", slots, missing=["which channel to remove"])
            if self._has(low, ["add", "jod", "daal", "bana", "set", "kar do", "rakh", "hain", "hai", "="]):
                if entities:
                    if self._has(low, [" hain", " hai", "set", "rakh", "="]):
                        slots["targets"] = entities
                        return Decision("SET_MAIN_CHANNELS", slots)
                    slots["targets"] = entities
                    return Decision("ADD_MAIN_CHANNELS", slots)
                if reply_entity:
                    slots["targets"] = [str(reply_entity.id)]
                    slots["targets_title"] = reply_entity.title
                    return Decision("ADD_MAIN_CHANNELS", slots)
                if refers_ctx and ctx_channel:
                    slots["targets"] = [str(ctx_channel["id"])]
                    return Decision("ADD_MAIN_CHANNELS", slots)
                return Decision("ADD_MAIN_CHANNELS", slots, missing=["channel ids to configure"])

        # ----- inspect -----
        if self._has(low, ["inspect", "jaanch", "check karo", "analyze", "analyse", "dekho kya", "scan"]):
            if reply_entity:
                slots["target"] = {"id": reply_entity.id, "title": reply_entity.title, "via": "reply"}
            elif entities:
                slots["target"] = entities[0]
            elif refers_ctx and ctx_channel:
                slots["target"] = {"id": ctx_channel["id"], "title": ctx_channel.get("title", ""), "via": "context"}
            else:
                return Decision("INSPECT_CHANNEL", slots, missing=["channel to inspect"])
            return Decision("INSPECT_CHANNEL", slots)

        # ----- task control -----
        if re.search(r"\b(retry|dobara|phir se try)\b", low):
            return self._task_control(slots, account_id, "retry")
        if self._has(low, ["pause", "rok do thoda", "hold"]):
            return self._task_control(slots, account_id, "pause")
        if self._has(low, ["resume", "continue", "waps chalu", "fir se chalu"]):
            return self._task_control(slots, account_id, "resume")
        if self._has(low, ["stop", "band", "ruk", "khatam", "cancel kar"]):
            return self._task_control(slots, account_id, "stop")

        # ----- listing / status -----
        if self._has(low, ["running", "chal raha", "kaam dikhao", "work dikhao", "tasks dikhao",
                           "task list", "kya ho raha", "progress dikhao", "mera running", "list tasks"]):
            return Decision("LIST_TASKS", slots)
        if self._has(low, ["status", "health", "haalat", "sab theek", "diagnostics", "diag"]):
            return Decision("STATUS", slots)
        if self._has(low, ["help", "madad", "kya kar sakte", "commands", "kaise use"]):
            return Decision("HELP", slots)

        # ----- delete (destructive) -----
        if self._has(low, ["delete", "hata do", "saaf karo", "mita"]):
            count = None
            m = re.search(r"(\d{1,4})\s*(?:messages?|msg|sms)", low)
            if m:
                count = int(m.group(1))
            elif re.search(r"\blast\s+(\d{1,4})\b", low):
                count = int(re.search(r"\blast\s+(\d{1,4})\b", low).group(1))  # type: ignore
            elif self._has(low, ["ye message", "is message", "this message"]) or reply_entity:
                count = 1
            if reply_entity and not entities:
                slots["target"] = {"id": reply_entity.id, "title": reply_entity.title, "via": "reply"}
            elif entities:
                slots["target"] = entities[0]
            elif refers_ctx and ctx_channel:
                slots["target"] = {"id": ctx_channel["id"], "title": ctx_channel.get("title", ""), "via": "context"}
            else:
                return Decision("DELETE_MESSAGES", slots, missing=["which channel to clean"])
            if count is None:
                count = 5
            slots["count"] = max(1, min(count, 500))
            return Decision("DELETE_MESSAGES", slots)

        # ----- forward / post to main channels -----
        if self._has(low, ["forward", "bhej", "post kar", "daal do main", "main channel pe", "main channels pe",
                           "main channels me"]):
            count = 1
            m = re.search(r"(\d{1,3})\s*(?:messages?|msg)", low)
            if m:
                count = int(m.group(1))
            slots["count"] = count
            if reply_entity:
                slots["source"] = {"id": reply_entity.id, "title": reply_entity.title, "via": "reply"}
            elif entities:
                slots["source"] = entities[0]
            elif refers_ctx and ctx_channel:
                slots["source"] = {"id": ctx_channel["id"], "title": ctx_channel.get("title", ""), "via": "context"}
            else:
                return Decision("FORWARD_TO_MAIN", slots, missing=["source of the message"])
            return Decision("FORWARD_TO_MAIN", slots)

        # ----- schedule -----
        if self._has(low, ["schedule", "baad me bhej", "later"]):
            dur = parse_duration(low)
            if dur:
                slots["run_in_sec"] = dur
            return Decision("UNMAPPED", slots,
                            note="scheduling needs explicit content + target; try: post '<text>' to main channels in 2 hours")

        # ----- alias / remember -----
        m = re.search(r"(?:yaad rakh|remember|alias)\s*[:\-]?\s*(.+?)\s*=\s*(.+)$", low)
        if m:
            slots["alias"] = m.group(1).strip()
            slots["value"] = m.group(2).strip()
            return Decision("SET_ALIAS", slots)

        return Decision("UNMAPPED", slots)

    # -- helpers -------------------------------------------------------------
    def _choice(self, account_id: str, low: str) -> Optional[Decision]:
        ctx = self.context.get(account_id)
        pc = ctx.get("pending_choice")
        if not pc:
            return None
        mapping = pc.get("mapping") or {}
        keys = {"1": 0, "first": 0, "pehla": 0, "2": 1, "second": 1, "dusra": 1,
                "3": 2, "third": 2, "teesra": 2}
        idx = None
        for k, v in keys.items():
            if re.fullmatch(k, low.strip()):
                idx = v
                break
        if idx is None:
            for k in mapping:
                if k in low:
                    idx = mapping.index(k) if k in mapping else None
                    break
        if idx is None or idx >= len(pc.get("options", [])):
            return None
        opt = pc["options"][idx]
        self.context.clear_choice(account_id)
        return Decision(opt["intent"], {**opt.get("slots", {}), "account_ref": None})

    def _task_control(self, slots: dict, account_id: str, action: str,
                      prefer_kind: Optional[str] = None) -> Decision:
        ctx = self.context.get(account_id)
        slots["task_action"] = action
        m = re.search(r"task[_\s]?([a-z0-9]{8,})", slots.get("_raw", "") or "", re.I)
        if m:
            slots["task_id"] = m.group(1)
        elif ctx.get("last_task_id"):
            slots["task_id"] = ctx["last_task_id"]
        if prefer_kind:
            slots["prefer_kind"] = prefer_kind
        return Decision("TASK_CONTROL", slots)


# ----------------------------------------------------------------------------
# 15. CROSS ENGINE - reply-aware live cross (targets ONLY from account config)
# ----------------------------------------------------------------------------

class CrossEngine:
    """Forwards new posts from a source to the account's configured Main Channels.

    read path: AccountManager.get_main_channels (single source of truth).
    Dedupe via task.progress['last_processed_id'] + bounded processed deque.
    First tick anchors the cursor at the newest message (no history dump by default).
    """

    def __init__(self, tasks: TaskEngine, tools: TelegramTools,
                 accounts: AccountManager, resolver: EntityResolver, diag: Diagnostics):
        self.tasks = tasks
        self.tools = tools
        self.accounts = accounts
        self.resolver = resolver
        self.diag = diag

    def active_for(self, account_id: str, chat_id: int) -> list[Task]:
        out = []
        for t in self.tasks.list(account_id):
            if t.kind == "cross" and t.status == TASK_ACTIVE:
                if int(t.params.get("source", {}).get("id", 0) or 0) == int(chat_id):
                    out.append(t)
        return out

    async def deliver(self, task: Task, msg: Any) -> None:
        last = int(task.progress.get("last_processed_id", 0) or 0)
        if msg.id <= last:
            return
        processed = deque(task.progress.get("processed_ids") or [], maxlen=500)
        if msg.id in processed:
            task.progress["last_processed_id"] = max(last, msg.id)
            self.tasks.save_task(task)
            return
        account_id = task.account_id
        client = await self.resolver._client(account_id)
        src_ent = await self.resolver.resolve(account_id, str(task.params["source"]["id"]))
        counters = task.progress.setdefault("counters", {})
        steps = task.progress.setdefault("steps", {})
        steps.setdefault("source_resolved", "done")
        steps.setdefault("targets_loaded", "done")
        steps["delivery"] = "active"
        for tgt in (task.params.get("targets") or []):
            key = str(tgt["id"])
            stat = counters.setdefault(key, {"title": tgt.get("title", ""), "sent": 0,
                                             "verified": 0, "failed": 0, "last_error": ""})
            try:
                tgt_ent = await self.resolver.resolve(account_id, str(tgt["id"]))
                res = None
                try:
                    res = await client.forward_messages(tgt_ent.entity, msg.id,
                                                        from_peer=src_ent.entity)
                except ChatForwardsRestrictedError:
                    if (msg.message or "") or msg.media:
                        res = await client.send_message(tgt_ent.entity, msg.message or "",
                                                        file=msg.media)
                if isinstance(res, list):
                    res = res[0] if res else None
                if res is not None:
                    stat["sent"] += 1
                    got = await client.get_messages(tgt_ent.entity, ids=res.id)
                    if got is not None:
                        stat["verified"] += 1
                    else:
                        stat["failed"] += 1
                        stat["last_error"] = "verification failed"
            except FloodWaitError:
                self.tasks.save_task(task)
                raise
            except ChatAdminRequiredError:
                stat["failed"] += 1
                stat["last_error"] = "no post permission"
            except Exception as exc:
                stat["failed"] += 1
                stat["last_error"] = type(exc).__name__
        processed.append(msg.id)
        task.progress["processed_ids"] = list(processed)
        task.progress["last_processed_id"] = max(last, msg.id)
        self.tasks.save_task(task)
        total = sum(c.get("sent", 0) for c in counters.values() if isinstance(c, dict))
        if total and total % 25 == 0:
            ver = sum(c.get("verified", 0) for c in counters.values() if isinstance(c, dict))
            await self.tools.send_note(
                account_id,
                f"CROSS UPDATE [{task.task_id[:12]}]\n"
                f"Source: {task.params.get('source', {}).get('title', '')}\n"
                f"Delivered: {total} | verified: {ver}")

    async def tick(self, task: Task) -> None:
        account_id = task.account_id
        client = await self.resolver._client(account_id)
        src_ent = await self.resolver.resolve(account_id, str(task.params["source"]["id"]))
        last = int(task.progress.get("last_processed_id", 0) or 0)
        if not last:
            recent = await client.get_messages(src_ent.entity, limit=1)
            if recent:
                task.progress["last_processed_id"] = recent[0].id
                self.tasks.save_task(task)
            return
        batch = await client.get_messages(src_ent.entity, min_id=last, limit=30)
        msgs = [m for m in (batch or []) if getattr(m, "id", None) and m.id > last]
        for m in reversed(msgs):
            await self.deliver(task, m)


# ----------------------------------------------------------------------------
# 16. JARVIS CORE - orchestrates the entire pipeline
# ----------------------------------------------------------------------------

AI_ALLOWED_INTENTS = {
    "CROSS_START", "CROSS_STOP", "MONITOR_START", "STOP_ALL_MONITORS", "INSPECT_CHANNEL",
    "LIST_MAIN_CHANNELS", "ADD_MAIN_CHANNELS", "SET_MAIN_CHANNELS", "REMOVE_MAIN_CHANNELS",
    "TASK_CONTROL", "LIST_TASKS", "STATUS", "HELP", "DELETE_MESSAGES", "FORWARD_TO_MAIN",
    "SET_ALIAS", "UNMAPPED",
}
AI_ALLOWED_SLOTS = {"source", "target", "targets", "count", "duration_sec", "condition",
                    "task_id", "task_action", "account_ref", "alias", "value"}


def respond(reply: str, status: str = "SUCCESS", intent: str = "",
            data: Optional[dict] = None) -> dict:
    return {"ok": status == "SUCCESS", "status": status, "reply": reply,
            "intent": intent, "data": data or {}}


def chunk_text(text: str, size: int = 3800) -> list[str]:
    if len(text) <= size:
        return [text]
    out, cur = [], ""
    for line in text.split("\n"):
        if len(cur) + len(line) + 1 > size:
            out.append(cur)
            cur = line
        else:
            cur = f"{cur}\n{line}" if cur else line
    if cur:
        out.append(cur)
    return out


class JarvisCore:
    def __init__(self) -> None:
        # persistence
        self.accounts_store = JSONStore(DATA_DIR / "accounts.json", store_defaults("accounts"))
        self.sessions_store = JSONStore(DATA_DIR / "sessions.json", store_defaults("sessions"))
        self.tasks_store = JSONStore(DATA_DIR / "tasks.json", store_defaults("tasks"))
        self.monitors_store = JSONStore(DATA_DIR / "monitors.json", store_defaults("monitors"))
        self.schedules_store = JSONStore(DATA_DIR / "schedules.json", store_defaults("schedules"))
        self.memory_store = JSONStore(DATA_DIR / "memory.json", store_defaults("memory"))
        self.context_store = JSONStore(DATA_DIR / "context.json", store_defaults("context"))
        self.diag_store = JSONStore(DATA_DIR / "diag.json", store_defaults("diag"))
        # engines
        self.diag = Diagnostics(self.diag_store)
        self.memory = MemoryStore(self.memory_store)
        self.context = ContextEngine(self.context_store)
        self.accounts = AccountManager(self.accounts_store, self.sessions_store, self.diag)
        self.resolver = EntityResolver(self.accounts, self.memory, self.diag)
        self.tools = TelegramTools(self.accounts, self.resolver, self.memory, self.diag)
        self.confirm = ConfirmationEngine(self.context, self.diag)
        self.registry = ToolRegistry()
        self.brain = MiniBrain(self.context)
        self.tasks = TaskEngine(self.tasks_store, self.diag)
        self.scheduler = Scheduler(self.schedules_store, self.diag)
        self.monitors = MonitorEngine(self.monitors_store, self.diag)
        self.cross = CrossEngine(self.tasks, self.tools, self.accounts, self.resolver, self.diag)
        # wiring
        self.tasks.tick_handler = self._task_tick
        self.scheduler.execute_handler = self._schedule_execute
        self.admin_cache: dict[tuple, tuple[float, set]] = {}
        self._handler_clients: dict[str, Any] = {}
        self._register_tools()

    # -- tool registry metadata ------------------------------------------
    def _register_tools(self) -> None:
        R = self.registry
        R.register(ToolSpec("inspect_channel", "discovery",
                            "Deep read of a channel/group: meta, your rights, recent posts, unknown senders.",
                            ["account_id", "ref"], [], [], False, True, False, "refetch entity + sample"))
        R.register(ToolSpec("list_channels", "discovery",
                            "List channels/groups visible to the account (dialog scan).",
                            ["account_id"], [], [], False, True, False, "dialog snapshot"))
        R.register(ToolSpec("list_admins", "discovery",
                            "List admin members of a channel/group.",
                            ["account_id", "ref"], [], [], False, True, False, "participant scan"))
        R.register(ToolSpec("forward_messages", "delivery",
                            "Forward N recent messages source -> target (copy fallback when forwards restricted).",
                            ["account_id", "source", "target"], ["count"], [], False, True, False,
                            "message id refetch on target"))
        R.register(ToolSpec("post_message", "delivery",
                            "Post a text message into a target.",
                            ["account_id", "target", "text"], [], ["send rights"], False, True, False,
                            "message id refetch on target"))
        R.register(ToolSpec("delete_messages", "moderation",
                            "Bulk delete messages from a channel (confirmation required).",
                            ["account_id", "ref", "count"], ["only_ids"],
                            ["delete_messages admin right"], True, True, False,
                            "post-delete refetch (gone check)"))
        R.register(ToolSpec("cross_start", "cross",
                            "Reply-aware live cross: new source posts -> configured Main Channels.",
                            ["account_id", "source"], ["duration_sec"], [], False, True, True,
                            "per-forward refetch + cursor"))
        R.register(ToolSpec("cross_stop", "cross", "Stop active cross task(s).",
                            ["account_id"], [], [], False, True, False, "task state"))
        R.register(ToolSpec("monitor_start", "monitoring",
                            "Event-driven watch: alert in Saved Messages on new posts / unknown senders.",
                            ["account_id", "source"], ["condition", "duration_sec"], [],
                            False, True, True, "cursor dedupe + alert note"))
        R.register(ToolSpec("monitor_stop", "monitoring", "Stop one or all monitors.",
                            ["account_id"], [], [], False, True, False, "monitor state"))
        R.register(ToolSpec("config_main_channels", "configuration",
                            "Single source of truth for Main Channels (web + telegram both use this).",
                            ["account_id", "refs"], [], [], False, True, False, "store readback"))
        R.register(ToolSpec("task_control", "control",
                            "stop/pause/resume/retry a task resolved from context (no TASK_ID needed).",
                            ["account_id", "action"], ["task_id"], [], False, True, False, "task state"))
        R.register(ToolSpec("schedule_post", "scheduler",
                            "Persisted delayed action, executed by the scheduler loop.",
                            ["account_id", "run_at", "payload"], [], [], False, True, True, "run record"))

    # -- engine hooks -------------------------------------------------------
    async def _task_tick(self, task: Task) -> None:
        if task.kind == "cross":
            await self.cross.tick(task)
        elif task.kind == "monitor":
            await self._monitor_task_tick(task)
        # delete / forward_bulk run inline; their runners only expire

    async def _monitor_task_tick(self, task: Task) -> None:
        mon = self.monitors_store.data["monitors"].get(task.params.get("monitor_id", ""))
        if not mon:
            self.tasks.set_status(task, TASK_FAILED, "monitor record missing")
            return
        if mon.get("expires_ts") and utc_now() > mon["expires_ts"]:
            mon["status"] = "EXPIRED"
            self.monitors_store.save()
            self.tasks.set_status(task, TASK_EXPIRED, "monitor window over")
            return
        if mon.get("status") == "STOPPED":
            self.tasks.set_status(task, TASK_STOPPED, "monitor stopped")

    async def _schedule_execute(self, item: dict) -> ToolResult:
        payload = item.get("payload") or {}
        account_id = item.get("account_id")
        if payload.get("type") == "post_main":
            text = payload.get("text", "")
            sent, failed, errors = 0, 0, []
            for ch in self.accounts.get_main_channels(account_id):
                r = await self.tools.post_message(account_id, ch["id"], text)
                if r.ok:
                    sent += 1
                else:
                    failed += 1
                    errors.append(f"{ch.get('title')}: {r.error}")
            if sent and not failed:
                return ToolResult.success({"sent": sent})
            if sent:
                return ToolResult(True, "SUCCESS", {"sent": sent, "failed": failed},
                                  "; ".join(errors[:3]), False, None)
            return ToolResult.failure("; ".join(errors[:3]) or "no main channels", retryable=False)
        if payload.get("type") == "goal":
            res = await self.handle_goal(account_id, payload.get("text", ""), source="scheduler")
            return ToolResult(res["ok"], res["status"], {"reply": res["reply"]}, None if res["ok"] else res["reply"])
        return ToolResult.failure("unknown schedule payload")

    # -- AI fallback (optional assistant - never executes anything) ---------
    async def ai_interpret(self, text: str) -> Optional[Decision]:
        if not OPENAI_API_KEY:
            return None
        prompt = (
            "Map this Telegram-operations goal (English/Hinglish) to JSON "
            "{\"intent\": one of " + json.dumps(sorted(AI_ALLOWED_INTENTS)) + ", \"slots\": {...}}. "
            "Slots allowed: " + ", ".join(sorted(AI_ALLOWED_SLOTS)) +
            ". If unclear use {\"intent\":\"UNMAPPED\",\"slots\":{}}. Output only JSON.")
        try:
            async with httpx.AsyncClient(timeout=25) as h:
                r = await h.post(f"{OPENAI_BASE_URL}/chat/completions",
                                 headers={"Authorization": f"Bearer {OPENAI_API_KEY}"},
                                 json={"model": OPENAI_MODEL, "temperature": 0,
                                       "messages": [{"role": "system", "content": prompt},
                                                    {"role": "user", "content": text}]})
            content = r.json()["choices"][0]["message"]["content"]
            m = re.search(r"\{.*\}", content, re.S)
            data = json.loads(m.group(0)) if m else {}
            intent = str(data.get("intent", "UNMAPPED"))
            if intent not in AI_ALLOWED_INTENTS or intent == "UNMAPPED":
                return None
            raw_slots = data.get("slots") if isinstance(data.get("slots"), dict) else {}
            slots = {k: v for k, v in raw_slots.items()
                     if k in AI_ALLOWED_SLOTS and isinstance(v, (str, int, float, bool, list, dict))}
            self.diag.info("ai", "interpret", f"mapped to {intent}")
            return Decision(intent, slots)
        except Exception as exc:
            self.diag.warn("ai", "interpret", f"provider unavailable ({type(exc).__name__})")
            return None

    # -- pre-parser directives (hard patterns, before MiniBrain) -------------
    def _pre_decision(self, account_id: str, text: str) -> Optional[Decision]:
        t = strip_command(text).strip()
        low = t.lower()
        m = re.match(r"create account(?:\s+(?P<label>.+))?$", low)
        if m:
            return Decision("CREATE_ACCOUNT", {"label": (m.group("label") or "").strip()})
        m = re.match(r"login\s+(?:account\s+)?(\d+)\s+(\+?[\d\s-]{8,16})$", low)
        if m:
            return Decision("LOGIN_START", {"account_ref": f"account {m.group(1)}",
                                            "phone": re.sub(r"[^\d+]", "", m.group(2))})
        m = re.match(r"(?:code|otp)\s+(\d{4,10})$", low)
        if m:
            return Decision("LOGIN_COMPLETE", {"code": m.group(1)})
        m = re.search(r"post\s+[\"'](?P<body>.+?)[\"']\s+(?:to\s+)?main channels?\s+in\s+(?P<when>.+)$", low)
        if m:
            dur = parse_duration(m.group("when"))
            if dur:
                return Decision("SCHEDULE_POST", {"text": m.group("body"), "run_in_sec": dur})
        m = re.match(r"post\s+[\"'](?P<body>.+?)[\"']\s+(?:to\s+)?main channels?$", low)
        if m:
            return Decision("POST_MAIN_NOW", {"text": m.group("body")})
        return None

    async def _resolve_names_from_text(self, account_id: str, text: str) -> Optional[ResolvedEntity]:
        t = strip_command(text)
        t = re.sub(r"\b(account|acc|ke|ko|ka|ki|mein|main|channel|channels|chennal|bana|do|kar|add|jod|daal|"
                   r"cross|target|hain|hai|rakh|inspect|check|karo|please|plz|isko|isse|isme|ye|yeh|"
                   r"set|to|the|a|an|of|in|on|for|pe|par|se|aur|and)\b", " ", t.lower())
        t = re.sub(r"\d+", " ", t)
        t = " ".join(t.split())
        if len(t) < 3:
            return None
        try:
            return await self.resolver.resolve(account_id, t)
        except Exception:
            return None

    # -- account picking ------------------------------------------------------
    def _pick_account(self, account_hint: Optional[str], text: str) -> tuple[Optional[str], Optional[dict]]:
        probe = None
        m = re.search(r"(?:account|acc)\s*#?\s*(\d+)", text.lower())
        if m:
            probe = f"account {m.group(1)}"
        aid = self.accounts.resolve_ref(account_hint) or self.accounts.resolve_ref(probe)
        if aid:
            return aid, None
        accs = self.accounts.all()
        if not accs:
            return None, respond(
                "SIR, no account exists yet.\nCreate one in Web Control (Accounts panel) or say: create account <label>.",
                "MISSING_CONTEXT")
        if len(accs) == 1:
            return accs[0]["account_id"], None
        names = ", ".join(f"{i+1}) {a['label']}" for i, a in enumerate(accs))
        return None, respond(
            f"SIR, multiple accounts exist. Tell me which one.\n{names}", "MISSING_CONTEXT")

    # -- the pipeline ----------------------------------------------------------
    async def handle_goal(self, account_hint: Optional[str], text: str, source: str = "web",
                          reply_msg: Any = None) -> dict:
        text = (text or "").strip()
        if not text:
            return respond("SIR, empty goal.", "FAILED")
        aid, err = self._pick_account(account_hint, text)
        if err:
            return err

        # 1) confirmations are account-bound, single-use, short-lived
        answer = self.confirm.matches(text)
        pend = self.confirm.pending(aid)
        if pend is not None and answer is not None:
            if not answer:
                self.confirm.consume(aid)
                return respond("Cancelled, SIR. Nothing was executed.", "WAITING",
                               pend.get("payload", {}).get("intent", ""))
            payload = self.confirm.consume(aid) or {}
            dec = Decision(payload.get("intent", "UNMAPPED"), payload.get("slots") or {})
            self.diag.ok("confirm", "accepted", f"{dec.intent} confirmed", account_id=aid)
            return await self._execute(aid, dec, None, source, confirmed=True)
        elif answer is not None and pend is None:
            return respond("SIR, nothing is awaiting confirmation.", "WAITING")

        # 2) reply-context resolution (Saved Messages reference)
        reply_entity = None
        if reply_msg is not None:
            try:
                reply_entity = await self.resolver.from_reply(aid, reply_msg)
                if reply_entity:
                    self.diag.info("context", "reply", f"reply -> {reply_entity.brief()}", account_id=aid)
            except Exception:
                reply_entity = None

        # 3) goal/intent
        dec = self._pre_decision(aid, text) or self.brain.parse(aid, text, reply_entity)
        dec.slots["_raw"] = text
        if dec.intent == "UNMAPPED":
            ai_dec = await self.ai_interpret(strip_command(text))
            if ai_dec is not None:
                dec = ai_dec
        if dec.intent == "UNMAPPED":
            self.diag.info("brain", "unmapped", short(strip_command(text), 80), account_id=aid)
            return respond(
                "SIR, I could not map that to my toolbox.\nI can: inspect channels, watch channels "
                "(unknown-sender alerts), Cross source posts to your Main Channels, forward/post, "
                "delete with confirmation, configure Main Channels by name or ID, and control running "
                "work.\nTry: help", "FAILED", "UNMAPPED")
        if dec.missing:
            # context-first: attempt alias/title resolution before bothering the user
            ent = await self._resolve_names_from_text(aid, text)
            if ent is not None:
                if "MAIN_CHANNELS" in dec.intent:
                    dec.slots["targets"] = [str(ent.id)]
                elif dec.intent in ("MONITOR_START", "CROSS_START", "FORWARD_TO_MAIN"):
                    dec.slots["source"] = {"id": ent.id, "title": ent.title, "via": "name"}
                else:
                    dec.slots["target"] = {"id": ent.id, "title": ent.title, "via": "name"}
                dec.missing = []
        if dec.missing:
            return respond(
                "SIR, missing exactly:\n- " + "\n- ".join(dec.missing) +
                "\nReply to a message from the target in Saved Messages, or give me @username / channel ID.",
                "MISSING_CONTEXT", dec.intent, dec.to_dict())
        try:
            return await self._execute(aid, dec, reply_entity, source)
        except AmbiguityError as amb:
            return respond(f"SIR, {amb.question}", "MISSING_CONTEXT", dec.intent)
        except ValidationError as ve:
            return respond("SIR, cannot proceed:\n- " + "\n- ".join(ve.missing),
                           "FAILED", dec.intent)
        except FloodWaitError as fe:
            return respond(f"SIR, Telegram asked me to wait {fe.seconds}s (FloodWait respected). "
                           f"Retry shortly.", "WAITING", dec.intent)
        except Exception as exc:
            self.diag.err("core", "execute", f"{dec.intent}: {type(exc).__name__} {short(str(exc),120)}",
                          account_id=aid)
            return respond(f"SIR, execution hit an internal error ({type(exc).__name__}). "
                           f"Details are in Web diagnostics.", "FAILED", dec.intent)

    # -- executor --------------------------------------------------------------
    async def _execute(self, account_id: str, dec: Decision, reply_entity: Optional[ResolvedEntity],
                       source: str, confirmed: bool = False) -> dict:
        S = dec.slots
        acc_label = self.accounts.get(account_id)["label"]

        def via(e: dict) -> str:
            return {"reply": "detected from your reply", "context": "from current context"}.get(
                e.get("via", ""), "")

        # ---- account lifecycle ----
        if dec.intent == "CREATE_ACCOUNT":
            label = S.get("label") or f"Account {len(self.accounts.all()) + 1}"
            try:
                cfg = self.accounts.create(label)
            except ValidationError as ve:
                return respond("SIR, " + "; ".join(ve.missing), "FAILED", dec.intent)
            return respond(
                f"YES SIR. '{cfg['label']}' created.\nNext: login with 'login account "
                f"{len(self.accounts.all())} +91xxxxxxxxxx' or connect in Web Control.",
                "SUCCESS", dec.intent, {"account_id": cfg["account_id"]})
        if dec.intent == "LOGIN_START":
            aid2 = self.accounts.require_single_or(S.get("account_ref"))
            r = await self.accounts.start_login(aid2, S.get("phone", ""))
            if r.get("already"):
                return respond("SIR, that account is already authorized.", "SUCCESS", dec.intent)
            self.ensure_handlers(aid2)
            return respond("SIR, code sent to " + r.get("phone", "your number") +
                           ".\nReply with: code 12345", "WAITING", dec.intent)
        if dec.intent == "LOGIN_COMPLETE":
            rt = self.accounts.runtime.get(account_id)
            pend_any = account_id if (rt and rt.pending_login) else None
            if pend_any is None:
                for a in self.accounts.all():
                    r2 = self.accounts.runtime.get(a["account_id"])
                    if r2 and r2.pending_login:
                        pend_any = a["account_id"]
                        break
            if pend_any is None:
                return respond("SIR, no login is pending. Start with: login account 1 <phone>",
                               "FAILED", dec.intent)
            r = await self.accounts.complete_login(pend_any, S.get("code", ""))
            if r.get("need_password"):
                return respond(
                    "SIR, two-step verification is ON. For security, enter your password in Web Control "
                    "(Accounts panel -> password field), not in chat.", "WAITING", dec.intent)
            self.ensure_handlers(pend_any)
            return respond(f"YES SIR. Authorized as {r.get('name') or 'user'}. Systems online.",
                           "SUCCESS", dec.intent)

        # ---- monitoring ----
        if dec.intent == "MONITOR_START":
            src_slot = S.get("source")
            src = await self.resolver.resolve(account_id, src_slot["id"] if isinstance(src_slot, dict) else src_slot)
            dur = int(S.get("duration_sec") or 86400)
            condition = S.get("condition") or "all"
            note = ""
            if condition == "unknown" and src.kind == "channel":
                condition = "all"
                note = "\n(Channels post as admins, so I am tracking all new posts.)"
            self.memory.learn_channel(account_id, str(src.id), src.title, src.username)
            task = self.tasks.create(account_id, "monitor",
                                     {"source": {"id": src.id, "title": src.title, "kind": src.kind},
                                      "condition": condition},
                                     expires_in=dur, resumable=True,
                                     dedup_key=f"mon:{account_id}:{src.id}:{condition}")
            mon = self.monitors.add(account_id,
                                    {"id": src.id, "title": src.title, "kind": src.kind},
                                    condition, "notify_saved", dur, task.task_id)
            task.params["monitor_id"] = mon["monitor_id"]
            task.progress["steps"] = {"source_resolved": "done", "watch_registered": "done"}
            self.tasks.save_task(task)
            self.tasks.start_runner(task)
            self.ensure_handlers(account_id)
            self.context.update(account_id,
                                last_channel={"id": src.id, "title": src.title},
                                last_task_id=task.task_id, last_monitor_id=mon["monitor_id"])
            src_line = f"{src.title} [{src.id}]"
            if isinstance(src_slot, dict):
                src_line += f" ({via(src_slot)})"
            return respond(
                f"YES SIR. Monitoring active.\nSource: {src_line}\n"
                f"Condition: {'unknown senders (non-admin)' if condition == 'unknown' else 'all new posts'}.\n"
                f"Window: {human_delta(dur)}. Alerts land in your Saved Messages.{note}",
                "SUCCESS", dec.intent, {"task_id": task.task_id, "monitor_id": mon["monitor_id"]})

        if dec.intent == "STOP_ALL_MONITORS":
            n = self.monitors.stop_all(account_id)
            stopped_tasks = 0
            for t in self.tasks.list(account_id):
                if t.kind == "monitor" and t.status == TASK_ACTIVE:
                    self.tasks.set_status(t, TASK_STOPPED, "all monitoring stopped")
                    stopped_tasks += 1
            return respond(f"YES SIR. Monitoring stopped ({n} monitor(s), {stopped_tasks} task(s)).",
                           "SUCCESS", dec.intent, {"monitors_stopped": n})

        # ---- cross ----
        if dec.intent == "CROSS_START":
            src_slot = S.get("source")
            src = await self.resolver.resolve(account_id, src_slot["id"] if isinstance(src_slot, dict) else src_slot)
            self.memory.learn_channel(account_id, str(src.id), src.title, src.username)
            mains = self.accounts.get_main_channels(account_id)
            if not mains:
                raise ValidationError([
                    "no Main Channels configured for " + acc_label,
                    "tell me: 'account N ke main channels <id1> <id2> hain' or set them in Web Control"])
            targets, skipped = [], []
            for ch in mains[:MAX_TARGETS]:
                if int(ch["id"]) == int(src.id):
                    skipped.append(f"{ch.get('title')} (source = target)")
                    continue
                try:
                    ent = await self.resolver.resolve(account_id, str(ch["id"]))
                    targets.append({"id": ent.id, "title": ent.title, "username": ent.username})
                except EntityResolutionError as exc:
                    skipped.append(f"{ch.get('title') or ch['id']} ({exc})")
            if not targets:
                raise ValidationError(["no reachable Main Channel target: " + "; ".join(skipped[:4])])
            for t in self.tasks.list(account_id):
                if t.kind == "cross" and t.status == TASK_ACTIVE and \
                        int(t.params.get("source", {}).get("id", 0) or 0) == int(src.id):
                    return respond(
                        f"SIR, Cross is already active for {src.title} -> {len(t.params.get('targets') or [])} target(s). "
                        f"Say 'isko stop karo' to stop it first.", "WAITING", dec.intent,
                        {"task_id": t.task_id})
            dur = int(S.get("duration_sec") or 86400)
            task = self.tasks.create(account_id, "cross",
                                     {"source": {"id": src.id, "title": src.title, "kind": src.kind},
                                      "targets": targets, "skipped": skipped},
                                     expires_in=dur, resumable=True,
                                     dedup_key=f"cross:{account_id}:{src.id}")
            task.progress["steps"] = {"source_resolved": "done", "targets_loaded": "done",
                                      "delivery": "waiting"}
            self.tasks.save_task(task)
            self.tasks.start_runner(task)
            self.ensure_handlers(account_id)
            self.context.update(account_id,
                                last_channel={"id": src.id, "title": src.title},
                                last_task_id=task.task_id)
            src_line = f"{src.title} [{src.id}]"
            if isinstance(src_slot, dict) and src_slot.get("via"):
                src_line = f"{src_line} ({via(src_slot)})"
            msg = (f"YES SIR. Cross started.\nSource: {src_line}\n"
                   f"Targets loaded: {len(targets)} Main Channel(s).")
            if skipped:
                msg += "\nSkipped: " + "; ".join(skipped[:4])
            msg += (f"\nExpiry: {human_delta(dur)}. Event-driven watching is live; "
                    f"every delivery is verified before I count it.")
            return respond(msg, "SUCCESS", dec.intent, {"task_id": task.task_id,
                                                        "targets": len(targets)})

        if dec.intent == "CROSS_STOP":
            stopped = 0
            for t in self.tasks.list(account_id):
                if t.kind == "cross" and t.status == TASK_ACTIVE:
                    self.tasks.set_status(t, TASK_STOPPED, "cross stopped by user")
                    stopped += 1
            if not stopped:
                return respond("SIR, no active Cross task found.", "FAILED", dec.intent)
            return respond(f"YES SIR. Cross stopped ({stopped} task(s)).", "SUCCESS", dec.intent)

        # ---- inspection / discovery ----
        if dec.intent == "INSPECT_CHANNEL":
            tgt_slot = S.get("target")
            r = await self.tools.inspect_channel(
                account_id, tgt_slot["id"] if isinstance(tgt_slot, dict) else tgt_slot)
            if not r.ok:
                status = r.status
                return respond(f"SIR, inspection failed: {r.error}", status, dec.intent)
            d = r.data
            rights = d.get("rights") or {}
            unknown = sum(1 for m in d.get("last_messages", [])
                          if m.get("sender") and m["sender"] not in ("forwarded",))
            lines = [
                f"CHANNEL REPORT",
                f"{d['title']} [{d['id']}]{(' @' + d['username']) if d.get('username') else ''} ({d['kind']})",
                f"Members: {d.get('participants') if d.get('participants') is not None else 'unknown'} | "
                f"I am admin: {'yes' if rights.get('is_admin') else 'no/unknown'}",
                f"My rights: post={'y' if rights.get('post') else 'n'} "
                f"delete={'y' if rights.get('delete') else 'n'} ban={'y' if rights.get('ban') else 'n'}",
                f"Named senders observed in sample: {unknown}",
                f"Sampled {d.get('message_count_sampled')} messages. Recent:",
            ]
            for m in d.get("last_messages", [])[:8]:
                tag = f" ({m['sender']})" if m.get("sender") else ""
                lines.append(f"  [#{m['id']}] {m['text']}{tag}")
            if isinstance(tgt_slot, dict) and tgt_slot.get("via"):
                lines.append(f"Target {via(tgt_slot)}.")
            self.context.update(account_id, last_channel={"id": d["id"], "title": d["title"]})
            return respond("\n".join(lines), "SUCCESS", dec.intent, d)

        if dec.intent == "LIST_MAIN_CHANNELS":
            mains = self.accounts.get_main_channels(account_id)
            if not mains:
                return respond(
                    f"SIR, {acc_label} has no Main Channels yet.\n"
                    f"Tell me: 'account 1 ke main channels 1234567890 hain' or set them in Web Control.",
                    "SUCCESS", dec.intent, {"main_channels": []})
            lines = [f"YES SIR. {acc_label} Main Channels ({len(mains)}):"]
            for i, ch in enumerate(mains, 1):
                lines.append(f"{i}) {ch.get('title') or '?'} [{ch['id']}]"
                             + (f" @{ch['username']}" if ch.get("username") else ""))
            return respond("\n".join(lines), "SUCCESS", dec.intent, {"main_channels": mains})

        if dec.intent in ("ADD_MAIN_CHANNELS", "SET_MAIN_CHANNELS", "REMOVE_MAIN_CHANNELS"):
            refs = [str(x) for x in (S.get("targets") or [])]
            if not refs and dec.intent == "REMOVE_MAIN_CHANNELS":
                raise ValidationError(["which channel should I remove from Main Channels?"])
            mains = self.accounts.get_main_channels(account_id)
            cur = {str(c["id"]): c for c in mains}
            notes, changed = [], []
            if dec.intent == "SET_MAIN_CHANNELS":
                cur = {}
            for ref_s in refs:
                try:
                    ent = await self.resolver.resolve(account_id, ref_s)
                except EntityResolutionError as exc:
                    notes.append(f"skip {ref_s}: {exc}")
                    continue
                key = str(ent.id)
                if dec.intent == "REMOVE_MAIN_CHANNELS":
                    if key in cur:
                        cur.pop(key)
                        changed.append(f"- {ent.title} [{ent.id}]")
                    continue
                cur[key] = {"id": ent.id, "title": ent.title, "username": ent.username,
                            "added_at": iso(), "via": "jarvis"}
                self.memory.learn_channel(account_id, key, ent.title, ent.username)
                changed.append(f"+ {ent.title} [{ent.id}]")
            out = list(cur.values())[:MAX_TARGETS]
            self.accounts.set_main_channels(account_id, out)
            web_note = " Web Control reflects this immediately."
            lines = [f"YES SIR. {acc_label} Main Channels updated ({len(out)} total)."]
            lines += changed[:8]
            if notes:
                lines.append("Notes: " + "; ".join(notes[:4]))
            lines.append(web_note.strip())
            return respond("\n".join(lines), "SUCCESS", dec.intent,
                           {"main_channels": out, "notes": notes})

        # ---- task control ----
        if dec.intent == "TASK_CONTROL":
            action = S.get("task_action") or "stop"
            task = None
            if S.get("task_id"):
                task = self.tasks.get(str(S["task_id"]))
            if task is None or task.account_id != account_id:
                pool = []
                for t in self.tasks.list(account_id):
                    if action == "retry":
                        if t.status in (TASK_FAILED, TASK_EXPIRED, TASK_WAITING, TASK_PAUSED):
                            pool.append(t)
                    elif t.status == TASK_ACTIVE:
                        pool.append(t)
                if S.get("prefer_kind"):
                    kp = [t for t in pool if t.kind == S["prefer_kind"]]
                    if kp:
                        pool = kp
                if len(pool) == 1:
                    task = pool[0]
                elif len(pool) > 1:
                    opts = []
                    labels = []
                    for i, t in enumerate(pool[:5], 1):
                        src = t.params.get("source", {}).get("title") or t.kind
                        labels.append(f"{i}) {t.kind} '{short(src, 24)}' ({t.status})")
                        opts.append({"intent": "TASK_CONTROL",
                                     "slots": {"task_id": t.task_id, "task_action": action,
                                               "account_ref": None}})
                    self.context.update(account_id, pending_choice={
                        "mapping": [str(i) for i in range(1, len(opts) + 1)],
                        "options": opts, "ts": utc_now()})
                    verb = {"stop": "stop", "pause": "pause", "retry": "retry"}.get(action, action)
                    return respond(
                        "SIR, I found {} matching tasks:\n{}\nWhich one should I {}? (say: 1 / 2 / ...)".format(
                            len(pool[:5]), "\n".join(labels), verb),
                        "MISSING_CONTEXT", dec.intent)
                return respond("SIR, I don't see any matching task.", "FAILED", dec.intent)
            res = await self.tasks.control(task.task_id, action)
            if action == "stop" and task.params.get("monitor_id"):
                self.monitors.stop(task.params["monitor_id"])
            if not res.ok:
                return respond(f"SIR, could not {action}: {res.error}", "FAILED", dec.intent)
            self.context.update(account_id, last_task_id=task.task_id)
            self.diag.ok("tasks", f"control.{action}", f"{task.kind} {task.task_id[:12]}",
                         account_id=account_id, task_id=task.task_id)
            return respond(f"YES SIR. {task.kind.title()} {task.task_id[:12]} -> "
                           f"{res.data['task']['status']}.", "SUCCESS", dec.intent,
                           {"task": res.data["task"]})

        if dec.intent == "LIST_TASKS":
            acts = [t for t in self.tasks.list(account_id)
                    if t.status in (TASK_ACTIVE, TASK_PAUSED, TASK_FAILED, TASK_WAITING, TASK_EXPIRED)]
            mons = self.monitors.active_all(account_id)
            if not acts and not mons:
                return respond("SIR, nothing is running right now. No active tasks or monitors.",
                               "SUCCESS", dec.intent, {"tasks": []})
            lines = [f"YES SIR. Work board ({acc_label}):"]
            for t in sorted(acts, key=lambda x: -x.updated_at)[:10]:
                src = t.params.get("source", {}).get("title") or ""
                tgt_n = len(t.params.get("targets") or [])
                age = human_delta(utc_now() - t.created_at)
                extra = f" -> {tgt_n} targets" if tgt_n else ""
                err = f" | last error: {short(t.last_error, 60)}" if t.last_error else ""
                lines.append(f"- [{t.kind}] {t.task_id[:12]} {t.status} '{short(src, 28)}'{extra} "
                             f"| {age}{err}")
            if mons:
                lines.append(f"Monitors active: {len(mons)}")
            return respond("\n".join(lines), "SUCCESS", dec.intent,
                           {"tasks": [t.public() for t in acts]})

        if dec.intent == "STATUS":
            diag = self.diag.snapshot()
            lines = ["YES SIR. Systems report:"]
            for a in self.accounts.all():
                rt = self.accounts.runtime.get(a["account_id"])
                st = "online+authorized" if (rt and rt.authorized) else \
                     ("connected, NOT authorized" if (rt and rt.connected) else "offline")
                lines.append(f"- {a['label']}: {st} | {len(a.get('main_channels') or [])} main channel(s)")
            lines.append(f"Tasks: {self.tasks.counts_active()} active | "
                         f"Monitors: {len(self.monitors.active_all())} active | "
                         f"Schedules pending: {len(self.scheduler.list_pending())}")
            lines.append(f"Uptime: {human_delta(diag['uptime_sec'])}")
            if diag.get("last_success"):
                ls = diag["last_success"]
                lines.append(f"Last success: {ls['component']}.{ls['operation']} ({ls['ts']})")
            if diag.get("last_failure"):
                lf = diag["last_failure"]
                lines.append(f"Last failure: {lf['component']}.{lf['operation']}: {short(lf['message'], 70)}")
            lines.append("Full diagnostics are on the Web dashboard.")
            return respond("\n".join(lines), "SUCCESS", dec.intent)

        if dec.intent == "HELP":
            lines = [
                "JARVIS capability map (say it naturally, English/Hinglish):",
                "1) '/Cross Start' (reply to a source message) - live cross to Main Channels.",
                "2) 'account 1 ke main channels <id1> <id2> hain' - configure targets.",
                "3) 'Devil Channel ko main channel bana do' - add target by name.",
                "4) 'is channel inspect karo' - deep channel report (reply works).",
                "5) 'isme unknown messages pe dhyan rakhna 2 ghante' - monitor.",
                "6) 'sab monitoring band kar do' - stop every watch.",
                "7) 'delete last 25 messages from this channel' - needs your yes (protected).",
                "8) 'ye task pause/stop/retry karo' - natural task control.",
                "9) 'mera running work dikhao' - work board. 10) 'status' - systems report.",
                "11) 'post \"<text>\" to main channels in 2 hours' - scheduled post.",
                "Commands run from your Saved Messages. Web Control: same brain, same state.",
            ]
            return respond("\n".join(lines), "SUCCESS", dec.intent,
                           {"capabilities": self.registry.capabilities()})

        # ---- destructive: delete (confirmation protected) ----
        if dec.intent == "DELETE_MESSAGES":
            tgt_slot = S.get("target")
            ent = await self.resolver.resolve(
                account_id, tgt_slot["id"] if isinstance(tgt_slot, dict) else tgt_slot)
            count = int(S.get("count") or 5)
            if not confirmed:
                self.confirm.require(
                    account_id, f"delete {count} messages from '{ent.title}'",
                    {"intent": "DELETE_MESSAGES",
                     "slots": {"target": {"id": ent.id, "title": ent.title}, "count": count}})
                return respond(
                    f"SIR, {count} messages delete karne hain in '{ent.title}'. Confirm?\n"
                    f"(reply 'yes' within {CONFIRM_TTL}s - single use)",
                    "WAITING", dec.intent)
            task = self.tasks.create(account_id, "delete",
                                     {"target": {"id": ent.id, "title": ent.title}, "count": count},
                                     expires_in=2 * 3600, resumable=False, interval=3600)
            self.context.update(account_id, last_task_id=task.task_id,
                                last_channel={"id": ent.id, "title": ent.title})
            task.progress["steps"] = {"target_resolved": "done", "confirmed": "done",
                                      "deleting": "active"}
            self.tasks.save_task(task)
            res = await self.tools.delete_messages(account_id, ent.id, count)
            if res.ok:
                d = res.data or {}
                task.progress["steps"]["deleting"] = "done"
                task.progress["steps"]["verified"] = "done"
                task.progress["counters"] = {"deleted": d.get("deleted"), "requested": d.get("requested"),
                                             "verified_gone": (res.verification or {}).get("verified_gone")}
                self.tasks.set_status(task, TASK_COMPLETED, "")
                return respond(
                    f"DONE, SIR.\nDeleted {d.get('deleted')}/{d.get('requested')} messages in "
                    f"'{ent.title}'.\nVerification: {task.progress['counters']['verified_gone']} confirmed "
                    f"gone by re-fetch.", "SUCCESS", dec.intent, d)
            task.progress["steps"]["deleting"] = "failed"
            self.tasks.set_status(task, TASK_FAILED, res.error or "")
            st = res.status
            if st == "PERMISSION_REQUIRED":
                return respond(f"SIR, {res.error}", st, dec.intent)
            return respond(f"FAILED, SIR. Delete incomplete: {res.error}\n"
                           f"Say 'retry karo' to try again.", "FAILED", dec.intent)

        # ---- forward / post to main channels ----
        if dec.intent in ("FORWARD_TO_MAIN", "POST_MAIN_NOW"):
            mains = self.accounts.get_main_channels(account_id)
            if not mains:
                raise ValidationError(["no Main Channels configured for " + acc_label])
            text_to_post = S.get("text")
            count = int(S.get("count") or 1)
            src = None
            if dec.intent == "FORWARD_TO_MAIN":
                src_slot = S.get("source")
                src = await self.resolver.resolve(
                    account_id, src_slot["id"] if isinstance(src_slot, dict) else src_slot)
                self.context.update(account_id, last_channel={"id": src.id, "title": src.title})
            estimated = (len(mains) * count) if src else len(mains)
            if not confirmed and estimated > 10:
                self.confirm.require(
                    account_id, f"forward {count} msg(s) to {len(mains)} main channels",
                    {"intent": dec.intent, "slots": dict(S)})
                return respond(
                    f"SIR, this will deliver ~{estimated} messages across {len(mains)} Main Channels. "
                    f"Confirm? (reply 'yes' within {CONFIRM_TTL}s)", "WAITING", dec.intent)
            task = self.tasks.create(account_id, "forward_bulk",
                                     {"source": {"id": src.id, "title": src.title} if src else None,
                                      "text": text_to_post, "count": count,
                                      "targets": [c["id"] for c in mains]},
                                     expires_in=2 * 3600, resumable=False, interval=3600)
            self.context.update(account_id, last_task_id=task.task_id)
            task.progress["steps"] = {"source_resolved": "done", "execution": "active"}
            self.tasks.save_task(task)
            lines, agg = [], {"sent": 0, "verified": 0, "failed": 0}
            for ch in mains:
                if src and int(ch["id"]) == int(src.id):
                    continue
                if text_to_post:
                    r = await self.tools.post_message(account_id, ch["id"], text_to_post)
                else:
                    r = await self.tools.forward_messages(account_id, src.id, ch["id"], count)
                if r.ok:
                    d = r.data or {}
                    sent = d.get("sent", 1)
                    ver = (r.verification or {}).get("verified", 0)
                    agg["sent"] += sent
                    agg["verified"] += ver
                    lines.append(f"+ {ch.get('title')}: delivered {sent} (verified {ver})")
                else:
                    agg["failed"] += 1
                    mark = "PERMISSION REQUIRED" if r.status == "PERMISSION_REQUIRED" else "failed"
                    lines.append(f"x {ch.get('title')}: {mark} - {short(r.error or '', 70)}")
            ok = agg["failed"] == 0 and agg["sent"] > 0
            task.progress["counters"] = agg
            task.progress["steps"]["execution"] = "done" if agg["sent"] else "failed"
            self.tasks.set_status(task, TASK_COMPLETED if ok else TASK_FAILED,
                                  "" if ok else "partial/0 deliveries")
            head = "DONE, SIR." if ok else ("PARTIAL, SIR." if agg["sent"] else "FAILED, SIR.")
            return respond(f"{head}\n" + "\n".join(lines[:10]),
                           "SUCCESS" if ok else "FAILED", dec.intent, agg)

        if dec.intent == "SCHEDULE_POST":
            text = S.get("text") or ""
            run_in = int(S.get("run_in_sec") or 3600)
            if not self.accounts.get_main_channels(account_id):
                raise ValidationError(["no Main Channels configured for " + acc_label])
            item = self.scheduler.add(account_id, utc_now() + run_in,
                                      {"type": "post_main", "text": text})
            return respond(
                f"YES SIR. Scheduled.\nPost lands in {len(self.accounts.get_main_channels(account_id))} "
                f"Main Channel(s) at {iso(item['run_at'])} ({human_delta(run_in)} from now). "
                f"It persists across restarts.", "SUCCESS", dec.intent,
                {"schedule_id": item["schedule_id"], "run_at": iso(item["run_at"])})

        if dec.intent == "SET_ALIAS":
            alias = str(S.get("alias", "")).strip()
            value = str(S.get("value", "")).strip()
            try:
                ent = await self.resolver.resolve(account_id, value)
            except EntityResolutionError as exc:
                return respond(f"SIR, cannot map alias: {exc}", "FAILED", dec.intent)
            acc = self.memory._acc(account_id)
            acc["aliases"][alias.lower()] = str(ent.id)
            self.memory.store.save()
            self.memory.learn_channel(account_id, str(ent.id), ent.title, ent.username)
            return respond(f"YES SIR. '{alias}' now means {ent.title} [{ent.id}].",
                           "SUCCESS", dec.intent)

        return respond("SIR, that intent has no executor (should not happen).", "FAILED", dec.intent)

    # -- monitor event action ---------------------------------------------
    async def _is_known_sender(self, account_id: str, chat_id: int,
                               sender_id: Optional[int]) -> bool:
        if sender_id is None:
            return True
        rt = self.accounts.runtime.get(account_id)
        if rt and rt.self_id == sender_id:
            return True
        key = (account_id, chat_id)
        ts, known = self.admin_cache.get(key, (0, set()))
        if utc_now() - ts > 600:
            ids: set = set()
            try:
                from telethon.tl.types import ChannelParticipantsAdmins
                client = await self.resolver._client(account_id)
                ent = await self.resolver.resolve(account_id, str(chat_id))
                async for p in client.iter_participants(ent.entity, limit=200,
                                                        filter=ChannelParticipantsAdmins()):
                    ids.add(p.id)
            except Exception:
                ids = known if known else set()
            self.admin_cache[key] = (utc_now(), ids)
            known = ids
        return sender_id in known

    async def _monitor_event(self, account_id: str, mon: dict, msg: Any) -> None:
        mid = mon["monitor_id"]
        try:
            hit = False
            if mon.get("condition") == "unknown":
                if not msg.out:
                    hit = not await self._is_known_sender(account_id, msg.chat_id, msg.sender_id)
            else:
                hit = True
            if hit:
                sender_line = ""
                try:
                    if msg.sender:
                        sender_line = (getattr(msg.sender, "title", None) or
                                       getattr(msg.sender, "first_name", "") or str(msg.sender_id))
                except Exception:
                    sender_line = str(msg.sender_id or "?")
                await self.tools.send_note(
                    account_id,
                    f"MONITOR ALERT [{mid[-6:]}]\n"
                    f"Source: {mon['source'].get('title')} [{mon['source'].get('id')}]\n"
                    f"{'Unknown sender' if mon.get('condition') == 'unknown' else 'New post'}: "
                    f"{short(sender_line, 40)}\n"
                    f"Msg #{msg.id}: {short(msg.raw_text or '[media]', 160)}")
            self.monitors.mark_processed(mid, msg.id, hit)
        except FloodWaitError:
            raise
        except Exception as exc:
            mon["error_count"] = mon.get("error_count", 0) + 1
            mon["last_error"] = type(exc).__name__
            self.monitors_store.save()
            self.diag.err("monitors", "event", type(exc).__name__, account_id=account_id)

    # -- telegram surface -----------------------------------------------------
    def ensure_handlers(self, account_id: str) -> None:
        if not TELETHON_OK:
            return
        rt = self.accounts.runtime.get(account_id)
        if not rt or not rt.client or not rt.connected or not rt.authorized:
            return
        if self._handler_clients.get(account_id) is rt.client:
            return
        self._handler_clients[account_id] = rt.client

        async def handler(event, aid=account_id):
            await self._on_tg_message(aid, event)

        rt.client.add_event_handler(handler, events.NewMessage())
        self.diag.ok("telegram", "handlers", f"event handlers live for {account_id}",
                     account_id=account_id)

    async def _on_tg_message(self, account_id: str, event: Any) -> None:
        msg = event.message
        if msg is None:
            return
        try:
            rt = self.accounts.runtime.get(account_id)
            text = (msg.raw_text or "").strip()
            me_id = rt.self_id if rt else None
            # Saved Messages command surface (your own account only)
            if msg.out and text and me_id and getattr(msg.peer_id, "user_id", None) == me_id:
                is_cmd = looks_like_command(text)
                is_conf = (self.confirm.matches(text) is not None
                           and self.confirm.pending(account_id) is not None)
                if is_cmd or is_conf:
                    reply_msg = None
                    if msg.is_reply:
                        try:
                            reply_msg = await msg.get_reply_message()
                        except Exception:
                            reply_msg = None
                    asyncio.create_task(self._tg_process(account_id, text, reply_msg))
                    return
            # watches (event-driven; polling tick is only a safety net)
            chat_id = msg.chat_id
            if chat_id is None:
                return
            for mon in self.monitors.active_for(account_id, chat_id):
                if int(msg.id) > int(mon.get("last_processed_id") or 0):
                    asyncio.create_task(self._monitor_event(account_id, mon, msg))
            for task in self.cross.active_for(account_id, chat_id):
                if int(msg.id) > int(task.progress.get("last_processed_id") or 0):
                    fresh = self.tasks.get(task.task_id)
                    if fresh:
                        asyncio.create_task(self._cross_event(fresh.task_id, msg))
        except Exception as exc:
            self.diag.err("telegram", "dispatch", type(exc).__name__, account_id=account_id)

    async def _cross_event(self, task_id: str, msg: Any) -> None:
        task = self.tasks.get(task_id)
        if not task or task.status != TASK_ACTIVE:
            return
        try:
            await self.cross.deliver(task, msg)
        except FloodWaitError as fe:
            await asyncio.sleep(fe.seconds)
        except Exception as exc:
            self.diag.err("cross", "event", type(exc).__name__,
                          account_id=task.account_id, task_id=task.task_id)

    async def _tg_process(self, account_id: str, text: str, reply_msg: Any) -> None:
        try:
            res = await self.handle_goal(account_id, text, source="telegram", reply_msg=reply_msg)
            reply = res.get("reply") or "..."
            rt = self.accounts.runtime.get(account_id)
            if not rt or not rt.client:
                return
            for chunk in chunk_text(reply):
                try:
                    await rt.client.send_message("me", chunk)
                except FloodWaitError as fe:
                    await asyncio.sleep(fe.seconds)
                    try:
                        await rt.client.send_message("me", chunk)
                    except Exception:
                        pass
                except Exception as exc:
                    self.diag.err("telegram", "respond", type(exc).__name__, account_id=account_id)
                    break
        except Exception as exc:
            self.diag.err("telegram", "process", f"{type(exc).__name__}: {short(str(exc), 120)}",
                          account_id=account_id)

    # -- snapshots for web ---------------------------------------------------
    def status_snapshot(self) -> dict:
        diag = self.diag.snapshot()
        accounts = []
        for a in self.accounts.all():
            pub = self.accounts.public(a["account_id"])
            pub["memory_aliases"] = len(self.memory.public(a["account_id"])["aliases"])
            pub["known_channels"] = self.memory.public(a["account_id"])["known_channels_count"]
            accounts.append(pub)
        tasks = [t.public() for t in
                 sorted(self.tasks.list(), key=lambda x: -x.updated_at)][:60]
        confirmations = []
        for a in self.accounts.all():
            c = self.confirm.public(a["account_id"])
            if c:
                c["account_id"] = a["account_id"]
                confirmations.append(c)
        persistence = {}
        for name in ("accounts", "sessions", "tasks", "monitors", "schedules",
                     "memory", "context", "diag"):
            persistence[name] = (DATA_DIR / f"{name}.json").exists()
        return {
            "ok": True, "time": iso(),
            "uptime_sec": diag["uptime_sec"],
            "telethon": TELETHON_OK, "ai_available": bool(OPENAI_API_KEY),
            "accounts": accounts,
            "tasks": tasks,
            "monitors": self.monitors.active_all(),
            "schedules": self.scheduler.list_pending(),
            "confirmations": confirmations,
            "diag": diag,
            "persistence": persistence,
            "limits": {"tasks": MAX_ACTIVE_TASKS, "monitors": MAX_MONITORS,
                       "schedules": MAX_SCHEDULES},
        }

    # -- lifecycle ------------------------------------------------------------
    async def startup(self) -> None:
        self.diag.info("boot", "start", "startup validation running")
        if not TELETHON_OK:
            self.diag.err("boot", "deps", f"telethon missing: {TELETHON_ERR}")
        if not (ENV_API_ID and ENV_API_HASH):
            any_creds = any(a.get("api_id") for a in self.accounts.all())
            if not any_creds:
                self.diag.warn("boot", "env",
                               "no api credentials yet (set JARVIS_API_ID/JARVIS_API_HASH or per-account)")
        self.scheduler.start()
        # reconnect + restore in the background - the HTTP port must bind immediately
        asyncio.create_task(self._restore_accounts())
        self.diag.ok("boot", "complete", f"uptime begins; {len(self.accounts.all())} account(s)")
        self.diag.persist()

    async def _restore_accounts(self) -> None:
        """Runs after the HTTP listener is up - reconnects + resumes work."""
        for a in self.accounts.all():
            aid = a["account_id"]
            try:
                rt = await self.accounts.connect(aid)
                if rt.authorized:
                    self.ensure_handlers(aid)
                    # resume only resumable active tasks on authorized accounts
                    for t in self.tasks.list(aid):
                        if t.status == TASK_ACTIVE and t.resumable:
                            self.tasks.start_runner(t)
                else:
                    for t in self.tasks.list(aid):
                        if t.status == TASK_ACTIVE:
                            self.tasks.set_status(t, TASK_WAITING,
                                                  "account not authorized at boot - login, then 'retry karo'")
            except Exception as exc:
                self.diag.err("boot", "account.restore", f"{a['label']}: {type(exc).__name__}",
                              account_id=aid)
                for t in self.tasks.list(aid):
                    if t.status == TASK_ACTIVE:
                        self.tasks.set_status(t, TASK_WAITING,
                                              f"account offline at boot ({type(exc).__name__})")

    async def shutdown(self) -> None:
        self.diag.info("boot", "shutdown", "graceful stop")
        for t in self.tasks.list():
            if t.status == TASK_ACTIVE:
                self.tasks.save_task(t)   # state persisted; runners stop
        await self.tasks.shutdown()
        for a in self.accounts.all():
            await self.accounts.disconnect(a["account_id"])
        self.diag.persist()


CORE: Optional[JarvisCore] = None


# ----------------------------------------------------------------------------
# 17. WEB API - same brain, same state as Telegram
# ----------------------------------------------------------------------------

def build_app() -> "FastAPI":
    @asynccontextmanager
    async def lifespan(_app: "FastAPI"):
        global CORE
        CORE = JarvisCore()
        await CORE.startup()
        yield
        await CORE.shutdown()

    app = FastAPI(title="JARVIS CORE", docs_url=None, redoc_url=None, openapi_url=None,
                  lifespan=lifespan)

    async def body(request: "Request") -> dict:
        try:
            data = await request.json()
            return data if isinstance(data, dict) else {}
        except Exception:
            return {}

    def guard() -> Optional["JSONResponse"]:
        if CORE is None:
            return JSONResponse({"ok": False, "error": "core booting"}, status_code=503)
        return None

    @app.get("/")
    async def index() -> "FileResponse":
        return FileResponse(ROOT / "index.html", headers={"Cache-Control": "no-store"})

    @app.get("/healthz")
    async def healthz() -> "JSONResponse":
        return JSONResponse({"ok": True, "up": True, "time": iso()})

    @app.get("/api/status")
    async def api_status() -> "JSONResponse":
        g = guard()
        if g:
            return g
        return JSONResponse(CORE.status_snapshot())

    @app.get("/api/capabilities")
    async def api_caps() -> "JSONResponse":
        g = guard()
        if g:
            return g
        return JSONResponse({"ok": True, "tools": CORE.registry.capabilities()})

    @app.post("/api/goal")
    async def api_goal(request: "Request") -> "JSONResponse":
        g = guard()
        if g:
            return g
        b = await body(request)
        text = str(b.get("text") or "").strip()
        if not text:
            return JSONResponse({"ok": False, "error": "empty goal"}, status_code=400)
        t_low = text.lower()
        wrapped = text if (looks_like_command(text) or t_low in AFFIRM or t_low in DENY) \
            else f"/AI {text}"
        res = await CORE.handle_goal(b.get("account_ref") or b.get("account_id"),
                                     wrapped, source="web")
        return JSONResponse(res)

    @app.post("/api/accounts")
    async def api_account_create(request: "Request") -> "JSONResponse":
        g = guard()
        if g:
            return g
        b = await body(request)
        try:
            cfg = CORE.accounts.create(str(b.get("label") or "").strip() or None,
                                       str(b.get("api_id") or ""), str(b.get("api_hash") or ""))
        except ValidationError as ve:
            return JSONResponse({"ok": False, "error": "; ".join(ve.missing)}, status_code=400)
        return JSONResponse({"ok": True, "account": CORE.accounts.public(cfg["account_id"])})

    @app.post("/api/accounts/{aid}/login/start")
    async def api_login_start(aid: str, request: "Request") -> "JSONResponse":
        g = guard()
        if g:
            return g
        b = await body(request)
        try:
            r = await CORE.accounts.start_login(aid, str(b.get("phone") or ""))
            CORE.ensure_handlers(aid)
            return JSONResponse({"ok": True, **r})
        except ValidationError as ve:
            return JSONResponse({"ok": False, "error": "; ".join(ve.missing)}, status_code=400)
        except Exception as exc:
            return JSONResponse({"ok": False, "error": type(exc).__name__}, status_code=400)

    @app.post("/api/accounts/{aid}/login/complete")
    async def api_login_complete(aid: str, request: "Request") -> "JSONResponse":
        g = guard()
        if g:
            return g
        b = await body(request)
        try:
            r = await CORE.accounts.complete_login(aid, str(b.get("code") or ""),
                                                   str(b.get("password") or ""))
            CORE.ensure_handlers(aid)
            return JSONResponse({"ok": bool(r.get("ok")), **r})
        except ValidationError as ve:
            return JSONResponse({"ok": False, "error": "; ".join(ve.missing)}, status_code=400)
        except Exception as exc:
            return JSONResponse({"ok": False, "error": type(exc).__name__}, status_code=400)

    @app.post("/api/accounts/{aid}/session")
    async def api_session_import(aid: str, request: "Request") -> "JSONResponse":
        g = guard()
        if g:
            return g
        b = await body(request)
        try:
            r = await CORE.accounts.import_session(aid, str(b.get("session_string") or ""))
            CORE.ensure_handlers(aid)
            # never echo the session back
            return JSONResponse({"ok": True, **r})
        except ValidationError as ve:
            return JSONResponse({"ok": False, "error": "; ".join(ve.missing)}, status_code=400)
        except Exception as exc:
            return JSONResponse({"ok": False, "error": type(exc).__name__}, status_code=400)

    @app.post("/api/accounts/{aid}/connect")
    async def api_connect(aid: str) -> "JSONResponse":
        g = guard()
        if g:
            return g
        try:
            rt = await CORE.accounts.connect(aid)
            CORE.ensure_handlers(aid)
            return JSONResponse({"ok": True, "authorized": rt.authorized, "connected": rt.connected})
        except ValidationError as ve:
            return JSONResponse({"ok": False, "error": "; ".join(ve.missing)}, status_code=400)
        except Exception as exc:
            return JSONResponse({"ok": False, "error": type(exc).__name__}, status_code=400)

    @app.post("/api/accounts/{aid}/disconnect")
    async def api_disconnect(aid: str) -> "JSONResponse":
        g = guard()
        if g:
            return g
        await CORE.accounts.disconnect(aid)
        return JSONResponse({"ok": True})

    @app.delete("/api/accounts/{aid}")
    async def api_delete_account(aid: str) -> "JSONResponse":
        g = guard()
        if g:
            return g
        CORE.accounts.delete(aid)
        return JSONResponse({"ok": True})

    @app.post("/api/accounts/{aid}/config")
    async def api_config(aid: str, request: "Request") -> "JSONResponse":
        g = guard()
        if g:
            return g
        b = await body(request)
        refs = b.get("main_channels")
        if not isinstance(refs, list):
            return JSONResponse({"ok": False, "error": "main_channels must be a list of ids/@usernames"},
                                status_code=400)
        out, notes = [], []
        cur: dict[str, dict] = {}
        for ref in refs[:MAX_TARGETS]:
            try:
                ent = await CORE.resolver.resolve(aid, str(ref).strip())
                cur[str(ent.id)] = {"id": ent.id, "title": ent.title, "username": ent.username,
                                    "added_at": iso(), "via": "web"}
                CORE.memory.learn_channel(aid, str(ent.id), ent.title, ent.username)
            except Exception as exc:
                notes.append(f"{ref}: {type(exc).__name__}: {short(str(exc), 60)}")
        CORE.accounts.set_main_channels(aid, list(cur.values()))
        CORE.diag.ok("config", "main_channels", f"{len(cur)} main channel(s) set from web", account_id=aid)
        return JSONResponse({"ok": True, "main_channels": list(cur.values()), "notes": notes})

    @app.post("/api/tasks/{tid}/action")
    async def api_task_action(tid: str, request: "Request") -> "JSONResponse":
        g = guard()
        if g:
            return g
        b = await body(request)
        action = str(b.get("action") or "")
        task = CORE.tasks.get(tid)
        if not task:
            return JSONResponse({"ok": False, "error": "task not found"}, status_code=404)
        res = await CORE.tasks.control(task.task_id, action)
        if action == "stop" and task.params.get("monitor_id"):
            CORE.monitors.stop(task.params["monitor_id"])
        return JSONResponse(res.to_dict())

    @app.post("/api/monitors/{mid}/stop")
    async def api_monitor_stop(mid: str) -> "JSONResponse":
        g = guard()
        if g:
            return g
        ok = CORE.monitors.stop(mid)
        return JSONResponse({"ok": ok})

    @app.post("/api/schedules/{sid}/cancel")
    async def api_schedule_cancel(sid: str) -> "JSONResponse":
        g = guard()
        if g:
            return g
        ok = CORE.scheduler.cancel(sid)
        return JSONResponse({"ok": ok})

    @app.post("/api/confirm")
    async def api_confirm(request: "Request") -> "JSONResponse":
        g = guard()
        if g:
            return g
        b = await body(request)
        answer = "yes" if b.get("answer") in (True, "yes", "YES", "haan") else "no"
        res = await CORE.handle_goal(b.get("account_id"), answer, source="web")
        return JSONResponse(res)

    return app


app = build_app() if WEB_OK else None


# ----------------------------------------------------------------------------
# 18. ENTRYPOINT
# ----------------------------------------------------------------------------

def banner() -> None:
    print("=" * 64)
    print(" JARVIS CORE - autonomous telegram operations (fresh build)")
    print("=" * 64)
    print(f" bind        : 0.0.0.0:{PORT}  (PORT env: {'set -> ' + os.environ['PORT'] if os.environ.get('PORT') else 'not set, using fallback'})")
    print(f" data dir    : {DATA_DIR}")
    print(f" telethon    : {'ok' if TELETHON_OK else 'MISSING - ' + TELETHON_ERR}")
    print(f" ai provider : {'configured (' + OPENAI_MODEL + ')' if OPENAI_API_KEY else 'not configured (deterministic mode)'}")
    print(f" api creds   : {'env set' if (ENV_API_ID and ENV_API_HASH) else 'env missing (per-account creds or set JARVIS_API_ID/JARVIS_API_HASH)'}")
    print("=" * 64)


if __name__ == "__main__":
    banner()
    if not WEB_OK:
        print("FATAL: fastapi/uvicorn/httpx missing. pip install -r requirements.txt")
        sys.exit(1)
    print(f" STARTING HTTP SERVER on 0.0.0.0:{PORT} ...", flush=True)
    try:
        uvicorn.run(app, host=HOST, port=PORT, log_level="info", proxy_headers=True)
    except Exception as exc:
        print(f"FATAL: http server failed to start: {type(exc).__name__}: {exc}")
        sys.exit(1)
