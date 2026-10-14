"""Core templates and Stratum V1 sessions feeding the same hashing engine."""
import copy
import json
import os
import socket
import ssl
import threading
import time
from decimal import Decimal
from urllib.parse import urlsplit
from . import VERSION
from .rpc import RPC, RPCError
from .protocol import DIFF1, core_work, pool_work, target_from_difficulty
from .difficulty import apply_target

def endpoint(value, tls_default=True):
    parsed = urlsplit(value if "://" in value else ("stratum+ssl://" if tls_default else "stratum+tcp://") + value)
    if parsed.scheme not in ("stratum+tcp", "stratum+ssl", "stratum+tls") or not parsed.hostname or not parsed.port:
        raise ValueError("Pool must be host:port, stratum+tcp://host:port or stratum+ssl://host:port")
    if parsed.username or parsed.password or parsed.path not in ("", "/") or parsed.query or parsed.fragment:
        raise ValueError("Keep pool credentials in pool_user / pool_password, not in the endpoint")
    return parsed.hostname, parsed.port, parsed.scheme != "stratum+tcp"

class PrimaryReachable(ConnectionError):
    """A planned return from backup; it must not count as another failure."""

class CoreConnection:
    def __init__(self, config, emit):
        self.c, self.emit = config, emit
        self.rpc = RPC(config)
        self.stop = threading.Event()
        self.refresh = threading.Event()
        self.lock = threading.Lock()
        self.template = None
        self.generation = 0
        self.extra = int.from_bytes(os.urandom(8), "little")
        self.connected = False
        self.label = self.rpc.url
        self.thread = threading.Thread(target=self.run, daemon=True, name="core-templates")

    def start(self):
        self.thread.start()

    def close(self):
        with self.lock:
            self.stop.set()
            self.connected = False
        self.refresh.set()

    @staticmethod
    def template_identity(template):
        # Core updates curtime on every short poll. Existing headers remain valid
        # on that parent; a changed longpoll marker alone is also not new work.
        return {k: v for k, v in template.items() if k not in ('curtime', 'longpollid')}

    def run(self):
        while not self.stop.is_set():
            self.refresh.clear()
            try:
                if not self.connected:
                    self.rpc.check()
                with self.lock:
                    generation = self.generation
                # A timed-out long poll can keep a Core HTTP worker occupied
                # until its watched tip/mempool changes. Use ordinary polling
                # so a quiet chain cannot accumulate abandoned server waiters.
                template = self.rpc.call("getblocktemplate", [{"rules":["segwit"]}])
                with self.lock:
                    if self.stop.is_set():
                        return
                    if generation != self.generation:
                        # A concurrent accepted submission retired this work.
                        # Discard the in-flight response and fetch the new tip.
                        continue
                    changed = (self.template is None or
                               self.template_identity(template) != self.template_identity(self.template))
                    self.template = template
                    if changed:
                        self.generation += 1
                    self.connected = True
                if changed:
                    self.emit("job", f"Core template · height {template['height']}", height=template["height"])
                if not self.stop.is_set():
                    self.refresh.wait(self.c["template_refresh"])
            except Exception as e:
                with self.lock:
                    self.connected = False
                    self.generation += 1
                    self.template = None
                self.emit("connection", str(e), **(e.diagnostics() if isinstance(e, RPCError) else {}))
                if not self.stop.is_set():
                    self.refresh.wait(self.c["retry_seconds"])

    def work(self):
        with self.lock:
            if not self.connected or self.template is None:
                return None
            template, generation = self.template, self.generation
            self.extra = (self.extra + 1) & ((1 << 64) - 1)
            extra = self.extra.to_bytes(8,"little")
        work = core_work(template, self.c["address"], self.c["network"], extra, generation)
        return apply_target(self.c, work)

    def valid(self, work):
        return self.connected and work.generation == self.generation and not self.stop.is_set()

    def submit(self, work, nonce):
        if not self.valid(work):
            return False, "stale template", False
        header = work.header[:76] + nonce.to_bytes(4,"little")
        result = self.rpc.call("submitblock", [(header + work.data["body"]).hex()])
        accepted = result is None
        if accepted:
            with self.lock:
                # A returned acceptance retires this template immediately;
                # Wake polling immediately to fetch the next parent.
                if work.generation == self.generation:
                    self.template = None
                    self.generation += 1
            self.refresh.set()
            try:
                receipt = self.verify_accepted(work, nonce)
            except Exception as error:
                # Core may have accepted the block, so a readback failure is
                # unknown, not rejection and not permission to resubmit.
                return None, 'Block submitted; acceptance verification incomplete: ' + str(error), False
            self.emit('block_verified', 'Core block independently verified', **receipt)
        return accepted, "block accepted" if accepted else str(result), accepted

    def verify_accepted(self, work, nonce):
        from .block_validation import verify_accepted_block
        return verify_accepted_block(self.rpc, work, nonce)

class PoolConnection:
    def __init__(self, config, emit):
        self.c, self.emit = config, emit
        self.stop = threading.Event()
        self.lock = threading.RLock()
        self.send_lock = threading.Lock()
        self.socket = None
        self.connected = False
        self.label = config["pool"]
        self.generation = 0
        self.params = None
        self.extra1 = ""
        self.extra_size = 0
        self.counter = 0
        self.next_target = DIFF1
        self.target = DIFF1
        self.request_id = 0
        self.pending = {}
        self.user = config["pool_user"] or config["address"] + "." + config["worker"]
        self.thread = threading.Thread(target=self.run, daemon=True, name="pool-stratum")

    def start(self):
        self.thread.start()

    def close(self):
        self.stop.set()
        with self.lock:
            sock = self.socket
        if sock:
            try:
                sock.shutdown(socket.SHUT_RDWR)
            except OSError:
                pass

    def send(self, method, params, kind="ignore"):
        with self.lock:
            if self.socket is None:
                raise ConnectionError("Pool disconnected")
            self.request_id += 1
            rid = self.request_id
            waiter = {"kind":kind,"event":threading.Event(),"result":None,"error":None,"sent":time.monotonic()}
            self.pending[rid] = waiter
            sock = self.socket
        try:
            with self.send_lock:
                sock.sendall((json.dumps({"id":rid,"method":method,"params":params})+"\n").encode())
        except Exception:
            with self.lock:
                self.pending.pop(rid, None)
            raise
        return waiter

    def receive(self, message):
        method = message.get("method")
        params = message.get("params", [])
        with self.lock:
            if method == "mining.set_difficulty":
                difficulty = params[0]
                self.next_target = target_from_difficulty(difficulty)
                self.emit("difficulty", f"Share difficulty {difficulty}")
            elif method == "mining.set_extranonce":
                self.extra1, self.extra_size = str(params[0]), int(params[1])
                if not 1 <= self.extra_size <= 16:
                    raise ValueError("Unsupported pool extranonce length")
                bytes.fromhex(self.extra1)
                self.counter = 0
                self.generation += 1
            elif method == "mining.notify":
                if len(params) < 9:
                    raise ValueError("Incomplete Stratum job")
                self.params = copy.deepcopy(params)
                self.target = self.next_target
                self.generation += 1
                # Do not rewind extranonce2 when a pool reuses a job ID.
                self.emit("job", f"Pool job {str(params[0])[:40]}")
            elif method == "client.reconnect":
                # Reconnect only to configured destinations; don't trust redirection messages.
                raise ConnectionError("Pool requested reconnect")
            elif method == "client.get_version":
                with self.send_lock:
                    self.socket.sendall((json.dumps({"id":message.get("id"),"result":"BTC Miner/"+VERSION,"error":None})+"\n").encode())
            elif message.get("id") is not None:
                waiter = self.pending.pop(message["id"], None)
                if waiter is None:
                    return
                waiter["result"], waiter["error"] = message.get("result"), message.get("error")
                waiter["event"].set()
                kind = waiter["kind"]
                if kind == "subscribe":
                    if waiter["error"] or not isinstance(waiter["result"], list) or len(waiter["result"]) < 3:
                        raise ValueError("Pool rejected subscription")
                    self.extra1 = str(waiter["result"][1]); self.extra_size = int(waiter["result"][2])
                    bytes.fromhex(self.extra1)
                    if not 1 <= self.extra_size <= 16:
                        raise ValueError("Unsupported pool extranonce length")
                    password = os.environ.get(self.c["pool_password_env"], self.c["pool_password"])
                    self.send("mining.authorize", [self.user,password], "authorize")
                elif kind == "authorize":
                    if waiter["error"] or waiter["result"] is not True:
                        raise ValueError("Pool authorization failed; check pool_user and password")
                    self.connected = True
                    self.emit("connection", f"Connected · {self.label}")
                    if self.c["pool_difficulty"] > 0:
                        self.send("mining.suggest_difficulty", [self.c["pool_difficulty"]])

    def run(self):
        failures = 0
        use_backup = False
        while not self.stop.is_set():
            value = self.c["backup"] if use_backup else self.c["pool"]
            sock = None
            try:
                host, port, tls = endpoint(value, self.c["tls"])
                self.label = value
                self.emit("connection", f"Connecting · {value}")
                sock = socket.create_connection((host,port), timeout=self.c["connect_timeout"])
                if tls:
                    sock = ssl.create_default_context().wrap_socket(sock,server_hostname=host)
                sock.settimeout(1)
                with self.lock:
                    self.socket = sock
                    self.params = None
                    self.connected = False
                    self.counter = 0
                    self.next_target = DIFF1
                    self.generation += 1
                self.send("mining.subscribe", ["BTC Miner/"+VERSION], "subscribe")
                buffer = b""; began = last_message = time.monotonic()
                while not self.stop.is_set():
                    now = time.monotonic()
                    if not self.connected and now - began > 30:
                        raise TimeoutError("Pool handshake timed out")
                    if now - last_message > 180:
                        raise TimeoutError("Pool has been silent for 180 seconds")
                    if use_backup and now - began >= self.c["primary_retry_seconds"]:
                        # Probe TCP/TLS before leaving a working backup connection.
                        try:
                            ph, pp, ptls = endpoint(self.c["pool"], self.c["tls"])
                            probe = socket.create_connection((ph,pp),timeout=2)
                            try:
                                if ptls:
                                    probe = ssl.create_default_context().wrap_socket(probe,server_hostname=ph)
                            finally:
                                probe.close()
                        except OSError:
                            began = now
                        else:
                            use_backup = False; failures = 0
                            raise PrimaryReachable("Primary endpoint is reachable; reconnecting")
                    try:
                        chunk = sock.recv(65536)
                    except socket.timeout:
                        continue
                    if not chunk:
                        raise ConnectionError("Pool closed the connection")
                    buffer += chunk
                    if len(buffer) > 2 * 1024 * 1024:
                        raise ValueError("Stratum message exceeded 2 MiB")
                    while b"\n" in buffer:
                        line, buffer = buffer.split(b"\n",1)
                        if line.strip():
                            self.receive(json.loads(line, parse_float=Decimal))
                            last_message = time.monotonic()
                    if self.connected and time.monotonic() - began >= 30:
                        failures = 0
                    with self.lock:
                        for rid, pending in list(self.pending.items()):
                            if now - pending["sent"] > 30:
                                pending["error"] = "response timeout"; pending["event"].set()
                                self.pending.pop(rid, None)
            except Exception as e:
                if not self.stop.is_set():
                    self.emit("connection", str(e))
                    if not isinstance(e, PrimaryReachable):
                        failures += 1
                        if self.c["backup"] and failures >= self.c["retries_before_backup"]:
                            use_backup = not use_backup; failures = 0
                            self.emit("connection", "Switching to backup" if use_backup else "Returning to primary")
            finally:
                with self.lock:
                    self.connected = False; self.socket = None; self.params = None
                    self.generation += 1
                    for pending in self.pending.values():
                        pending["error"] = "connection lost; submission outcome unknown"
                        pending["event"].set()
                    self.pending.clear()
                if sock:
                    sock.close()
            self.stop.wait(self.c["retry_seconds"])

    def work(self):
        with self.lock:
            if not self.connected or self.params is None or not self.extra_size:
                return None
            if self.counter >= 1 << (8*self.extra_size):
                raise RuntimeError("Extranonce space exhausted; reconnect to obtain a new subscription")
            extra = self.counter.to_bytes(self.extra_size,"big").hex(); self.counter += 1
            return pool_work(self.params, self.extra1, extra, self.target, self.generation)

    def valid(self, work):
        return self.connected and work.generation == self.generation and not self.stop.is_set()

    def submit(self, work, nonce):
        if not self.valid(work):
            return False, "stale job", False
        waiter = self.send("mining.submit", [self.user, work.data["job_id"], work.data["extranonce2"],
                                            work.data["ntime"], f"{nonce:08x}"], "share")
        deadline = time.monotonic() + 15
        while not waiter["event"].wait(.2):
            if self.stop.is_set() or time.monotonic() > deadline:
                return None, "submission outcome unknown (timeout/disconnect)", False
        if waiter["error"]:
            return (None if isinstance(waiter["error"], str) else False), str(waiter["error"]), False
        accepted = waiter["result"] is True
        return accepted, "share accepted" if accepted else "share rejected", False
