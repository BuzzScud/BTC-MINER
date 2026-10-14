import base64
import json
import os
import http.client
import ipaddress
import re
import socket
import time
import urllib.request
import urllib.error
from pathlib import Path
from .platform_support import bitcoin_directory

PORTS = {"mainnet":8332,"testnet":18332,"testnet4":48332,"regtest":18443}
CHAIN = {"mainnet":"main","testnet":"test","testnet4":"testnet4","regtest":"regtest"}

def is_local(host):
    if host.lower() == 'localhost':
        return True
    try:
        return ipaddress.ip_address(host.strip('[]')).is_loopback
    except ValueError:
        return False


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        raise ValueError('Bitcoin Core RPC redirects are refused')

class RPCError(RuntimeError):
    """Safe transport diagnostics: never retain params, auth or response text."""
    def __init__(self, method, kind, elapsed, timeout, http_status=None, rpc_code=None):
        self.method = method if isinstance(method, str) and re.fullmatch(r'[a-z][a-z0-9_]{0,63}', method) else 'unknown'
        self.kind = kind
        self.elapsed_seconds = round(elapsed, 6)
        self.timeout_seconds = timeout
        self.http_status = http_status
        self.rpc_code = rpc_code if isinstance(rpc_code, int) and not isinstance(rpc_code, bool) else None
        suffix = f' HTTP {http_status}' if http_status is not None else ''
        if self.rpc_code is not None: suffix += f' RPC {self.rpc_code}'
        super().__init__(f'Bitcoin Core {self.method}: {kind}{suffix} after {elapsed:.3f}s (socket timeout {timeout}s)')

    def diagnostics(self):
        return {'rpc_method': self.method, 'rpc_error_kind': self.kind,
                'rpc_elapsed_seconds': self.elapsed_seconds, 'rpc_timeout_seconds': self.timeout_seconds,
                'http_status': self.http_status, 'rpc_code': self.rpc_code}

class RPC:
    def __init__(self, config):
        self.c = config
        host = config["rpc_host"]
        if ":" in host:
            host = "[" + host.strip("[]") + "]"
        scheme = 'https' if config.get('rpc_tls', False) else 'http'
        self.url = f"{scheme}://{host}:{config['rpc_port'] or PORTS[config['network']]}/"
        # Do not route local cookies through an environment-configured proxy.
        self.opener = urllib.request.build_opener(urllib.request.ProxyHandler({}), NoRedirect())

    def cookie(self):
        if self.c["rpc_cookie"]:
            return Path(self.c["rpc_cookie"]).expanduser()
        root = Path(self.c["rpc_datadir"]).expanduser() if self.c["rpc_datadir"] else bitcoin_directory()
        sub = {"mainnet":"","regtest":"regtest","testnet":"testnet3","testnet4":"testnet4"}[self.c["network"]]
        return root / sub / ".cookie"

    def local_config_auth(self):
        """Use existing Core credentials only for its matching loopback RPC port.

        Explicit cookie/user settings take precedence. Secrets remain in Core's
        config file and in memory; they are never saved in miner settings.
        Includes/custom config paths require explicit miner authentication.
        """
        if self.c["rpc_cookie"] or self.c["rpc_host"].strip("[]") not in ("127.0.0.1", "::1", "localhost"):
            return None
        root = Path(self.c["rpc_datadir"]).expanduser() if self.c["rpc_datadir"] else bitcoin_directory()
        try:
            lines = (root/"bitcoin.conf").read_text().splitlines()
        except OSError:
            return None
        sections = {"": {}}; section = ""
        for line in lines:
            line = line.split("#", 1)[0].strip()
            if line.startswith("[") and line.endswith("]"):
                section = line[1:-1].strip(); sections.setdefault(section, {})
            elif "=" in line:
                key, value = line.split("=", 1)
                sections[section][key.strip()] = value.strip()
        if any('includeconf' in values for values in sections.values()):
            return None
        config = dict(sections[""], **sections.get(CHAIN[self.c["network"]], {}))
        port = self.c["rpc_port"] or PORTS[self.c["network"]]
        if str(config.get("rpcport", PORTS[self.c["network"]])) != str(port):
            return None
        user, password = config.get("rpcuser"), config.get("rpcpassword")
        return user + ":" + password if user and password else None

    def call(self, method, params=None, timeout=None):
        if not is_local(self.c['rpc_host']):
            if not self.c.get('rpc_tls', False):
                raise ValueError('Remote Core RPC requires rpc_tls=on with a trusted HTTPS proxy, or a local secure tunnel')
            if not (self.c['rpc_user'] or self.c['rpc_cookie']):
                raise ValueError('Remote Core RPC requires an explicit RPC username or cookie path; local cookie discovery is disabled')
        user = self.c["rpc_user"]
        if user:
            password = os.environ.get(self.c["rpc_password_env"], "")
            if not password:
                raise ValueError(f"Set {self.c['rpc_password_env']} or use cookie authentication")
            auth = user + ":" + password
        else:
            try:
                auth = self.cookie().read_text().strip()
            except OSError:
                auth = self.local_config_auth()
                if auth is None:
                    raise ValueError(f"Bitcoin Core cookie not found: {self.cookie()}; configure RPC authentication in /setup") from None
        payload = json.dumps({"jsonrpc":"1.0","id":"btc-miner","method":method,"params":params or []}).encode()
        req = urllib.request.Request(self.url, data=payload, headers={"Content-Type":"application/json",
                                    "Authorization":"Basic " + base64.b64encode(auth.encode()).decode()})
        deadline = self.c["rpc_timeout"] if timeout is None else timeout
        started = time.monotonic()
        status = None
        def failure(kind, code=None):
            return RPCError(method, kind, time.monotonic()-started, deadline, status, code)
        try:
            with self.opener.open(req, timeout=deadline) as response:
                result = json.load(response)
        except urllib.error.HTTPError as e:
            status = e.code
            try:
                with e:
                    result = json.load(e)
            except (ValueError, OSError, http.client.HTTPException):
                raise failure('authentication' if status in (401, 403) else 'http_error') from None
        except (OSError, urllib.error.URLError) as e:
            reason = e.reason if isinstance(e, urllib.error.URLError) else e
            kind = 'timeout' if isinstance(reason, (TimeoutError, socket.timeout)) else 'connection_refused' if isinstance(reason, ConnectionRefusedError) else 'connection_error'
            raise failure(kind) from None
        except http.client.HTTPException:
            raise failure('protocol_error') from None
        except (ValueError, UnicodeError):
            raise failure('invalid_json') from None
        if status in (401, 403):
            raise failure('authentication')
        if not isinstance(result, dict) or 'error' not in result or 'result' not in result:
            raise failure('invalid_response')
        if result['error'] is not None:
            error = result['error']
            raise failure('rpc_error', error.get('code') if isinstance(error, dict) else None)
        if status is not None:
            raise failure('http_error')
        if 'id' in result and result['id'] != 'btc-miner':
            raise failure('invalid_response')
        return result['result']

    def check(self):
        info = self.call("getblockchaininfo")
        if info["chain"] != CHAIN[self.c["network"]]:
            raise ValueError(f"Network mismatch: node is {info['chain']}, configured {self.c['network']}")
        if info.get("initialblockdownload"):
            raise ValueError("Bitcoin Core is still syncing")
        if info.get("blocks",0) < info.get("headers",0):
            raise ValueError("Bitcoin Core is still catching up with its known headers")
        if self.c["network"] != "regtest":
            network = self.call("getnetworkinfo")
            if not network.get("networkactive") or network.get("connections",0) < 1:
                raise ValueError("Bitcoin Core needs an active peer connection before mining")
        return info
