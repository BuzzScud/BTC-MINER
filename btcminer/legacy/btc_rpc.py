"""
Bitcoin Core JSON-RPC client.
getblocktemplate, submitblock, getblockchaininfo; auth via user/pass.
"""
import json
import socket
import urllib.request
import urllib.error
from typing import Any, Optional

from config import MinerConfig


class BitcoinRPCError(Exception):
    """RPC returned an error."""

    def __init__(self, code: int, message: str) -> None:
        self.code = code
        self.message = message
        super().__init__(f"RPC error {code}: {message}")


def _rpc_call(config: MinerConfig, method: str, params: Optional[list] = None) -> Any:
    payload = {"jsonrpc": "1.0", "id": "miner", "method": method}
    if params is not None:
        payload["params"] = params

    data = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(
        config.rpc_url,
        data=data,
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    auth = config.auth_tuple()
    if auth:
        import base64

        creds = base64.b64encode(f"{auth[0]}:{auth[1]}".encode()).decode()
        req.add_header("Authorization", f"Basic {creds}")

    try:
        with urllib.request.urlopen(req, timeout=config.rpc_timeout) as resp:
            out = json.loads(resp.read().decode())
    except urllib.error.HTTPError as e:
        body = e.read().decode() if e.fp else ""
        if e.code == 503:
            raise BitcoinRPCError(
                503,
                "Work queue depth exceeded. Add rpcworkqueue=32 to bitcoin.conf and restart Bitcoin Core.",
            )
        try:
            err = json.loads(body)
            err_obj = err.get("error")
            if err_obj:
                raise BitcoinRPCError(
                    err_obj.get("code", -1), err_obj.get("message", body)
                )
        except (ValueError, TypeError):
            pass
        raise BitcoinRPCError(-1, f"HTTP {e.code}: {body[:200]}")
    except urllib.error.URLError as e:
        reason = str(e.reason)
        if "Connection refused" in reason or "Errno 61" in reason:
            raise BitcoinRPCError(
                -1,
                "Connection refused. Is Bitcoin Core running? Start Bitcoin-Qt or bitcoind. Mainnet uses port 8332; ensure server=1 (and rpcallowip if needed) in bitcoin.conf.",
            )
        raise BitcoinRPCError(-1, reason)
    except socket.timeout:
        raise BitcoinRPCError(-1, "RPC request timed out. Bitcoin Core may be busy or unresponsive.")
    except BrokenPipeError:
        raise BitcoinRPCError(-1, "Broken pipe writing to Bitcoin Core RPC. Connection was reset.")
    except ConnectionResetError:
        raise BitcoinRPCError(-1, "Connection reset by Bitcoin Core. Node may be restarting or overloaded.")
    except OSError as e:
        raise BitcoinRPCError(-1, f"OS-level network error: {e}")

    if "error" in out and out["error"] is not None:
        err = out["error"]
        raise BitcoinRPCError(err.get("code", -1), err.get("message", "unknown"))
    return out.get("result")


def getblocktemplate(config: MinerConfig, capabilities: Optional[list] = None) -> Any:
    """Fetch block template. capabilities e.g. ['segwit']."""
    params: list[Any] = [{}]
    if capabilities:
        params[0]["rules"] = capabilities
    return _rpc_call(config, "getblocktemplate", params)


def submitblock(config: MinerConfig, hex_block: str) -> Any:
    """Submit mined block (hex)."""
    return _rpc_call(config, "submitblock", [hex_block])


def getblockchaininfo(config: MinerConfig) -> Any:
    """Get chain info (height, chain name, etc.)."""
    return _rpc_call(config, "getblockchaininfo")


def getblockhash(config: MinerConfig, height: int) -> str:
    """Get block hash at given chain height. Returns hex hash string."""
    return _rpc_call(config, "getblockhash", [height])


def getblock(config: MinerConfig, block_hash: str, verbosity: int = 1) -> Any:
    """Get block by hash. verbosity=1 returns JSON with height, bits, nonce, etc."""
    return _rpc_call(config, "getblock", [block_hash, verbosity])


def getnetworkinfo(config: MinerConfig) -> Any:
    """Get network info (connections, version, etc.)."""
    return _rpc_call(config, "getnetworkinfo")


def getmempoolinfo(config: MinerConfig) -> Any:
    """Get mempool aggregate info (size, bytes, total_fee, mempoolminfee, loaded, etc.)."""
    return _rpc_call(config, "getmempoolinfo")


def getrawmempool(config: MinerConfig, verbose: bool = True) -> Any:
    """Get raw mempool; when verbose=True, returns dict of txid -> { fee, vsize, time, ... }."""
    return _rpc_call(config, "getrawmempool", [verbose])
