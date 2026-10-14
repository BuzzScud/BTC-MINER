"""Network selection with local connection profiles; selecting never starts work."""
import json
from . import service
from .rpc import PORTS, CHAIN, RPC
from .settings import ROOT, CHOICES, DEFAULTS, atomic_json, load, save, validate

PROFILES = ROOT / "network-profiles.local.json"
FIELDS = ("connection", "address", "rpc_host", "rpc_port", "rpc_datadir",
          "rpc_cookie", "rpc_user", "rpc_password_env", "rpc_tls", "pool", "backup",
          "pool_user", "pool_password", "pool_password_env", "tls")


def read_profiles():
    if not PROFILES.exists():
        return {}
    profiles = json.loads(PROFILES.read_text())
    if not isinstance(profiles, dict):
        raise ValueError("Network profiles must be an object")
    for name, profile in profiles.items():
        if (name not in CHOICES["network"] or not isinstance(profile, dict)
                or set(profile) - set(FIELDS)):
            raise ValueError("Invalid saved network profile; settings were not changed")
        validate(dict(DEFAULTS, **dict(profile, network=name)))
    return profiles


def describe(config):
    return {"network":config["network"], "connection":config["connection"],
            "rpc_host":config["rpc_host"],
            "rpc_port":config["rpc_port"] or PORTS[config["network"]],
            "payout_address_set":bool(config["address"]),
            "options":list(CHOICES["network"]),
            "note":"testnet4 is the current test network; testnet selects legacy testnet3. "
                   "Switching stops mining. Review /config and /doctor --connect before s."}


def select(name=None):
    if name is None:
        return describe(load())
    if name not in CHOICES["network"]:
        raise ValueError("Choose " + ", ".join(CHOICES["network"]))
    # Share the start/stop lock so another start cannot race the save.
    with service.lifecycle_lock():
        current = load()
        if name == current["network"]:
            return {**describe(current), "message":f"Already using {name}; no settings changed."}
        profiles = read_profiles()
        profiles[current["network"]] = {key:current[key] for key in FIELDS}
        target = {key:DEFAULTS[key] for key in FIELDS}
        target.update(profiles.get(name, {}))
        selected = validate(dict(current, **dict(target, network=name)))
        # A failed stop aborts the switch before either file is changed.
        service._stop(summary=False)
        atomic_json(PROFILES, profiles)
        save(selected)
        return {**describe(selected), "mining_started":False,
                "message":f"Network changed to {name}. Mining is stopped. "
                          "Review /config and run /doctor --connect before s."}


def check_connection(config):
    """Read-only RPC handshake, chain identity, sync and peer checks; no mining."""
    result = {"ok":False, "connected":False, "network_match":False,
              "node_ready":False, "network":config["network"], "mining_started":False}
    if config["connection"] != "core":
        return dict(result, message="Pool profile selected. This check requires a Bitcoin Core connection; use /setup to configure Core.")
    rpc = RPC(config)
    result['rpc'] = rpc.url
    try:
        info = rpc.call('getblockchaininfo')
        result.update(connected=True, chain=info['chain'], blocks=info.get('blocks'),
                      headers=info.get('headers'), verification_progress=info.get('verificationprogress'))
        if info['chain'] != CHAIN[config['network']]:
            result['message'] = f"Network mismatch: selected {config['network']}, node reports {info['chain']}. Check /setup."
            return result
        result['network_match'] = True
        network = rpc.call('getnetworkinfo')
        syncing = bool(info.get('initialblockdownload') or info.get('blocks',0) < info.get('headers',0))
        peers = network.get('connections',0)
        ready = not syncing and (config['network']=='regtest' or (network.get('networkactive') and peers>0))
        result.update(ok=True, node_ready=bool(ready), syncing=syncing, peers=peers,
                      payout_address_set=bool(config['address']))
        status = 'Node is still syncing.' if syncing else ('Node is ready.' if ready else 'Node needs active peers.')
        result['message'] = f"Connected to {config['network']} Bitcoin Core. {status} " + (
            "Use /doctor --connect to check mining readiness." if config['address'] else "Set your payout address in /setup before mining.")
    except (OSError, ValueError, RuntimeError) as error:
        result['message'] = 'Connection check failed: ' + str(error)
    return result
