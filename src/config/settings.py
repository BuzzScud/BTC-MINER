"""Validated local configuration; contains public payout details, never wallet keys."""
import json
import os
import platform
import tempfile
from pathlib import Path
from . import ROOT
from .difficulty import MAX_MULTIPLIER

CONFIG = ROOT / "machine.local.json"
LOGS = ROOT / "logs"
DEFAULTS = {
    "connection": "core", "network": "mainnet", "strategy": "thesis2",
    "workers": 2, "partition": "quadrant", "batch_size": 16384,
    "cpu_duty": 100, "pause_on_active": 120, "yield_cpu": True,
    "worker": "btc-m2-8gb", "address": "",
    "rpc_host": "127.0.0.1", "rpc_port": 0, "rpc_datadir": "",
    "rpc_cookie": "", "rpc_user": "", "rpc_password_env": "BTC_RPC_PASSWORD",
    "rpc_timeout": 15, "template_refresh": 15,
    "pool": "", "backup": "", "pool_user": "", "pool_password": "x",
    "pool_password_env": "BTC_POOL_PASSWORD", "tls": True,
    "pool_difficulty": 0, "connect_timeout": 10, "retry_seconds": 5,
    "retries_before_backup": 5, "primary_retry_seconds": 120,
    "single_nonce_only": False, "phase3_nonces": 65536,
    "entropy_min": 0.18, "entropy_max": 0.45,
    "native_hasher": True, "native_nonce": False, "native_candidates": False,
    "recovery": False, "round_restart_seconds": 600,
    "supt_log": True, "supt_sample_every": 64, "nonce_log": True,
    # Optional observational journal; bounded queue and four background replay
    # hashes per completed batch. It never grants candidate exclusion authority.
    "observatory_telemetry": True,
    "provider_enabled": False, "provider_user": "",
    "stop_after_block": False, "keep_awake": True,
    "max_rounds": 0, "run_seconds": 0,
    "thesis2_step": 7, "thesis2_prime": 19, "thesis2_order": "flower",
    "regtest_difficulty_multiplier": 1,
    "pruning_enabled": True, "pruning_budget_ms": 1000, "pruning_candidates": 8,
    "distribution_enabled": True, "distribution_port": 0,
    "distribution_host": "127.0.0.1", "distribution_auth": "",
    "distribution_cert": "", "distribution_key": "",
    "distribution_lease_seconds": 15, "distribution_pruning_ms": 1000,
    # Opt-in until the user-authorized private qualification is complete.
    "resource_control": False, "resource_min_workers": min(2, os.cpu_count() or 1), "resource_max_workers": min(6, os.cpu_count() or 1),
    "resource_cpu_target": 85, "resource_cpu_backoff": 90,
    "resource_rss_mib": 4096, "resource_peer_rss_mib": 256,
    "resource_swap_growth_mib": 128, "resource_external_workers": 0,
    "provider_metrics_path": "", "provider_metrics_ws_path": "",
}
ALIASES = {"threads": "workers", "mode": "strategy", "wallet": "address",
           "pause": "pause_on_active", "yield": "yield_cpu"}
CHOICES = {"connection": ("core", "pool"), "network": ("mainnet", "testnet4", "testnet", "regtest"),
           "strategy": ("thesis2", "thesis", "linear", "hybrid"), "partition": ("quadrant", "chunk", "ordered"),
           "thesis2_order": ("field", "flower")}
BOUNDS = {"workers": (1, os.cpu_count() or 8), "batch_size": (64, 1000000),
          "cpu_duty": (1, 100), "pause_on_active": (0, 3600), "rpc_port": (0, 65535),
          "rpc_timeout": (1, 120), "template_refresh": (2, 300), "pool_difficulty": (0, 1e18),
          "connect_timeout": (1, 120), "retry_seconds": (1, 300),
          "retries_before_backup": (1, 100), "primary_retry_seconds": (30, 3600),
          "phase3_nonces": (0, 1 << 32), "entropy_min": (0, 1), "entropy_max": (0, 1),
          "round_restart_seconds": (0, 86400), "supt_sample_every": (1, 10000000),
          "max_rounds": (0,100000000), "run_seconds": (0,31536000),
          "thesis2_step": (1,359), "thesis2_prime": (7,24001),
          "regtest_difficulty_multiplier": (1, MAX_MULTIPLIER),
          "pruning_budget_ms": (1, 2000), "pruning_candidates": (1, 64),
          "distribution_port": (0,65535), "distribution_lease_seconds": (2,300),
          "distribution_pruning_ms": (0,2000),
          "resource_min_workers": (1,os.cpu_count() or 8),
          "resource_max_workers": (1,os.cpu_count() or 8),
          "resource_external_workers": (0,(os.cpu_count() or 8)-1),
          "resource_cpu_target": (1,99), "resource_cpu_backoff": (2,100),
          "resource_rss_mib": (64,65536), "resource_peer_rss_mib": (16,65536),
          "resource_swap_growth_mib": (1,4096)}

def atomic_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(prefix=".write-", dir=path.parent)
    try:
        with os.fdopen(fd, "w") as f:
            json.dump(value, f, indent=2, allow_nan=False)
            f.write("\n")
        if os.name == "nt" and (path.suffix == ".sock" or path.name in ("machine.local.json", "network-profiles.local.json")):
            from .platform_support import private_file
            private_file(tmp)
        os.replace(tmp, path)
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)

def validate(config):
    if set(config) - set(DEFAULTS):
        raise ValueError("Unknown settings: " + ", ".join(sorted(set(config) - set(DEFAULTS))))
    out = dict(DEFAULTS, **config)
    for key, default in DEFAULTS.items():
        value = out[key]
        if isinstance(default, bool):
            if not isinstance(value, bool):
                raise ValueError(f"{key} must be true or false")
        elif isinstance(default, (int, float)):
            if isinstance(value, bool) or not isinstance(value, (int, float)):
                raise ValueError(f"{key} must be numeric")
            if key != "pool_difficulty" and isinstance(default, int) and int(value) != value:
                raise ValueError(f"{key} must be an integer")
            if key in BOUNDS and not BOUNDS[key][0] <= value <= BOUNDS[key][1]:
                raise ValueError(f"{key} must be between {BOUNDS[key][0]} and {BOUNDS[key][1]}")
            out[key] = float(value) if isinstance(default, float) or key == "pool_difficulty" else int(value)
        elif not isinstance(value, str) or any(ord(c) < 32 for c in value):
            raise ValueError(f"{key} must be plain text")
        if key in CHOICES and value not in CHOICES[key]:
            raise ValueError(f"{key}: choose {', '.join(CHOICES[key])}")
    if out["entropy_min"] > out["entropy_max"]:
        raise ValueError("entropy_min cannot exceed entropy_max")
    if out['resource_min_workers'] > out['resource_max_workers']:
        raise ValueError('resource_min_workers cannot exceed resource_max_workers')
    if out['resource_external_workers'] >= out['resource_max_workers']:
        raise ValueError('Resource budget must retain at least one coordinator worker')
    if out['resource_cpu_target'] >= out['resource_cpu_backoff']:
        raise ValueError('resource_cpu_target must be below resource_cpu_backoff')
    if out['resource_peer_rss_mib'] > out['resource_rss_mib']:
        raise ValueError('Peer memory ceiling cannot exceed the total ceiling')
    path=out['provider_metrics_path']
    if path and (not path.startswith('/api/') or '?' in path or '#' in path or '..' in path):
        raise ValueError('provider_metrics_path must be an origin-relative /api/ path')
    path=out['provider_metrics_ws_path']
    if path and (not path.startswith('/ws/') or '?' in path or '#' in path or '..' in path):
        raise ValueError('provider_metrics_ws_path must be an origin-relative /ws/ path')
    from math import gcd
    from .thesis2 import qualifying_primes
    if gcd(out["thesis2_step"],360) != 1:
        raise ValueError("thesis2_step must be coprime to 360 (for example 7)")
    if out["thesis2_prime"] not in qualifying_primes():
        raise ValueError("thesis2_prime must be a prime p >= 7 with (p-1) dividing 144000")
    if not out["worker"] or any(c not in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789._-" for c in out["worker"]):
        raise ValueError("worker: use letters, numbers, dots, underscores or hyphens")
    if "://" in out["rpc_host"] or "/" in out["rpc_host"] or "@" in out["rpc_host"]:
        raise ValueError("rpc_host must be a hostname or IP, without a URL or credentials")
    return out

def load():
    if CONFIG.exists():
        with CONFIG.open() as f:
            return validate(json.load(f))
    return validate({})

def save(config):
    config = validate(config)
    atomic_json(CONFIG, config)
    return config

def changes(config, assignments):
    updated = dict(config)
    for assignment in assignments:
        key, sep, value = assignment.partition("=")
        key = ALIASES.get(key.lower(), key.lower())
        if not sep or key not in DEFAULTS:
            raise ValueError(f"Expected a known KEY=value: {assignment}")
        default = DEFAULTS[key]
        if isinstance(default, bool):
            if value.lower() not in ("on", "off", "true", "false", "1", "0", "yes", "no"):
                raise ValueError(f"{key}: use on/off")
            value = value.lower() in ("on", "true", "1", "yes")
        elif isinstance(default, float) or key == "pool_difficulty":
            value = float(value)
        elif isinstance(default, int):
            value = int(value)
        updated[key] = value
    return validate(updated)

def public(config):
    return {k: ("••••" if k == "pool_password" and v not in ("", "x") else v) for k, v in config.items()}

def apply_math_environment(c, logs=None):
    logs = LOGS if logs is None else Path(logs)
    mappings = {"BTC_USE_C_NONCE": c["native_nonce"], "BTC_USE_C_CANDIDATES": c["native_candidates"],
                "BTC_DISABLE_RECOVERY": not c["recovery"], "BTC_SUPT_LOG": c["supt_log"],
                "BTC_DISABLE_NONCE_LOG": not c["nonce_log"]}
    for key, value in mappings.items():
        os.environ[key] = str(int(value))
    os.environ["BTC_ENTROPY_CUT_MIN"] = str(c["entropy_min"])
    os.environ["BTC_ENTROPY_CUT_MAX"] = str(c["entropy_max"])
    os.environ["BTC_SUPT_SAMPLE_EVERY"] = str(c["supt_sample_every"])
    os.environ["BTC_SUPT_DATA_DIR"] = str(logs / "math")
    os.environ["BTC_NONCE_LOG_PATH"] = str(logs / "nonces.jsonl")
