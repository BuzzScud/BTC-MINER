"""Optional stricter proof-of-work target for private Core regtest sessions."""
from dataclasses import replace

KEY = "regtest_difficulty_multiplier"
# Keep every allowed value exact in JSON consumers. The target division itself
# uses Python integers; a 32-bit nonce does not limit the difficulty multiplier.
MAX_MULTIPLIER = (1 << 53) - 1


def available(config):
    return config["network"] == "regtest" and config["connection"] == "core"


def active_multiplier(config):
    return config.get(KEY, 1) if available(config) else 1


def apply_target(config, work):
    multiplier = active_multiplier(config)
    if multiplier == 1:
        return work
    # A stricter local acceptance threshold, never a change to consensus nBits.
    return replace(work, target=min(work.target, work.network_target // multiplier))


def describe(config):
    return {"available": available(config), "network": config["network"],
            "connection": config["connection"], "multiplier": active_multiplier(config),
            "saved_multiplier": config.get(KEY, 1), "minimum": 1,
            "maximum": MAX_MULTIPLIER, "options": "up / down / reset / N",
            "message": "Local regtest work multiplier; higher means fewer solutions, not a faster hashrate."
            if available(config) else "Difficulty controls require Bitcoin Core on regtest; public and pool targets are unchanged."}


def change(value=None):
    from . import service, settings
    if value is None:
        return describe(settings.load())
    with service.lifecycle_lock():
        config = settings.load()
        if not available(config):
            raise ValueError("Difficulty controls require Bitcoin Core on regtest. Use /network regtest and configure its Core connection first.")
        current = config.get(KEY, 1)
        value = str(value).lower()
        if value == "up":
            multiplier = min(MAX_MULTIPLIER, current * 2)
        elif value == "down":
            multiplier = max(1, current // 2)
        elif value == "reset":
            multiplier = 1
        else:
            try:
                multiplier = int(value)
            except ValueError:
                raise ValueError("Difficulty: use up, down, reset, or an integer multiplier") from None
        updated = settings.validate(dict(config, **{KEY: multiplier}))
        if multiplier == current:
            return {**describe(config), "changed": False, "mining_restarted": False,
                    "message": f"Test difficulty is already ×{current:,}; no restart needed."}
        running = service.status().get("running", False) or service.supervisor_running()
        if running:
            service.validate_start(updated)
            # Save only after the previous engine has stopped successfully.
            service._stop(summary=False)
        settings.save(updated)
        if running:
            service._start()
        return {**describe(updated), "changed": True, "mining_restarted": bool(running),
                "message": f"Test difficulty ×{multiplier:,}. " +
                ("Miner restarted; session counters reset." if running else "Saved; applies on next start.")}
