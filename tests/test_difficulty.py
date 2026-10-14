import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch

from btcminer import difficulty, settings
from btcminer.protocol import Work, target_from_bits


class TargetTests(unittest.TestCase):
    def setUp(self):
        target = target_from_bits("207fffff")
        self.work = Work(bytes(range(80)), target, target, 123, "207fffff", "job", 1, {"body": b"transactions"})

    def test_stricter_target_preserves_consensus_header_and_body(self):
        c = dict(settings.DEFAULTS, network="regtest", regtest_difficulty_multiplier=256)
        work = difficulty.apply_target(c, self.work)
        self.assertEqual(work.target, self.work.network_target // 256)
        for field in ("network_target", "header", "bits", "height", "key", "generation", "data"):
            self.assertEqual(getattr(work, field), getattr(self.work, field))
        self.assertEqual(self.work.target, self.work.network_target)
        self.assertIs(difficulty.apply_target(dict(c, regtest_difficulty_multiplier=1), self.work), self.work)

    def test_public_networks_and_pool_ignore_saved_multiplier(self):
        for network in ("mainnet", "testnet4", "testnet", "regtest"):
            for connection in ("core", "pool"):
                c = dict(settings.DEFAULTS, network=network, connection=connection, regtest_difficulty_multiplier=256)
                if network == "regtest" and connection == "core":
                    continue
                with self.subTest(network=network, connection=connection):
                    self.assertIs(difficulty.apply_target(c, self.work), self.work)
                    self.assertEqual(difficulty.active_multiplier(c), 1)

    def test_core_connection_uses_stricter_target(self):
        from btcminer.connections import CoreConnection
        c = dict(settings.DEFAULTS, network="regtest", regtest_difficulty_multiplier=32)
        connection = CoreConnection(c, Mock())
        connection.connected = True
        connection.template = {"fixture": True}
        with patch("btcminer.connections.core_work", return_value=self.work):
            self.assertEqual(connection.work().target, self.work.target // 32)
        connection.connected = False
        self.assertIsNone(connection.work())

    def test_default_and_multiplier_validation(self):
        self.assertEqual(settings.validate({})[difficulty.KEY], 1)
        for value in (0, -1, True, 1.5, "2", difficulty.MAX_MULTIPLIER + 1):
            with self.subTest(value=value), self.assertRaises(ValueError):
                settings.validate({difficulty.KEY: value})
        self.assertEqual(settings.validate({difficulty.KEY: difficulty.MAX_MULTIPLIER})[difficulty.KEY], difficulty.MAX_MULTIPLIER)

    def test_large_multiplier_is_exact_and_preserves_consensus(self):
        for multiplier in ((1 << 32) + 1, 100_000_000_000, difficulty.MAX_MULTIPLIER):
            with self.subTest(multiplier=multiplier):
                c = settings.validate(dict(settings.DEFAULTS, network='regtest',
                                           regtest_difficulty_multiplier=multiplier))
                c = settings.validate(json.loads(json.dumps(c)))
                work = difficulty.apply_target(c, self.work)
                self.assertEqual(work.target, self.work.network_target // multiplier)
                self.assertEqual(work.header, self.work.header)
                self.assertEqual(work.network_target, self.work.network_target)
                self.assertGreater(work.target, 0)
                self.assertEqual(difficulty.active_multiplier(dict(c, network='mainnet')), 1)


class DifficultyControlTests(unittest.TestCase):
    def setUp(self):
        folder = tempfile.TemporaryDirectory()
        self.addCleanup(folder.cleanup)
        self.root = Path(folder.name)
        for target, value in (("btcminer.settings.CONFIG", self.root / "config.json"),
                              ("btcminer.service.LOGS", self.root / "logs")):
            p = patch(target, value); p.start(); self.addCleanup(p.stop)
        settings.save(dict(settings.DEFAULTS, network="regtest"))
        self.mocks = {}
        for name, result in (("status", {"running": False}), ("supervisor_running", False),
                             ("validate_start", None), ("_stop", {"ok": True}), ("_start", {"ok": True})):
            p = patch("btcminer.service." + name, return_value=result)
            self.mocks[name] = p.start(); self.addCleanup(p.stop)

    def test_stopped_up_down_numeric_reset_never_starts(self):
        for value, expected in (("up", 2), ("up", 4), ("down", 2), ("9", 9), ("down", 4),
                                ("100000000000", 100_000_000_000), ("up", 200_000_000_000), ("reset", 1)):
            result = difficulty.change(value)
            self.assertEqual(result["multiplier"], expected)
            self.assertEqual(settings.load()[difficulty.KEY], expected)
            self.assertFalse(result["mining_restarted"])
        self.mocks["_start"].assert_not_called()
        self.mocks["_stop"].assert_not_called()

    def test_show_and_bounds_are_noops_even_when_running(self):
        self.mocks["status"].return_value = {"running": True}
        before = settings.CONFIG.read_bytes()
        self.assertEqual(difficulty.change()["multiplier"], 1)
        for value in ("down", "reset", "1"):
            self.assertFalse(difficulty.change(value)["changed"])
        self.assertEqual(settings.CONFIG.read_bytes(), before)
        settings.save(dict(settings.load(), regtest_difficulty_multiplier=difficulty.MAX_MULTIPLIER))
        self.assertFalse(difficulty.change("up")["changed"])
        self.mocks["_start"].assert_not_called()
        self.mocks["_stop"].assert_not_called()

    def test_running_change_stops_before_saving_then_restarts_once(self):
        self.mocks["status"].return_value = {"running": True}
        self.mocks["_stop"].side_effect = lambda **_: self.assertEqual(settings.load()[difficulty.KEY], 1)
        self.mocks["_start"].side_effect = lambda: self.assertEqual(settings.load()[difficulty.KEY], 2)
        result = difficulty.change("up")
        self.assertTrue(result["mining_restarted"])
        self.mocks["_stop"].assert_called_once_with(summary=False)
        self.mocks["_start"].assert_called_once_with()

    def test_supervisor_between_attempts_is_stopped_and_restarted(self):
        self.mocks["supervisor_running"].return_value = True
        self.assertTrue(difficulty.change("up")["mining_restarted"])
        self.mocks["_stop"].assert_called_once()
        self.mocks["_start"].assert_called_once()

    def test_validation_or_stop_failure_preserves_saved_setting(self):
        self.mocks["status"].return_value = {"running": True}
        for name in ("validate_start", "_stop"):
            with self.subTest(failure=name):
                self.mocks[name].side_effect = RuntimeError("test failure")
                with self.assertRaisesRegex(RuntimeError, "test failure"):
                    difficulty.change("up")
                self.assertEqual(settings.load()[difficulty.KEY], 1)
                self.mocks["_start"].assert_not_called()
                self.mocks[name].side_effect = None

    def test_save_or_start_failure_is_not_reported_as_success(self):
        self.mocks["status"].return_value = {"running": True}
        with patch("btcminer.settings.save", side_effect=OSError("disk full")):
            with self.assertRaisesRegex(OSError, "disk full"):
                difficulty.change("up")
        self.mocks["_start"].assert_not_called()
        self.mocks["_start"].side_effect = RuntimeError("cannot start")
        with self.assertRaisesRegex(RuntimeError, "cannot start"):
            difficulty.change("up")
        self.assertEqual(settings.load()[difficulty.KEY], 2)

    def test_invalid_controls_and_non_regtest_mutations_preserve_config(self):
        before = settings.CONFIG.read_bytes()
        for value in ("0", "-1", "1.5", "nan", "invalid", str(difficulty.MAX_MULTIPLIER + 1)):
            with self.subTest(value=value), self.assertRaises(ValueError):
                difficulty.change(value)
            self.assertEqual(settings.CONFIG.read_bytes(), before)
        for network, connection in (("mainnet", "core"), ("testnet4", "core"), ("testnet", "core"), ("regtest", "pool")):
            settings.save(dict(settings.DEFAULTS, network=network, connection=connection, regtest_difficulty_multiplier=32))
            before = settings.CONFIG.read_bytes()
            self.assertFalse(difficulty.change()["available"])
            for value in ("up", "down", "reset", "2"):
                with self.assertRaisesRegex(ValueError, "require Bitcoin Core on regtest"):
                    difficulty.change(value)
            self.assertEqual(settings.CONFIG.read_bytes(), before)
        self.mocks["_stop"].assert_not_called()
        self.mocks["_start"].assert_not_called()

    def test_public_cli_dispatch(self):
        from btcminer.cli import main
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            self.assertEqual(main(["difficulty", "up"]), 0)
        self.assertEqual(json.loads(output.getvalue())["multiplier"], 2)
