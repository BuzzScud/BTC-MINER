import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from btcminer import networks, settings
from btcminer.rpc import RPC


class NetworkTests(unittest.TestCase):
    def setUp(self):
        folder = tempfile.TemporaryDirectory()
        self.addCleanup(folder.cleanup)
        self.root = Path(folder.name)
        for target, value in (("btcminer.settings.CONFIG", self.root/"config.json"),
                              ("btcminer.networks.PROFILES", self.root/"profiles.json"),
                              ("btcminer.service.LOGS", self.root/"logs")):
            p = patch(target, value); p.start(); self.addCleanup(p.stop)
        self.original = dict(settings.DEFAULTS, network="testnet4", workers=1,
                             address="testnet-payout", rpc_host="127.0.0.1",
                             rpc_port=48332, rpc_datadir="/custom/testnet4",
                             rpc_cookie="/custom/testnet4/.cookie", rpc_user="test-user")
        settings.save(self.original)
        p = patch("btcminer.service._stop", return_value={"ok":True})
        self.stop = p.start(); self.addCleanup(p.stop)
        for name in ("start", "restart", "_start"):
            p = patch("btcminer.service."+name, side_effect=AssertionError("Must never start mining"))
            p.start(); self.addCleanup(p.stop)

    def test_round_trip_restores_network_connection_but_keeps_worker_setting(self):
        result = networks.select("mainnet")
        current = settings.load()
        self.assertEqual(current["network"], "mainnet")
        self.assertEqual(RPC(current).url, "http://127.0.0.1:8332/")
        for key in ("address", "rpc_cookie", "rpc_user", "rpc_datadir", "pool"):
            self.assertEqual(current[key], "")
        self.assertFalse(result["mining_started"])
        self.assertEqual(self.stop.call_count, 1)
        settings.save(dict(current, address="mainnet-payout", rpc_port=8333, workers=2))
        networks.select("testnet4")
        restored = settings.load()
        for key in networks.FIELDS:
            self.assertEqual(restored[key], self.original[key])
        self.assertEqual(restored["workers"], 2)
        networks.select("mainnet")
        self.assertEqual(settings.load()["address"], "mainnet-payout")
        self.assertEqual(settings.load()["rpc_port"], 8333)

    def test_show_and_same_network_preserve_state_without_stopping(self):
        self.assertEqual(networks.select()["network"], "testnet4")
        networks.select("testnet4")
        self.stop.assert_not_called()
        self.assertEqual(settings.load(), self.original)
        self.assertFalse(networks.PROFILES.exists())

    def test_stop_failure_does_not_save_network_or_profiles(self):
        self.stop.side_effect = RuntimeError("Still draining")
        with self.assertRaisesRegex(RuntimeError, "Still draining"):
            networks.select("mainnet")
        self.assertEqual(settings.load(), self.original)
        self.assertFalse(networks.PROFILES.exists())

    def test_invalid_network_or_profile_does_not_modify_configuration(self):
        with self.assertRaises(ValueError):
            networks.select("unknown")
        for value in ([], {"mainnet":{"workers":8}}, {"mainnet":{"rpc_port":-1}},
                      {"unknown":{}}, {"mainnet":{"rpc_host":"https://host"}}):
            with self.subTest(value=value):
                networks.PROFILES.write_text(json.dumps(value))
                with self.assertRaises(ValueError):
                    networks.select("mainnet")
                self.assertEqual(settings.load(), self.original)
        self.stop.assert_not_called()

    def test_pool_settings_do_not_cross_into_an_unconfigured_network(self):
        pool = dict(self.original, connection="pool", pool="stratum+tcp://test.example:3333",
                    pool_user="test-worker", pool_password="private-test-password")
        settings.save(pool)
        result = networks.select("mainnet")
        self.assertEqual(settings.load()["connection"], "core")
        self.assertEqual(settings.load()["pool_user"], "")
        self.assertNotIn("private-test-password", json.dumps(result))
        networks.select("testnet4")
        self.assertEqual(settings.load()["pool"], pool["pool"])
        self.assertEqual(settings.load()["pool_password"], pool["pool_password"])

    def test_testnet3_and_testnet4_use_separate_profiles_and_ports(self):
        networks.select("testnet")
        self.assertEqual(RPC(settings.load()).url, "http://127.0.0.1:18332/")
        networks.select("regtest")
        self.assertEqual(RPC(settings.load()).url, "http://127.0.0.1:18443/")
        networks.select("testnet4")
        self.assertEqual(RPC(settings.load()).url, "http://127.0.0.1:48332/")
