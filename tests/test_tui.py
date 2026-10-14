import json
import tempfile
import threading
import time
import unittest
from pathlib import Path
from unittest.mock import Mock, patch

from btcminer.tui import App, plain
from btcminer.settings import DEFAULTS
from test_protocol import ADDRESS


class TerminalTests(unittest.TestCase):
    def setUp(self):
        self.folder = tempfile.TemporaryDirectory()
        self.addCleanup(self.folder.cleanup)
        for target,value in (("btcminer.tui.LOGS",Path(self.folder.name)),
                             ("btcminer.tui.CONFIG",Path(self.folder.name)/"config.json"),
                             ("btcminer.tui.load",lambda:dict(DEFAULTS,address=ADDRESS))):
            patcher = patch(target,value); patcher.start(); self.addCleanup(patcher.stop)
        self.app = App()

    def test_s_starts_and_t_stops(self):
        self.app.execute = Mock()
        self.app.input("s")
        self.app.execute.assert_called_with(["start"])
        self.app.perf_target = 4
        self.app.input("t")
        self.app.execute.assert_called_with(["stop"])
        self.assertIsNone(self.app.perf_target)

    def test_stop_interrupts_provider_observation(self):
        self.app.busy = True
        self.app.active_args = ['provider', 'watch', '--seconds', '60']
        self.app.process = Mock()
        self.app.input('t')
        self.app.process.terminate.assert_called_once_with()
        self.assertTrue(self.app.pending_stop)

    def test_s_opens_setup_if_connection_is_incomplete(self):
        self.app.c["address"] = ""
        self.app.execute = Mock()
        self.app.input("s")
        self.assertIsNotNone(self.app.setup_draft)
        self.app.execute.assert_not_called()

    def test_typing_settings_does_not_trigger_start_stop_shortcuts(self):
        self.app.execute = Mock()
        self.app.setup_begin()
        self.app.input("s"); self.app.input("t")
        self.assertEqual(self.app.buf,"st")
        self.app.execute.assert_not_called()

    def test_stop_waits_for_busy_command_then_executes(self):
        started = threading.Event(); finish = threading.Event(); stopped = threading.Event()
        calls = []
        def launch(args, **kwargs):
            command = args[-1]; calls.append(command)
            proc = Mock(returncode=0)
            def communicate():
                if command == "start":
                    started.set(); finish.wait(3)
                else:
                    stopped.set()
                return json.dumps({"message":command+" done"}), None
            proc.communicate = communicate
            return proc
        with patch("btcminer.tui.subprocess.Popen",side_effect=launch):
            self.app.input("s")
            self.assertTrue(started.wait(2))
            self.app.input("t")
            self.assertTrue(self.app.pending_stop)
            finish.set()
            deadline = time.monotonic()+3
            while not stopped.is_set() and time.monotonic()<deadline:
                self.app.drain_updates()
                time.sleep(.01)
            self.assertTrue(stopped.is_set())
            while self.app.busy and time.monotonic()<deadline:
                self.app.drain_updates()
                time.sleep(.01)
        self.assertEqual(calls,["start","stop"])

    def test_dashboard_shows_stop_control_while_running(self):
        self.app.s = {"state":"MINING","running":True}
        self.assertIn("t to stop",plain(self.app.frame(110,36)))

    def test_q_closes_view_without_sending_stop(self):
        self.app.execute = Mock()
        self.app.input("q")
        self.assertFalse(self.app.alive)
        self.app.execute.assert_not_called()

    def test_network_command_routes_selection_and_cancels_pending_worker_change(self):
        self.app.execute = Mock()
        self.app.perf_target = 4
        self.app.command("/network mainnet")
        self.app.execute.assert_called_once_with(["network", "mainnet"], "/network")
        self.assertIsNone(self.app.perf_target)

    def test_selected_network_is_visible_in_footer_and_help(self):
        self.app.c["network"] = "testnet4"
        self.assertIn("/network testnet4", plain(self.app.frame(120,36)))
        self.app.command("/help")
        self.assertTrue(any("/network mainnet|testnet4" in line for line in self.app.overlay[1]))

    def test_network_menu_opens_from_typed_command_and_selects_mainnet(self):
        self.app.c['network'] = 'testnet4'
        self.app.execute = Mock()
        for key in '/network\r':
            self.app.input(key)
        self.app.execute.assert_not_called()
        screen = plain(self.app.frame(120,36))
        self.assertIn('Mainnet · real Bitcoin', screen)
        self.assertIn('Testnet4 · test Bitcoin', screen)
        self.app.input('\x1b[A')
        self.app.input('\r')
        self.app.execute.assert_called_once_with(['network','mainnet','--check'], 'Select and test mainnet')
        self.assertIsNone(self.app.network_choice)

    def test_network_menu_cancels_and_does_not_start_mining(self):
        self.app.execute = Mock()
        self.app.command('/network')
        self.app.input('s')
        self.app.input('\x1b')
        self.app.execute.assert_not_called()
        self.assertIsNone(self.app.network_choice)
        self.app.command('/network')
        self.app.input('1')
        self.app.input('\r')
        self.app.execute.assert_called_once_with(['network','mainnet','--check'], 'Select and test mainnet')
