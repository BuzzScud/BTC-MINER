"""Presentation checks use fixtures only: no miner service or local configuration."""
from collections import deque
from pathlib import Path
import tempfile
import time
import unicodedata
import unittest
from unittest.mock import Mock, patch

from btcminer.settings import DEFAULTS
from btcminer.tui import App, ACCENT, COMMANDS, RESET, clipped, plain


def columns(text):
    return sum(0 if unicodedata.combining(c) else
               2 if unicodedata.east_asian_width(c) in ("W", "F") else 1
               for c in text)


class EmberLayoutTests(unittest.TestCase):
    def setUp(self):
        folder = tempfile.TemporaryDirectory()
        self.addCleanup(folder.cleanup)
        for name, value in (("LOGS", Path(folder.name)),
                            ("CONFIG", Path(folder.name)/"missing.json"),
                            ("load", lambda: dict(DEFAULTS, network="testnet4"))):
            context = patch("btcminer.tui."+name, value)
            context.start(); self.addCleanup(context.stop)
        self.app = App()
        self.app.s = dict(state="MINING", running=True, rates={"10":4820000,"60":4760000,"900":4610000},
                          shares_accepted=12, shares_rejected=3, shares_unknown=2, blocks_accepted=1,
                          candidate_count=2048, hashes=4970000000, elapsed=1112,
                          hasher="native ARM SHA-256", endpoint="127.0.0.1:48332", height=102481)
        self.app.spark = deque([1,2,4,2,3,4,5], maxlen=26)
        self.app.mem = "mem 3.1 GB available / 8 GB"
        self.app.messages = deque([("14:02:00","start","Started · THESIS2 · 2 workers"),
                                   ("14:02:01","connection","Bitcoin Core connected")])

    def screen(self, cols=110, rows=36):
        return plain(self.app.frame(cols, rows))

    def test_frame_stays_inside_terminal_for_states_panels_and_resize(self):
        self.app.c["worker"] = "矿工 e\u0301 "*35
        self.app.s["endpoint"] = "节点.example/"*50
        self.app.note("Long event " + "測試 "*100, "error")
        for state in ("STOPPED", "STARTING", "CONNECTING", "MINING", "PAUSED"):
            self.app.s.update(state=state, running=state!="STOPPED",
                              paused_reason="keyboard / mouse active · resume after 120s idle" if state=="PAUSED" else "")
            for panel in ("events", "palette", "report", "setup"):
                self.app.buf = "/" if panel=="palette" else None
                self.app.overlay = ("Report", ["測試 "*100]*100) if panel=="report" else None
                self.app.setup_draft = dict(self.app.c) if panel=="setup" else None
                self.app.setup_fields = [("pool_password","Pool password","sensitive-default")]
                if panel=="setup": self.app.buf="sensitive-input"
                for cols,rows in ((1,1),(15,5),(40,8),(60,18),(80,24),(99,36),(100,24),(110,36),(140,45)):
                    with self.subTest(state=state,panel=panel,size=(cols,rows)):
                        lines=self.screen(cols,rows).split("\r\n")
                        self.assertEqual(len(lines),rows)
                        self.assertTrue(all(columns(line)<=cols-1 for line in lines))
                        self.assertNotIn("sensitive-default", "\n".join(lines))
                        self.assertNotIn("sensitive-input", "\n".join(lines))

    def test_wide_dashboard_preserves_real_rates_and_distinct_outcomes(self):
        frame=self.screen()
        for value in ("4.8 MH/s","4.6 MH/s","12 accepted shares","3 rejected solutions",
                      "2 unknown outcomes","1 accepted Core blocks","native ARM SHA-256",
                      "SESSION HASHES","4,970,000,000","height 102481","3.1 GB available / 8 GB",
                      "testnet4","t to stop","/network testnet4","q / Ctrl+C"):
            self.assertIn(value,frame)
        self.assertIn("SESSION", frame)
        self.assertIn("ENGINE / STRATEGY", frame)
        self.assertIn("│", frame)

    def test_compact_dashboard_keeps_results_and_controls_without_rail(self):
        frame=self.screen(80,24)
        self.assertNotIn("│ │",frame)
        self.assertIn('MINING LOOP',frame)
        for value in ("12 accepted shares","3 rejected solutions","2 unknown outcomes",
                      "1 accepted Core blocks","testnet4","t stop","s start","Type / for commands"):
            self.assertIn(value,frame)

    def test_stopped_session_does_not_display_old_rates_as_live(self):
        self.app.s.update(state="STOPPED",running=False)
        frame=self.screen()
        self.assertIn("RESULTS · LAST SESSION",frame)
        self.assertIn("12 accepted shares",frame)
        self.assertIn("last session 0h 18m 32s",frame)
        self.assertIn("0.0 H/s",frame)
        self.assertNotIn("4.8 MH/s",frame)
        self.assertNotIn("▁▃▆▃▄▆█",frame)

    def test_compact_stopped_results_are_labeled_as_last_session(self):
        self.app.s.update(state="STOPPED",running=False)
        frame=self.screen(80,24)
        self.assertIn("Last session: 12 accepted shares",frame)
        self.assertIn("3 rejected solutions",frame)
        self.assertIn("2 unknown outcomes",frame)
        self.assertNotIn("4.8 MH/s",frame)

    def test_queued_stop_and_pause_reason_are_both_visible(self):
        self.app.s.update(state="PAUSED",paused_reason="keyboard / mouse active · resume after 120s idle")
        self.app.pending_stop=True
        for cols,rows in ((80,24),(100,24),(110,36),(140,45)):
            with self.subTest(size=(cols,rows)):
                frame=self.screen(cols,rows)
                self.assertIn("Stop queued",frame)
                self.assertIn("resume after 120s idle",frame)
                self.assertIn("Type / for commands",frame)

    def test_existing_strategy_details_are_not_replaced_with_thesis2(self):
        for strategy in ("thesis2","thesis","linear","hybrid"):
            self.app.c["strategy"]=strategy
            for connection in ("core","pool"):
                self.app.c["connection"]=connection
                with self.subTest(strategy=strategy,connection=connection):
                    frame=self.screen()
                    if strategy=="thesis2":
                        self.assertIn("32-bit nonce traversal",frame)
                        self.assertIn("step 7 · prime 19",frame)
                    else:
                        self.assertIn(strategy+" · quadrant",frame)
                        self.assertIn("2,048 candidates",frame)
                        self.assertIn("entropy 0.18–0.45",frame)
                        self.assertNotIn("19² − 1",frame)

    def test_report_scroll_and_palette_selection_keep_session_rail(self):
        self.app.overlay=("Math report",[f"report-line-{i:03}" for i in range(100)])
        self.app.scroll=45
        frame=self.screen()
        self.assertIn("report-line-045",frame)
        self.assertNotIn("report-line-044",frame)
        self.assertIn("12 accepted shares",frame)
        self.app.buf="/"; self.app.palette=len(COMMANDS)-1
        frame=self.screen(100,24)
        self.assertIn("› /quit",frame)
        self.assertIn("12 accepted shares",frame)

    def test_pending_stop_pause_and_worker_feedback_remain_visible(self):
        self.app.s.update(state="PAUSED",paused_reason="keyboard / mouse active · resume after 120s idle")
        self.assertIn("resume after 120s idle",self.screen())
        self.app.pending_stop=True
        self.assertIn("Stop queued",self.screen())
        self.app.perf_target=4; self.app.perf_deadline=time.monotonic()+1.5
        self.assertIn("workers 2 → 4",self.screen())

    def test_setup_masks_both_input_and_saved_password(self):
        self.app.setup_draft=dict(self.app.c)
        self.app.setup_fields=[("pool_password","Pool password","secret-default")]
        self.app.buf="secret-input"
        frame=self.screen()
        self.assertIn("Pool password",frame)
        self.assertIn("••••",frame)
        self.assertNotIn("secret-default",frame)
        self.assertNotIn("secret-input",frame)

    def test_palette_key_behavior_and_rendering_have_no_command_side_effects(self):
        self.app.execute=Mock()
        self.app.buf="/workers"
        self.screen(); self.screen(80,24)
        self.app.execute.assert_not_called()
        # Preserve existing Tab behavior rather than introducing a new interaction.
        self.app.input("\t")
        self.app.execute.assert_called_once_with(["perf"],"/workers")

    def test_sparse_startup_status_renders(self):
        self.app.s={"state":"STOPPED"}
        self.app.messages.clear()
        frame=self.screen()
        for value in ("s to start","0 accepted shares","0 unknown outcomes","Type / for commands"):
            self.assertIn(value,frame)

    def test_regtest_difficulty_display_and_command_routing(self):
        self.app.c.update(network="regtest", regtest_difficulty_multiplier=8)
        self.app.s["regtest_difficulty_multiplier"] = 4
        for cols,rows in ((40,8),(60,18),(80,24),(100,24),(110,36),(140,45)):
            with self.subTest(size=(cols,rows)):
                frame = self.screen(cols,rows)
                if rows>=18:
                    self.assertIn("Test difficulty ×4", frame)
                self.assertEqual(len(frame.split("\r\n")), rows)
                self.assertTrue(all(columns(line)<=cols-1 for line in frame.split("\r\n")))
        self.app.s["running"] = False
        self.assertIn("Test difficulty ×8", self.screen())
        self.app.c["connection"] = "pool"
        self.assertNotIn("Test difficulty", self.screen())
        self.app.execute = Mock()
        self.app.command("/difficulty down")
        self.app.execute.assert_called_once_with(["difficulty", "down"], "/difficulty")

    def test_clipping_preserves_cells_and_ends_style_before_padding(self):
        self.assertEqual(plain(clipped(ACCENT+"矿工",3)),"矿…")
        self.assertEqual(plain(clipped(ACCENT+"矿工",4)),"矿工")
        self.assertEqual(plain(clipped(ACCENT+"e\u0301test",2)),"e\u0301…")
        self.assertEqual(clipped(ACCENT+"x",3),ACCENT+"x"+RESET+"  ")
        self.assertEqual(clipped("abc",0),"")

    def test_apple_terminal_uses_only_supported_foreground_colors(self):
        import re
        for cols, rows in ((120,68),(80,24),(147,58)):
            frame=self.app.frame(cols,rows)
            self.assertTrue(frame.startswith(RESET))
            self.assertNotIn('\x1b[38;2;',frame)
            self.assertNotIn('\x1b[48;',frame)
            for code in re.findall(r'\x1b\[([0-9;]+)m',frame):
                self.assertRegex(code,r'^(0|1|38;5;[0-9]{1,3})$')
            lines=plain(frame).split('\r\n')
            self.assertEqual(len(lines),rows)
            self.assertTrue(all(columns(line)<=cols-1 for line in lines))
