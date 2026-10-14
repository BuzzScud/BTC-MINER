"""Mining-loop UI tests use temporary preferences and mocked miner controls."""
import json
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import Mock, patch
from btcminer.settings import DEFAULTS
from btcminer.tui import App, plain, cell_width
from btcminer import loop_view


class LoopTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        self.logs = Path(tmp.name)
        for key,value in [('load',lambda:dict(DEFAULTS)),('LOGS',self.logs),('CONFIG',self.logs/'missing')]:
            ctx=patch('btcminer.tui.'+key,value);ctx.start();self.addCleanup(ctx.stop)
        self.app=App(); self.app.execute=Mock(); self.app.command('loop')

    def test_plain_command_enters_and_escape_returns_without_service_actions(self):
        a=self.app;a.command('dashboard')
        for key in 'loop\r':a.input(key)
        self.assertTrue(a.loop_mode)
        a.input('\x1b');self.assertFalse(a.loop_mode)
        a.execute.assert_not_called()

    def test_clockwise_layout_and_exact_large_counters(self):
        a=self.app;a.s=dict(state='MINING',running=True,hashes=2**53+1,shares_accepted=12,shares_rejected=3,shares_unknown=2,blocks_accepted=1)
        a.observed_at=time.time()
        screen=plain(a.frame(140,40))
        for item in ['01 Get job','02 Prepare candidates','03 Hash nonces','04 Submit result','9,007,199,254,740,993','12 shares accepted','3 solutions rejected','2 unknown outcomes','1 Core blocks accepted','──→','←──','↑','↓']:
            self.assertIn(item,screen)
        self.assertLess(screen.index('04 Submit'),screen.index('03 Hash'))

    def test_editor_keys_and_paste_never_dispatch_controls(self):
        a=self.app;a.input('e');a.input('\r');a.input('\x15')
        a.paste('stqp/stop\n\x03')
        self.assertTrue(a.alive);a.execute.assert_not_called()
        self.assertEqual(a.loop_editor['text'],'stqp/stop')
        a.input('\x1b');a.input('\x1b')
        self.assertIsNone(a.loop_editor);self.assertTrue(a.loop_mode)
        self.assertFalse((self.logs/'loop-view.json').exists())

    def test_labels_persist_without_restarting_and_bad_file_falls_back(self):
        a=self.app;a.input('e');a.input('\r');a.input('\x15');a.paste('Receive work');a.input('\r');a.input('\x13')
        self.assertEqual(App().loop_labels[0],'Receive work');a.execute.assert_not_called()
        (self.logs/'loop-view.json').write_text('{"labels": [1,2,3,4]}')
        self.assertEqual(App().loop_labels,loop_view.LABELS)

    def test_invalid_setting_remains_draft_and_valid_change_dispatches(self):
        a=self.app;a.input('3');a.input('e');a.input('\x1b[B');a.input('\r');a.input('\x15');a.paste('0');a.input('\r');a.input('\x13')
        self.assertIn('workers',a.loop_editor['error']);a.execute.assert_not_called()
        a.input('\r');a.input('\x15');a.paste('1');a.input('\r');a.input('\x13')
        a.execute.assert_called_once_with(['config','set','workers=1'],'Apply loop settings')
        self.assertIsNone(a.loop_editor)

    def test_running_config_requires_valid_start_and_does_not_start_during_test(self):
        a=self.app;a.s['running']=True;a.input('3');a.input('e');a.loop_editor['values']['workers']='1'
        with patch('btcminer.service.validate_start',side_effect=ValueError('Missing payout address')) as validate:
            a.input('\x13');validate.assert_called_once()
        self.assertIn('Missing payout',a.loop_editor['error']);a.execute.assert_not_called()
        with patch('btcminer.service.validate_start'):
            a.input('\x13')
        a.execute.assert_called_once()

    def test_busy_save_preserves_draft(self):
        a=self.app;a.input('e');a.busy=True;a.input('\x13')
        self.assertIn('running',a.loop_editor['error']);a.execute.assert_not_called()

    def test_real_controls_and_freeze_keep_live_lifecycle(self):
        a=self.app;a.s=dict(state='MINING',running=True);a.observed_at=time.time()
        a.input('f');a.s.update(state='PAUSED',paused_reason='manual')
        self.assertIn('PAUSED',plain(a.frame(100,24)))
        self.assertIn('FROZEN',plain(a.frame(100,24)))
        a.input('p');a.execute.assert_called_with(['resume'])
        a.input('t');a.execute.assert_called_with(['stop'])
        a.input('q');self.assertFalse(a.alive)

    def test_stale_and_disabled_samples_are_honest(self):
        a=self.app;a.s=dict(state='MINING',running=True,height=10);a.observed_at=time.time()-20
        a.sample=dict(timestamp=time.time()-40,nonce=123456789,hash='a'*64,job='b'*64,height=9,attempted=64)
        screen=plain(a.frame(140,40));self.assertIn('STALE',screen);self.assertIn('previous height',screen);self.assertIn('Job awaiting sample',screen)
        a.s['model_telemetry']={'enabled':False}
        screen=plain(a.frame(140,40));self.assertIn('sampling disabled',screen);self.assertNotIn('123,456,789',screen)

    def test_resize_all_modes_and_password_masking(self):
        a=self.app;a.loop_labels[0]='測試 e\u0301 '*8
        for mode in ['loop','editor','field','report','setup','command']:
            a.loop_editor=None;a.overlay=None;a.setup_draft=None;a.buf=None
            if mode in ('editor','field'):
                loop_view.begin_edit(a)
                if mode=='field':a.input('\r')
            elif mode=='report':a.overlay=('Report',['abc'*100]*80)
            elif mode=='setup':
                a.setup_draft=dict(a.c);a.setup_fields=[('pool_password','Password','sensitive-default')];a.buf='sensitive-input'
            elif mode=='command':a.buf='/loop'
            for cols,rows in [(1,1),(15,5),(40,8),(60,18),(76,24),(80,24),(100,24),(110,36),(140,45)]:
                with self.subTest(mode=mode,size=(cols,rows)):
                    lines=plain(a.frame(cols,rows)).split('\r\n')
                    self.assertEqual(len(lines),rows)
                    self.assertTrue(all(cell_width(line)<=cols-1 for line in lines))
                    self.assertNotIn('sensitive-input','\n'.join(lines))
                    self.assertNotIn('sensitive-default','\n'.join(lines))

    def test_config_failures_are_visible(self):
        a=self.app;a.busy=True
        a.complete_command(['config','set','workers=1'],'Apply loop settings','{"message":"Cannot save settings"}',1)
        self.assertIn('Cannot save settings',plain(a.frame(100,24)))
        self.assertFalse(a.busy)

    def test_overlay_escape_returns_to_loop_before_dashboard(self):
        a=self.app;a.command('help');a.input('\x1b')
        self.assertIsNone(a.overlay);self.assertTrue(a.loop_mode)
        a.input('\x1b');self.assertFalse(a.loop_mode)
