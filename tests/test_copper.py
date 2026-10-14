"""Fixture tests for Copper: split input, real sample scope, lifecycle isolation."""
import json
import tempfile
import threading
import time
import unittest
from pathlib import Path
from unittest.mock import Mock, patch
from btcminer.settings import DEFAULTS
from btcminer.tui import App, plain
from btcminer.ui_support import Keys, Observations, Painter


class InputTests(unittest.TestCase):
    def test_arrows_and_unicode_survive_fragmented_reads(self):
        keys = Keys()
        self.assertEqual(keys.feed(b'\x1b', 1), [])
        self.assertEqual(keys.feed(b'[', 1.01), [])
        self.assertEqual(keys.feed(b'A', 1.02), ['\x1b[A'])
        encoded = '矿'.encode()
        self.assertEqual(keys.feed(encoded[:1], 2), [])
        self.assertEqual(keys.feed(encoded[1:], 2.01), ['矿'])
        self.assertEqual(keys.feed(b'\x1b', 3), [])
        self.assertEqual(keys.feed(now=3.06), ['\x1b'])

    def test_paste_is_text_not_start_stop_or_enter(self):
        keys = Keys()
        result = keys.feed(b'\x1b[200~st/stop\n\x1b[201~q',1)
        self.assertEqual(result, [('paste',c) for c in 'st/stop\n']+['q'])


class ObservationTests(unittest.TestCase):
    def setUp(self):
        self.folder = tempfile.TemporaryDirectory(); self.addCleanup(self.folder.cleanup)
        self.path = Path(self.folder.name)/'model-events.jsonl'
        self.reader = Observations(self.folder.name)
        self.status = dict(running=True, model_telemetry=dict(session_id='current'))

    def row(self, **overrides):
        return dict(kind='batch',session_id='current',timestamp=time.time(),
                    job_id='a'*64,round_id='42',attempted='16384',height=100,
                    samples=[dict(nonce=4294967295,hash='0'*64)],**overrides)

    def test_never_mixes_sessions_or_uses_incomplete_suffix(self):
        old = self.row(); old['session_id']='old'
        self.path.write_text(json.dumps(old)+'\n'+json.dumps(self.row()))
        self.assertIsNone(self.reader.read(self.status))
        with self.path.open('a') as f: f.write('\n')
        sample = self.reader.read(self.status)
        self.assertEqual(sample['nonce'],4294967295)
        self.assertEqual(sample['hash'],'0'*64)
        self.assertEqual(sample['attempted'],16384)
        self.assertIsNone(self.reader.read(dict(running=False)))

    def test_rotation_missing_file_and_malformed_records(self):
        self.path.write_text(json.dumps(self.row())+'\n')
        self.assertIsNotNone(self.reader.read(self.status))
        self.path.rename(self.path.with_suffix('.old'))
        self.path.write_text('{bad}\n'+json.dumps(dict(kind='batch',session_id='current'))+'\n')
        self.assertIsNone(self.reader.read(self.status))
        self.path.unlink()
        self.assertIsNone(self.reader.read(self.status))


class CopperTests(unittest.TestCase):
    def test_provider_runtime_status_and_stopped_start_notice(self):
        self.app.c['provider_enabled'] = True
        self.app.s['provider'] = {'enabled': True, 'state': 'online', 'stream': 'connected', 'math_check': 'matched'}
        screen = plain(self.app.frame(160, 45))
        self.assertIn('API online', screen)
        self.assertIn('job math matched', screen)
        self.app.s.update(running=False, state='STOPPED')
        self.assertIn('API enabled', plain(self.app.frame(160, 45)))

    def setUp(self):
        self.folder = tempfile.TemporaryDirectory(); self.addCleanup(self.folder.cleanup)
        for target,value in [('LOGS',Path(self.folder.name)),('CONFIG',Path(self.folder.name)/'none'),
                             ('load',lambda:dict(DEFAULTS))]:
            p=patch('btcminer.tui.'+target,value);p.start();self.addCleanup(p.stop)
        self.app=App()
        self.app.s=dict(state='MINING',running=True,connected=True,hashes=9007199254740993,
                        rates={'10':10200000},workers=6,height=100)
        self.app.sample=dict(job='a'*64,round='42',nonce=4294967295,hash='f'*64,
                             timestamp=time.time(),height=100,attempted=16384)
        self.app.observed_at=time.time()

    def test_freeze_keeps_snapshot_but_never_miner_controls(self):
        self.app.execute=Mock()
        self.app.input('f')
        self.app.s['hashes']=123
        self.app.sample['nonce']=12
        screen=plain(self.app.frame(130,40))
        self.assertIn('DISPLAY FROZEN',screen)
        self.assertIn('9,007,199,254,740,993',screen)
        self.assertIn('4,294,967,295',screen)
        self.app.execute.assert_not_called()
        self.app.input('t')
        self.app.execute.assert_called_once_with(['stop'])
        self.app.input('f')
        self.assertIsNone(self.app.frozen)
        self.assertNotIn('9,007,199,254,740,993',plain(self.app.frame(130,40)))

    def test_stale_and_disabled_telemetry_are_explicit(self):
        self.app.observed_at=time.time()-30
        screen=plain(self.app.frame(130,40))
        self.assertIn('STALE',screen)
        self.assertIn('Status stale',screen)
        self.app.s['model_telemetry']={'enabled':False}
        self.assertIn('Sampling disabled',plain(self.app.frame(130,40)))

    def test_hub_is_case_insensitive_and_does_not_use_miner_command_queue(self):
        self.app.busy=True;self.app.execute=Mock();self.app.open_hub=Mock()
        self.app.command('/HUB')
        self.app.open_hub.assert_called_once_with([])
        self.app.execute.assert_not_called()

    def test_changed_rows_only_and_resize_clear(self):
        painter=Painter();frame=self.app.frame(130,40)
        self.assertIn('\x1b[2J',painter.render(frame,(130,40)))
        self.assertEqual(painter.render(frame,(130,40)),'')
        self.app.buf='/hub'
        changed=painter.render(self.app.frame(130,40),(130,40))
        self.assertNotIn('\x1b[2J',changed)
        self.assertIn('/hub',changed)
        self.assertIn('\x1b[2J',painter.render(self.app.frame(80,24),(80,24)))

    def test_main_thread_applies_background_snapshot(self):
        self.app.latest=(dict(state='PAUSED',running=True,hashes=100),dict(DEFAULTS),None,time.time())
        self.assertEqual(self.app.s['state'],'MINING')
        self.app.drain_updates()
        self.assertEqual(self.app.s['state'],'PAUSED')

    def test_stop_interrupts_diagnostic_before_stopping_miner(self):
        started=threading.Event();finished=threading.Event();calls=[]
        def launch(args,**kwargs):
            command=args[-1];calls.append(command)
            proc=Mock(returncode=0)
            def communicate():
                if command=='doctor':
                    started.set();finished.wait(2)
                return '{}',None
            proc.communicate=communicate;proc.terminate=finished.set
            return proc
        with patch('btcminer.tui.subprocess.Popen',side_effect=launch):
            self.app.execute(['doctor']);self.assertTrue(started.wait(1))
            self.app.input('t');self.assertTrue(finished.is_set())
            deadline=time.monotonic()+2
            while (self.app.busy or len(calls)<2) and time.monotonic()<deadline:
                self.app.drain_updates();time.sleep(.01)
        self.assertEqual(calls,['doctor','stop'])


if __name__=='__main__':
    unittest.main()
