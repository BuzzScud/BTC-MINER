"""Hub launcher is local, single-instance, and never invokes miner lifecycle."""
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import Mock,patch
from btcminer import hub


class HubTests(unittest.TestCase):
    def setUp(self):
        self.folder=tempfile.TemporaryDirectory();self.addCleanup(self.folder.cleanup)
        self.root=Path(self.folder.name).resolve()
        for name in ('observatory_server.py','index.html'):
            (self.root/name).write_text('fixture')
        p=patch('btcminer.hub.LOGS',self.root/'logs');p.start();self.addCleanup(p.stop)

    def test_path_with_spaces_and_missing_install(self):
        self.assertEqual(hub.locate(str(self.root)),self.root)
        with self.assertRaisesRegex(ValueError,'Observatory not found'):
            hub.locate(self.root/'missing')

    def test_existing_server_reused_without_spawn(self):
        with patch.object(hub,'health',side_effect=lambda port,folder: {} if port is None else {'pid':42}),patch.object(hub.subprocess,'Popen') as spawn:
            port,started=hub.ensure_server(self.root)
        self.assertEqual(port,63218);self.assertFalse(started);spawn.assert_not_called()

    def test_no_open_launch_and_browser_failure_return_usable_url(self):
        with patch.object(hub,'ensure_server',return_value=(63219,True)),patch.object(hub.subprocess,'run',side_effect=OSError) as opener:
            result=hub.launch(self.root,False)
            opener.assert_not_called()
            self.assertEqual(result['url'],'http://127.0.0.1:63219/#live-miner-study')
            result=hub.launch(self.root,True)
            self.assertTrue(result['ok']);self.assertFalse(result['browser_opened'])

    def test_wrong_root_or_fixture_server_cannot_be_reused(self):
        response=Mock()
        good=dict(service='btc-observatory',miner_root=str(hub.ROOT.resolve()),
                  observatory_root=str(self.root),start_fixture=False)
        response.__enter__=Mock(return_value=response);response.__exit__=Mock()
        opener=Mock();opener.open.return_value=response
        with patch.object(hub.urllib.request,'build_opener',return_value=opener):
            response.read.return_value=json.dumps(good).encode()
            self.assertEqual(hub.health(63218,self.root),good)
            for field,value in [('miner_root','wrong'),('service','other'),('start_fixture',True)]:
                response.read.return_value=json.dumps(dict(good,**{field:value})).encode()
                self.assertIsNone(hub.health(63218,self.root))

    def test_start_detaches_output_and_disables_fixture(self):
        process=Mock(pid=111);process.poll.return_value=None
        probe=Mock();probe.getsockname.return_value=('127.0.0.1',63218)
        probe.__enter__=Mock(return_value=probe);probe.__exit__=Mock()
        with patch.object(hub,'health',side_effect=[None,None,{'pid':111}]),patch.object(hub.socket,'socket',return_value=probe),patch.object(hub.subprocess,'Popen',return_value=process) as spawn:
            self.assertEqual(hub.ensure_server(self.root),(63218,True))
        args,kwargs=spawn.call_args
        self.assertIn('--no-fixture',args[0])
        self.assertTrue(kwargs['start_new_session'])
        self.assertNotEqual(kwargs['stdout'],hub.subprocess.PIPE)
        self.assertEqual(kwargs['env']['BTC_MINER_ROOT'],str(hub.ROOT.resolve()))
        self.assertTrue((self.root/'logs/hub.json').is_file())


if __name__=='__main__':unittest.main()
