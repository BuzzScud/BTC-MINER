"""Exercise public setup and OS boundaries without controlling an existing miner."""
import json
import os
from pathlib import Path
import socket
import subprocess
import sys
import tempfile
import threading
import unittest
from unittest.mock import patch, Mock

from btcminer import control_transport, onboarding, platform_support as platform, settings, service
from btcminer.native import Hasher
from btcminer.diagnostics import self_test


class PortabilityTests(unittest.TestCase):
    def test_built_native_backend_agrees_with_reference(self):
        result=self_test(dict(settings.DEFAULTS),require_native=True)
        self.assertTrue(result['ok'],result)

    def test_public_math_profile_matches_original_active_traversal(self):
        self.assertEqual({k:settings.DEFAULTS[k] for k in ('strategy','thesis2_order','thesis2_step','thesis2_prime')},
            dict(strategy='thesis2',thesis2_order='flower',thesis2_step=7,thesis2_prime=19))
        self.assertEqual(settings.DEFAULTS['provider_user'],'')
        self.assertEqual(settings.DEFAULTS['address'],'')

    def test_exclusive_lock_contends_across_processes_and_releases_on_close(self):
        with tempfile.TemporaryDirectory() as folder:
            path=Path(folder)/'lock'
            command=[sys.executable,'-c',
                "from btcminer.platform_support import fcntl; import sys; f=open(sys.argv[1],'a+'); "
                "fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB)",str(path)]
            with path.open('a+') as handle:
                platform.fcntl.flock(handle,platform.fcntl.LOCK_EX|platform.fcntl.LOCK_NB)
                result=subprocess.run(command,capture_output=True)
                self.assertNotEqual(result.returncode,0)
                self.assertIn(b'BlockingIOError',result.stderr)
            self.assertEqual(subprocess.run(command,capture_output=True).returncode,0)

    def test_real_control_transport_round_trip(self):
        with tempfile.TemporaryDirectory() as folder:
            address=Path(folder)/'control.sock'
            server,token=control_transport.listen(address)
            errors=[]
            def respond():
                try:
                    conn,_=server.accept()
                    with conn:
                        command=json.loads(conn.recv(4096));control_transport.authorize(command,token)
                        conn.sendall(b'{"ok":true}\n')
                except BaseException as error:errors.append(error)
            thread=threading.Thread(target=respond);thread.start()
            try:self.assertEqual(service._request(address,'status',{}),{'ok':True})
            finally:thread.join(4);server.close();address.unlink(missing_ok=True)
            self.assertFalse(errors,errors);self.assertFalse(thread.is_alive())

    def test_control_rejects_missing_or_wrong_credential(self):
        for value in ({}, {'_auth':'wrong'}, {'_auth':False}):
            with self.assertRaises(ValueError):control_transport.authorize(value,'a'*64)
        value={'_auth':'a'*64,'command':'status'}
        control_transport.authorize(value,'a'*64)
        self.assertNotIn('_auth',value)

    def test_pipe_read_is_bounded_and_preserves_bytes(self):
        process=subprocess.Popen([sys.executable,'-u','-c',
            "import sys,time; sys.stdout.buffer.write(b'hello\\n'); sys.stdout.flush(); time.sleep(3)"],stdout=subprocess.PIPE)
        try:
            self.assertEqual(platform.pipe_read(process.stdout,6,2),b'hello\n')
            with self.assertRaises(TimeoutError):platform.pipe_read(process.stdout,1,.03)
        finally:process.terminate();process.wait();process.stdout.close()

    def test_os_sampler_returns_owned_memory_and_cpu_interval(self):
        from btcminer.resources import HostSampler
        sampler=HostSampler();first=sampler.sample();second=sampler.sample()
        self.assertGreater(first['owned_rss_mib'],0)
        self.assertIn(str(os.getpid()),first['process_rss_mib'])
        # A same-tick second sample can be unavailable, never fabricated.
        if second['host_cpu_percent'] is not None:self.assertTrue(0<=second['host_cpu_percent']<=100)

    def test_input_retry_and_cancellation_do_not_start_mining(self):
        with patch('builtins.input',side_effect=['bad','pool']):
            self.assertEqual(onboarding.ask('Mode','core',onboarding.choice(('core','pool'))),'pool')
        with patch.object(sys.stdin,'isatty',return_value=True),patch.object(service,'status',return_value={'running':True}),patch.object(onboarding,'save') as save:
            with self.assertRaisesRegex(ValueError,'Stop this installation'):onboarding.wizard()
            save.assert_not_called()

    def test_wizard_cancel_and_pool_save_are_explicit_and_local(self):
        values=['pool','mainnet','stratum+ssl://pool.example:3333','fixture.worker','','1','n']
        for answer in ('n','y'):
            inputs=values+[answer]+(['n'] if answer=='y' else [])
            with patch.object(sys.stdin,'isatty',return_value=True),patch.object(service,'status',return_value={}),\
                 patch.object(onboarding,'load',return_value=dict(settings.DEFAULTS)),\
                 patch('builtins.input',side_effect=inputs),patch('getpass.getpass',return_value=''),\
                 patch.object(onboarding,'save') as save,patch.object(service,'start') as start:
                onboarding.wizard()
                self.assertEqual(save.call_count,int(answer=='y'));start.assert_not_called()

    def test_atomic_local_settings_survive_replacement(self):
        with tempfile.TemporaryDirectory() as folder:
            path=Path(folder)/'machine.local.json'
            settings.atomic_json(path,{'value':1});settings.atomic_json(path,{'value':2})
            self.assertEqual(json.loads(path.read_text()),{'value':2})
            if os.name!='nt':self.assertEqual(path.stat().st_mode & 0o777,0o600)

    def test_default_core_directory_matches_os(self):
        path=platform.bitcoin_directory()
        if sys.platform=='win32':self.assertEqual(path.name,'Bitcoin')
        elif sys.platform=='darwin':self.assertEqual(path.parts[-3:],('Library','Application Support','Bitcoin'))
        else:self.assertEqual(path.name,'.bitcoin')

if __name__=='__main__':unittest.main()
