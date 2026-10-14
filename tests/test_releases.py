"""Real disposable Git remotes; no GitHub writes, live miners, or package installs."""
from contextlib import nullcontext
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import Mock, patch

from btcminer import releases, runtime, service


def git(root, *args):
    return subprocess.check_output(['git','-C',str(root),*args],stderr=subprocess.PIPE,text=True).strip()


def manifest(root):
    names=['.gitignore','README.md','requirements.txt','PUBLIC_FILES.json']
    (root/'PUBLIC_FILES.json').write_text(json.dumps(names))
    (root/'FILES.sha256.json').write_text(json.dumps({n:hashlib.sha256((root/n).read_bytes()).hexdigest() for n in names}))


class ReleaseTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory(prefix='btc release fixture ')
        self.addCleanup(self.temp.cleanup)
        self.base=Path(self.temp.name)
        self.origin=self.base/'remote.git';self.origin.mkdir()
        git(self.origin,'init','--bare')
        self.owner=self.base/'owner';self.owner.mkdir()
        git(self.owner,'init','-b','main')
        git(self.owner,'config','user.name','Fixture')
        git(self.owner,'config','user.email','fixture@localhost')
        git(self.owner,'config','core.autocrlf','false')
        (self.owner/'.gitignore').write_text('.updates/\n*.local.json\n.env\n.cookie\nlogs/\nnative/*.so\n')
        (self.owner/'README.md').write_text('first release\n')
        (self.owner/'requirements.txt').write_text('')
        manifest(self.owner)
        git(self.owner,'add','.')
        git(self.owner,'commit','-m','first')
        git(self.owner,'remote','add','origin',str(self.origin))
        git(self.owner,'push','origin','HEAD:main','HEAD:stable')
        self.before=git(self.owner,'rev-parse','HEAD')
        self.root=self.base/'follower'
        git(self.base,'clone','-b','main',str(self.origin),str(self.root))
        git(self.root,'config','core.autocrlf','false')
        self.repo=releases.Repository(self.root,upstream=str(self.origin))
        self.stop=self.enter_patch(patch.object(service,'_stop',return_value={'ok':True}))
        self.enter_patch(patch.object(service,'lifecycle_lock',side_effect=nullcontext))
        self.run=self.enter_patch(patch.object(self.repo,'run'))
        self.valid=self.enter_patch(patch.object(self.repo,'validate',side_effect=self.validate))
        (self.root/'native').mkdir()
        for name in ('hasher_fast','abacus','rodsieve'):
            (self.root/'native'/('lib'+name+'.so')).write_bytes(b'old native')
        (self.root/'machine.local.json').write_text('{"fixture":"local-only"}')
        (self.root/'.env').write_text('LOCAL_FIXTURE=retained\n')
        (self.root/'logs').mkdir();(self.root/'logs/session.txt').write_text('retained')

    def enter_patch(self, context):
        result=context.start();self.addCleanup(context.stop);return result

    def validate(self, stage, **kwargs):
        (stage/'native').mkdir(exist_ok=True)
        for name in ('hasher_fast','abacus','rodsieve'):
            (stage/'native'/('lib'+name+'.so')).write_bytes(b'new native')
        return sys.executable,None

    def publish(self):
        (self.owner/'README.md').write_text('second release\n');manifest(self.owner)
        git(self.owner,'add','.');git(self.owner,'commit','-m','second')
        git(self.owner,'push','origin','HEAD:main','HEAD:stable')
        return git(self.owner,'rev-parse','HEAD')

    def test_real_fetch_switch_and_private_data_preservation(self):
        target=self.publish()
        self.assertTrue(self.repo.update())
        self.assertEqual(git(self.root,'rev-parse','HEAD'),target)
        self.assertEqual(git(self.root,'branch','--show-current'),'stable')
        self.assertEqual(git(self.root,'rev-parse','--abbrev-ref','@{upstream}'),'origin/stable')
        self.assertEqual((self.root/'machine.local.json').read_text(),'{"fixture":"local-only"}')
        self.assertEqual((self.root/'.env').read_text(),'LOCAL_FIXTURE=retained\n')
        self.assertEqual((self.root/'logs/session.txt').read_text(),'retained')
        self.assertEqual((self.root/'native/libabacus.so').read_bytes(),b'new native')
        self.assertEqual(self.stop.call_count,1)
        self.assertFalse(self.repo.transaction.exists())
        self.assertEqual(git(self.root,'config','remote.origin.pushurl'),releases.DISABLED_PUSH)

    def test_tracked_edits_and_local_commits_have_recoverable_backups(self):
        target=self.publish()
        git(self.root,'config','user.name','Fixture');git(self.root,'config','user.email','fixture@localhost')
        (self.root/'local-code.py').write_text('local commit\n')
        git(self.root,'add','local-code.py');git(self.root,'commit','-m','local commit')
        local=git(self.root,'rev-parse','HEAD')
        (self.root/'README.md').write_text('uncommitted user edit\n');git(self.root,'add','README.md')
        self.repo.update()
        self.assertEqual(git(self.root,'rev-parse','HEAD'),target)
        self.assertIn(local,git(self.root,'for-each-ref','--format=%(objectname)','refs/heads/backup'))
        self.assertEqual(git(self.root,'show','stash@{0}:README.md'),'uncommitted user edit')
        self.assertFalse((self.root/'local-code.py').exists())

    def test_failed_post_switch_check_restores_source_index_and_native_files(self):
        self.publish()
        (self.root/'README.md').write_text('staged edit\n');git(self.root,'add','README.md')
        self.run.side_effect=releases.UpdateError('injected post-switch failure')
        with self.assertRaisesRegex(releases.UpdateError,'injected'):
            self.repo.update()
        self.assertEqual(git(self.root,'rev-parse','HEAD'),self.before)
        self.assertEqual((self.root/'README.md').read_text(),'staged edit\n')
        self.assertEqual(git(self.root,'show',':README.md'),'staged edit')
        self.assertEqual((self.root/'native/libabacus.so').read_bytes(),b'old native')
        self.assertFalse(self.repo.transaction.exists())
        self.assertFalse((self.root/'.runtime.local.json').exists())

    def test_candidate_failure_never_stops_mining_or_changes_checkout(self):
        self.publish();self.valid.side_effect=releases.UpdateError('candidate rejected')
        with self.assertRaisesRegex(releases.UpdateError,'candidate rejected'):self.repo.update()
        self.stop.assert_not_called()
        self.assertEqual(git(self.root,'rev-parse','HEAD'),self.before)

    def test_interrupted_switch_recovers_on_next_invocation(self):
        target=self.publish()
        (self.root/'README.md').write_text('recoverable edit\n')
        self.run.side_effect=releases.UpdateError('failed validation')
        with patch.object(self.repo,'_restore',side_effect=OSError('injected interruption')):
            with self.assertRaisesRegex(releases.UpdateError,'interrupted'):self.repo.update()
        self.assertTrue(self.repo.transaction.exists())
        self.assertEqual(git(self.root,'rev-parse','HEAD'),target)
        self.repo.update(rollback=True)
        self.assertFalse(self.repo.transaction.exists())
        self.assertEqual(git(self.root,'rev-parse','HEAD'),self.before)
        self.assertEqual((self.root/'README.md').read_text(),'recoverable edit\n')
        self.assertEqual((self.root/'native/libabacus.so').read_bytes(),b'old native')

    def test_failed_switch_restores_previous_runtime_selection(self):
        self.publish()
        original={'environment':'.updates/env-original'}
        (self.root/'.runtime.local.json').write_text(json.dumps(original))
        def validate(stage,**kwargs):
            python,_=self.validate(stage,**kwargs)
            return python,'.updates/env-new'
        self.valid.side_effect=validate
        self.run.side_effect=releases.UpdateError('failed validation')
        with self.assertRaises(releases.UpdateError):self.repo.update()
        self.assertEqual(json.loads((self.root/'.runtime.local.json').read_text()),original)

    def test_offline_fetch_retains_current_installation(self):
        self.repo.upstream=str(self.base/'missing.git')
        git(self.root,'remote','set-url','origin',self.repo.upstream)
        with self.assertRaises(releases.UpdateError):self.repo.update(on_open=True)
        self.stop.assert_not_called();self.valid.assert_not_called()
        self.assertEqual(git(self.root,'rev-parse','HEAD'),self.before)

    def test_check_only_and_repeat_update_do_not_stop(self):
        self.publish();self.repo.update(check=True)
        self.stop.assert_not_called();self.valid.assert_not_called()
        self.repo.update();self.stop.reset_mock();self.valid.reset_mock()
        self.assertFalse(self.repo.update())
        self.stop.assert_not_called();self.valid.assert_not_called()

    def test_main_role_skips_follower_updates_and_can_restore_push_url(self):
        self.publish();self.repo.set_role('follower');self.repo.set_role('main')
        self.assertFalse(self.repo.update(on_open=True))
        self.stop.assert_not_called();self.valid.assert_not_called()
        self.assertEqual(self.repo.git('config','--get','remote.origin.pushurl',check=False),'')

    def test_no_git_or_unexpected_origin_is_rejected(self):
        with self.assertRaises(releases.UpdateError):releases.Repository(self.base).update()
        git(self.root,'remote','set-url','origin','https://example.invalid/other.git')
        with self.assertRaisesRegex(releases.UpdateError,'expected'):self.repo.update()
        self.stop.assert_not_called()

    def test_same_installation_update_lock_is_exclusive(self):
        with self.repo.lock():
            with self.assertRaisesRegex(releases.UpdateError,'Another update'):
                with self.repo.lock():pass

    def test_untracked_release_collision_is_preserved(self):
        (self.root/'README.md').unlink()
        # A newly introduced public file can collide with a user's untracked file.
        (self.owner/'new.py').write_text('release')
        names=json.loads((self.owner/'PUBLIC_FILES.json').read_text())+['new.py']
        (self.owner/'PUBLIC_FILES.json').write_text(json.dumps(names))
        (self.owner/'FILES.sha256.json').write_text(json.dumps({n:hashlib.sha256((self.owner/n).read_bytes()).hexdigest() for n in names}))
        git(self.owner,'add','.');git(self.owner,'commit','-m','new source');git(self.owner,'push','origin','HEAD:stable')
        (self.root/'new.py').write_text('user file')
        with self.assertRaisesRegex(releases.UpdateError,'untracked'):self.repo.update()
        self.assertEqual((self.root/'new.py').read_text(),'user file');self.stop.assert_not_called()

    def test_archive_rejects_secret_paths_and_symlinks_before_validation(self):
        for name in ('machine.local.json','.updates/secret.txt'):
            with self.subTest(name=name):
                with self.assertRaises(ValueError):
                    from scripts.audit_public import check_payload
                    check_payload(name,b'fixture')
        (self.owner/'unsafe').symlink_to('README.md')
        git(self.owner,'add','unsafe');git(self.owner,'commit','-m','invalid link');git(self.owner,'push','origin','HEAD:stable')
        with self.assertRaisesRegex(releases.UpdateError,'unsupported'):self.repo.update()
        self.stop.assert_not_called();self.valid.assert_not_called()

    def test_on_open_postpones_dependency_changes_without_creating_environment(self):
        stage=self.base/'candidate';stage.mkdir()
        with patch.object(self.repo,'dependencies_match',return_value=False):
            with self.assertRaisesRegex(releases.UpdateError,'approval'):
                releases.Repository.validate(self.repo,stage,on_open=True)
        self.run.assert_not_called();self.stop.assert_not_called()
        self.assertFalse(list(self.repo.area.glob('env-*')))

    def test_manual_dependency_decline_retains_environment(self):
        stage=self.base/'candidate';stage.mkdir()
        with patch.object(self.repo,'dependencies_match',return_value=False),patch.object(sys.stdin,'isatty',return_value=True),patch('builtins.input',return_value='n'):
            with self.assertRaisesRegex(releases.UpdateError,'declined'):
                releases.Repository.validate(self.repo,stage,on_open=False)
        self.run.assert_not_called()

    def test_manual_dependency_accept_uses_new_environment_without_touching_original(self):
        stage=self.base/'candidate';stage.mkdir()
        with patch.object(self.repo,'dependencies_match',return_value=False):
            python,environment=releases.Repository.validate(self.repo,stage,on_open=False,yes=True)
        self.assertTrue(environment.startswith('.updates/env-'))
        self.assertIn(environment,str(python).replace('\\','/'))
        command=self.run.call_args_list[0].args[0]
        self.assertIn('--yes',command);self.assertIn('--environment',command)

    def test_runtime_pointer_cannot_select_outside_executable(self):
        for value in ('../other','/tmp/other','.venv','..\\other'):
            (self.root/'.runtime.local.json').write_text(json.dumps({'environment':value}))
            with self.assertRaises(ValueError):runtime.interpreter(self.root)

    def test_pending_transaction_blocks_start_before_any_network_or_process(self):
        self.repo.area.mkdir(exist_ok=True);self.repo.transaction.write_text('{}')
        with patch.object(service,'ROOT',self.root),patch.object(service,'request') as request:
            with self.assertRaisesRegex(ValueError,'recovery'):service._start()
            request.assert_not_called()

    def test_release_pushes_only_after_secret_scan_and_exact_ci_success(self):
        owner=releases.Repository(self.owner,upstream=str(self.origin));owner.set_role('main')
        (self.owner/'README.md').write_text('next reviewed release\n');manifest(self.owner)
        git(self.owner,'add','.');git(self.owner,'commit','-m','next release')
        target=git(self.owner,'rev-parse','HEAD')
        with patch.object(owner,'run') as run,patch.object(owner,'ci_passed',side_effect=[False,True]),patch.object(releases.time,'sleep'):
            owner.release(yes=True,gitleaks='fixture-gitleaks')
        self.assertEqual(git(self.origin,'rev-parse','refs/heads/stable'),target)
        self.assertTrue(any('git' in call.args[0] and '--redact' in call.args[0] for call in run.call_args_list))

    def test_failed_release_scan_never_pushes(self):
        owner=releases.Repository(self.owner,upstream=str(self.origin));owner.set_role('main')
        with patch.object(owner,'run',side_effect=releases.UpdateError('secret scan rejected')),patch.object(owner,'ci_passed') as ci:
            with self.assertRaisesRegex(releases.UpdateError,'scan rejected'):owner.release(yes=True,gitleaks='fixture')
            ci.assert_not_called()
        self.assertEqual(git(self.origin,'rev-parse','stable'),self.before)

    def test_ci_requires_the_latest_matching_push_to_pass(self):
        sha='a'*40
        success=dict(id=1,head_sha=sha,head_branch='main',event='push',status='completed',conclusion='success')
        failed=dict(success,id=2,conclusion='failure')
        for runs,expected in (([success],True),([dict(success,head_sha='b'*40)],False),
                              ([dict(success,status='in_progress',conclusion=None)],False)):
            with patch.object(releases.urllib.request,'urlopen',return_value=io.BytesIO(json.dumps({'workflow_runs':runs}).encode())):
                self.assertEqual(self.repo.ci_passed(sha),expected)
        with patch.object(releases.urllib.request,'urlopen',return_value=io.BytesIO(json.dumps({'workflow_runs':[success,failed]}).encode())):
            with self.assertRaisesRegex(releases.UpdateError,'CI failed'):self.repo.ci_passed(sha)

    def test_publisher_refuses_dirty_or_follower_checkout(self):
        with self.assertRaisesRegex(releases.UpdateError,'Only the main'):self.repo.release(yes=True,gitleaks='fixture')
        self.repo.set_role('main');(self.root/'README.md').write_text('unreviewed')
        with self.assertRaisesRegex(releases.UpdateError,'Review and commit'):self.repo.release(yes=True,gitleaks='fixture')


if __name__=='__main__':unittest.main()
