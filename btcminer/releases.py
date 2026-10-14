"""Explicit stable releases and transactional updates for this Git installation."""
import argparse
from contextlib import contextmanager
from datetime import datetime, timezone
import hashlib
import importlib.metadata
import io
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import signal
import subprocess
import sys
import tarfile
import time
import urllib.request
import uuid

from .platform_support import fcntl, private_file, detached_options

UPSTREAM = 'https://github.com/BuzzScud/BTC-MINER.git'
API = 'https://api.github.com/repos/BuzzScud/BTC-MINER/actions/workflows/ci.yml/runs'
DISABLED_PUSH = 'DISABLED--use-the-main-machine-to-release'


class UpdateError(RuntimeError):
    pass


def write_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name+'.'+uuid.uuid4().hex+'.tmp')
    with temporary.open('w', encoding='utf-8') as output:
        output.write(json.dumps(value, indent=2)+'\n')
        output.flush()
        os.fsync(output.fileno())
    private_file(temporary)
    os.replace(temporary, path)


class Repository:
    def __init__(self, root, upstream=UPSTREAM):
        self.root = Path(root).resolve()
        self.upstream = upstream
        self.area = self.root/'.updates'
        self.transaction = self.area/'transaction.json'

    def git(self, *args, check=True, binary=False, timeout=30):
        env = dict(os.environ, GIT_TERMINAL_PROMPT='0', GIT_NO_REPLACE_OBJECTS='1')
        command = ['git', '-c', 'core.hooksPath='+str(self.area/'empty-hooks'),
                   '-c', 'core.fsmonitor=false', '-c', 'core.autocrlf=false',
                   '-c', 'push.followTags=false',
                   '-c', 'http.lowSpeedLimit=1', '-c', 'http.lowSpeedTime=10',
                   '-C', str(self.root), *args]
        try:
            process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                       text=not binary, env=env, **detached_options())
            try:
                output, _ = process.communicate(timeout=timeout)
            except subprocess.TimeoutExpired:
                if os.name == 'nt':
                    subprocess.run(['taskkill','/PID',str(process.pid),'/T','/F'],
                                   stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,timeout=5)
                else:
                    os.killpg(process.pid, signal.SIGKILL)
                process.kill()
                process.communicate(timeout=5)
                raise
        except (OSError, subprocess.TimeoutExpired):
            raise UpdateError('Git is unavailable or the operation timed out; installed files were retained.') from None
        if check and process.returncode:
            raise UpdateError('Git '+args[0]+' failed; resolve local conflicts or check the connection.')
        return output if process.returncode == 0 else (b'' if binary else '')

    def available(self):
        return bool(shutil.which('git') and (self.root/'.git').exists())

    def require_checkout(self):
        if not self.available():
            raise UpdateError('Updates require a Git clone. Clone BTC-MINER and run setup; preserve your local settings.')
        if Path(self.git('rev-parse','--show-toplevel').strip()).resolve() != self.root:
            raise UpdateError('Git points to a different working directory; no update was applied.')
        origin = self.git('remote', 'get-url', 'origin', check=False).strip()
        allowed = {self.upstream}
        if self.upstream == UPSTREAM:
            allowed |= {'https://github.com/BuzzScud/BTC-MINER', 'git@github.com:BuzzScud/BTC-MINER.git',
                        'ssh://git@github.com/BuzzScud/BTC-MINER.git'}
        if origin not in allowed:
            raise UpdateError('origin is not the expected BTC-MINER repository; update was not applied.')

    def role(self):
        return 'main' if self.git('config', '--get', 'btcminer.role', check=False).strip() == 'main' else 'follower'

    def set_role(self, value):
        self.require_checkout()
        if value == 'follower':
            push = self.git('config', '--get', 'remote.origin.pushurl', check=False).strip()
            if push and push != DISABLED_PUSH:
                self.git('config', 'btcminer.savedPushURL', push)
            self.git('config', 'remote.origin.pushurl', DISABLED_PUSH)
        else:
            if self.git('config', '--get', 'remote.origin.pushurl', check=False).strip() == DISABLED_PUSH:
                saved = self.git('config', '--get', 'btcminer.savedPushURL', check=False).strip()
                if saved:
                    self.git('config', 'remote.origin.pushurl', saved)
                else:
                    self.git('config', '--unset-all', 'remote.origin.pushurl', check=False)
        self.git('config', 'btcminer.role', value)
        return value

    def notice(self, message):
        try:
            if not self.area.is_symlink():
                write_json(self.area/'last-result.json', {'message':message, 'at':datetime.now(timezone.utc).isoformat()})
        except OSError:
            pass
        print(message, flush=True)

    @contextmanager
    def lock(self):
        if self.area.is_symlink():
            raise UpdateError('The update directory must not be a symbolic link.')
        self.area.mkdir(exist_ok=True, mode=0o700)
        (self.area/'empty-hooks').mkdir(exist_ok=True)
        with (self.area/'update.lock').open('a+') as handle:
            try:
                fcntl.flock(handle, fcntl.LOCK_EX|fcntl.LOCK_NB)
            except BlockingIOError:
                raise UpdateError('Another update or release is running.') from None
            yield

    def export(self, target, stage):
        """Materialize only regular, reviewed source files; never extract links."""
        from scripts.audit_public import check_payload
        raw = self.git('archive', '--format=tar', target, binary=True, timeout=60)
        with tarfile.open(fileobj=io.BytesIO(raw)) as archive:
            members = archive.getmembers()
            files = {}
            for member in members:
                name = PurePosixPath(member.name)
                if (name.is_absolute() or '..' in name.parts or '\\' in member.name
                        or ':' in member.name or name.as_posix() != member.name.rstrip('/')):
                    raise UpdateError('Release contains an unsafe path.')
                if member.isdir():
                    continue
                if not member.isfile() or member.name in files or member.size > 64*1024*1024:
                    raise UpdateError('Release contains an unsupported file or duplicate path.')
                files[member.name] = member
            if sum(m.size for m in files.values()) > 256*1024*1024:
                raise UpdateError('Release exceeds the source size limit.')
            def read(name):
                return archive.extractfile(files[name]).read()
            try:
                inventory = json.loads(read('PUBLIC_FILES.json'))
                hashes = json.loads(read('FILES.sha256.json'))
                if set(files) != set(inventory)|{'FILES.sha256.json'} or set(hashes) != set(inventory):
                    raise UpdateError('Release inventory is incomplete or contains unexpected files.')
                for name in files:
                    payload = read(name)
                    check_payload(name, payload)
                    if name in hashes and hashlib.sha256(payload).hexdigest() != hashes[name]:
                        raise UpdateError('Release source digest mismatch.')
                    destination = stage/name
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    destination.write_bytes(payload)
                    destination.chmod(files[name].mode & 0o777)
            except (KeyError, TypeError, ValueError):
                raise UpdateError('Release inventory or public-file checks failed.') from None
        return set(files)

    def dependencies_match(self, stage):
        try:
            for line in (stage/'requirements.txt').read_text().splitlines():
                if not line.strip() or line.startswith('#'):
                    continue
                name, expected = line.split('==')
                if importlib.metadata.version(name) != expected:
                    return False
            return True
        except (ValueError, importlib.metadata.PackageNotFoundError):
            return False

    def run(self, command, cwd, log):
        env = dict(os.environ, PYTHONUTF8='1', PYTHONDONTWRITEBYTECODE='1', BTC_VALIDATE_RUNTIME='1')
        # Prompts stay interactive; detailed build/test output stays in the update log.
        with log.open('ab') as output:
            result = subprocess.run([str(x) for x in command], cwd=cwd, env=env,
                                    stdout=output, stderr=output)
        if result.returncode:
            raise UpdateError('Candidate validation failed. See '+str(log.relative_to(self.root))+'.')

    def validate(self, stage, *, on_open, yes=False):
        from .runtime import interpreter
        log = self.area/'validation.log'
        same = self.dependencies_match(stage)
        if not same:
            if on_open:
                raise UpdateError('New dependencies need approval; run btc-miner update in a terminal.')
            print('This release needs the pinned packages in its requirements.txt, in a new isolated environment.')
            if not yes and (not sys.stdin.isatty() or input('Download and install them? [y/N] ').strip().lower() not in ('y','yes')):
                raise UpdateError('Dependency installation declined; current version retained.')
            environment = self.area/('env-'+uuid.uuid4().hex)
        else:
            environment = Path(interpreter(self.root)).parent.parent
        command = [sys.executable, 'scripts/setup_terminal.py', '--no-wizard', '--no-compiler-install', '--environment', environment]
        command += ['--no-install'] if same or on_open else ['--yes']
        self.run(command, stage, log)
        python = environment/('Scripts/python.exe' if os.name == 'nt' else 'bin/python')
        for args in (['scripts/check_math_integrity.py'], ['scripts/audit_public.py', '--worktree'],
                     ['-B','-m','unittest','discover','-s','tests']):
            self.run([python, *args], stage, log)
        return str(python), (environment.relative_to(self.root).as_posix() if not same else None)

    def _tracked(self):
        return set(filter(None, self.git('ls-files', '-z').split('\0')))

    def _restore(self, record):
        # No force/reset/clean: concurrent user edits must never be discarded.
        if not record.get('stash') and record.get('stash_message'):
            message = self.git('log','-1','--format=%s','refs/stash',check=False).strip()
            if message.endswith(': '+record['stash_message']):
                record['stash'] = self.git('rev-parse','refs/stash').strip()
        branch = record['branch']
        if branch:
            self.git('checkout', '-B', branch, record['before'])
        else:
            self.git('checkout', '--detach', record['before'])
        backup = self.area/record['backup']
        for name, existed in record['binaries'].items():
            path = self.root/'native'/name
            if existed:
                temporary = path.with_suffix(path.suffix+'.restore')
                shutil.copy2(backup/name, temporary)
                os.replace(temporary, path)
            else:
                path.unlink(missing_ok=True)
        pointer = self.root/'.runtime.local.json'
        if record['runtime'] is None:
            pointer.unlink(missing_ok=True)
        else:
            write_json(pointer, record['runtime'])
        if record.get('stash'):
            self.git('stash', 'apply', '--index', record['stash'])
        self.transaction.unlink(missing_ok=True)

    def recover(self):
        if not self.transaction.exists():
            return False
        from . import service
        with service.lifecycle_lock():
            service._stop(summary=True)
            self._restore(json.loads(self.transaction.read_text()))
        self.notice('Interrupted update rolled back; miner is stopped. Local backup refs were retained.')
        return True

    def apply(self, target, stage, python, environment):
        from . import service
        before = self.git('rev-parse', 'HEAD').strip()
        branch = self.git('symbolic-ref', '--short', '-q', 'HEAD', check=False).strip()
        stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'-'+uuid.uuid4().hex[:8]
        backup = self.area/('backup-'+stamp)
        backup.mkdir()
        built = sorted(p for p in (stage/'native').iterdir() if p.suffix in ('.dll','.so','.dylib'))
        if len(built) != 3:
            raise UpdateError('Expected all three validated native libraries.')
        binaries = {}
        for file in built:
            original = self.root/'native'/file.name
            binaries[file.name] = original.is_file()
            if original.is_file():
                shutil.copy2(original, backup/file.name)
        pointer = self.root/'.runtime.local.json'
        record = dict(before=before, target=target, branch=branch, backup=backup.name, binaries=binaries,
                      runtime=json.loads(pointer.read_text()) if pointer.exists() else None, stash=None,
                      stash_message='BTC update backup '+stamp)
        with service.lifecycle_lock():
            # Stop only this installation, after the candidate has passed validation.
            service._stop(summary=True)
            self.git('branch', 'backup/'+stamp, before)
            previous_stable = self.git('rev-parse','--verify','refs/heads/stable',check=False).strip()
            if previous_stable and previous_stable != before:
                self.git('branch','backup/'+stamp+'-stable',previous_stable)
            write_json(self.transaction, record)
            try:
                if self.git('status', '--porcelain', '--untracked-files=no').strip():
                    self.git('-c','user.name=BTC Miner update','-c','user.email=update@localhost',
                             'stash','push','-m',record['stash_message'])
                    record['stash'] = self.git('rev-parse','refs/stash').strip()
                    write_json(self.transaction, record)
                self.git('checkout', '-B', 'stable', target)
                for file in built:
                    destination = self.root/'native'/file.name
                    temporary = destination.with_suffix(destination.suffix+'.incoming')
                    shutil.copy2(file, temporary)
                    os.replace(temporary, destination)
                if environment:
                    write_json(pointer, {'environment':environment})
                self.run([python,'-B','-m','btcminer','self-test','--require-native'], self.root, self.area/'validation.log')
                self.set_role('follower')
                self.git('config','branch.stable.remote','origin')
                self.git('config','branch.stable.merge','refs/heads/stable')
                self.transaction.unlink()
            except BaseException:
                try:
                    self._restore(record)
                except Exception:
                    raise UpdateError('Update interrupted; miner stays stopped. Run update --rollback. Backups are in .updates and backup/ Git refs.') from None
                raise
        self.notice('Updated '+before[:7]+' → '+target[:7]+'. Miner is stopped; press s to start. Source backup: backup/'+stamp+'.')

    def update(self, *, on_open=False, yes=False, check=False, rollback=False):
        self.require_checkout()
        with self.lock():
            if rollback:
                if not self.recover():
                    self.notice('No interrupted update needs rollback.')
                return False
            if self.transaction.exists():
                self.recover()
                return False
            if self.role() == 'main':
                if not on_open:
                    self.notice('Main checkout retained. Review main with Git; use release to publish to followers.')
                return False
            self.git('fetch','--quiet','--no-tags',self.upstream,
                     '+refs/heads/stable:refs/remotes/origin/stable',timeout=15)
            target = self.git('rev-parse','refs/remotes/origin/stable^{commit}').strip()
            head = self.git('rev-parse','HEAD').strip()
            edited = bool(self.git('status','--porcelain','--untracked-files=no').strip())
            if target == head and not edited:
                if not on_open:
                    self.notice('Up to date: '+head[:7]+'.')
                return False
            if check:
                self.notice(('Local source edits will be backed up and restored to stable. ' if edited else '')+
                            'Release: '+head[:7]+' → '+target[:7]+'. Run update to install it.')
                return False
            stage = self.area/('stage-'+uuid.uuid4().hex)
            stage.mkdir()
            try:
                incoming = self.export(target, stage)
                for name in incoming-self._tracked():
                    if (self.root/name).exists() or (self.root/name).is_symlink():
                        raise UpdateError('A local untracked file conflicts with the release: '+name)
                self.notice('Validating release '+target[:7]+' before changing this installation…')
                python, environment = self.validate(stage, on_open=on_open, yes=yes)
                self.apply(target, stage, python, environment)
                return True
            finally:
                shutil.rmtree(stage)

    def ci_passed(self, sha):
        request = urllib.request.Request(API+'?head_sha='+sha+'&per_page=20', headers={'User-Agent':'BTC-Miner-release'})
        try:
            with urllib.request.urlopen(request, timeout=15) as response:
                runs = json.load(response)['workflow_runs']
        except Exception:
            raise UpdateError('Cannot verify GitHub CI for this commit; stable was not changed.') from None
        relevant = [r for r in runs if r.get('head_sha') == sha and r.get('head_branch') == 'main' and r.get('event') == 'push']
        if not relevant:
            return False
        latest = max(relevant, key=lambda r:r['id'])
        if latest.get('status') == 'completed' and latest.get('conclusion') != 'success':
            raise UpdateError('Platform CI failed for this commit; stable was not changed.')
        return latest.get('conclusion') == 'success'

    def release(self, *, yes=False, gitleaks=None):
        self.require_checkout()
        push_url = self.git('remote','get-url','--push','origin').strip()
        allowed = {self.upstream,'git@github.com:BuzzScud/BTC-MINER.git',
                   'ssh://git@github.com/BuzzScud/BTC-MINER.git','https://github.com/BuzzScud/BTC-MINER'}
        with self.lock():
            if self.role() != 'main':
                raise UpdateError('Only the main checkout releases. Select role main on your publishing machine.')
            if push_url not in allowed:
                raise UpdateError('The push destination is not the expected BTC-MINER repository.')
            if self.transaction.exists() or self.git('symbolic-ref','--short','HEAD').strip() != 'main':
                raise UpdateError('Release from main with no incomplete update.')
            if self.git('status','--porcelain').strip():
                raise UpdateError('Review and commit the public inventory first; release never commits unrelated files.')
            scanner = gitleaks or shutil.which('gitleaks')
            if not scanner:
                raise UpdateError('Install Gitleaks or pass --gitleaks PATH. No release was pushed.')
            sha = self.git('rev-parse','HEAD').strip()
            log = self.area/'release-validation.log'
            for args in (['scripts/audit_public.py'], ['scripts/check_math_integrity.py'],
                         ['scripts/verify_proof_evidence.py'], ['scripts/sync_layout.py','--check']):
                self.run([sys.executable,*args],self.root,log)
            self.run([scanner,'git','--redact','--log-opts=--all'],self.root,log)
            stage = self.area/('release-'+uuid.uuid4().hex)
            stage.mkdir()
            try:
                self.export(sha, stage)
                self.run([scanner,'dir','--redact',stage],self.root,log)
            finally:
                shutil.rmtree(stage)
            print('Release reviewed commit '+sha[:12]+' to all followers via stable.')
            if not yes and (not sys.stdin.isatty() or input('Publish this release? [y/N] ').strip().lower() not in ('y','yes')):
                raise UpdateError('Release cancelled.')
            self.git('push','origin',sha+':refs/heads/main',timeout=60)
            deadline = time.monotonic()+25*60
            while not self.ci_passed(sha):
                if time.monotonic() >= deadline:
                    raise UpdateError('CI is still pending; rerun release later. Stable was not changed.')
                print('Waiting for platform CI before publishing stable…',flush=True)
                time.sleep(15)
            if self.git('rev-parse','HEAD').strip() != sha or self.git('status','--porcelain').strip():
                raise UpdateError('Publishing checkout changed during CI; stable was not changed.')
            self.git('push','--atomic','origin',sha+':refs/heads/main',sha+':refs/heads/stable',timeout=60)
            self.notice('Released '+sha[:12]+'. Followers receive it on dashboard open or manual update; mining stays stopped.')


def main(argv=None):
    from . import ROOT
    parser = argparse.ArgumentParser(prog='btc-miner')
    sub = parser.add_subparsers(dest='command',required=True)
    role = sub.add_parser('role',help='Select this Git installation as main or follower')
    role.add_argument('value',nargs='?',choices=('main','follower'))
    update = sub.add_parser('update',help='Validate and install the stable release; keep mining stopped')
    update.add_argument('--check',action='store_true')
    update.add_argument('--rollback',action='store_true')
    update.add_argument('--yes',action='store_true',help='Approve dependency installation for this manual update')
    release = sub.add_parser('release',help='Scan, check CI, and publish the committed main revision to stable')
    release.add_argument('--yes',action='store_true')
    release.add_argument('--gitleaks')
    args = parser.parse_args(argv)
    repo = Repository(ROOT)
    try:
        if args.command == 'role':
            repo.require_checkout()
            print(repo.set_role(args.value) if args.value else repo.role())
        elif args.command == 'update':
            repo.update(check=args.check,rollback=args.rollback,yes=args.yes)
        else:
            repo.release(yes=args.yes,gitleaks=args.gitleaks)
        return 0
    except (UpdateError,OSError,ValueError) as error:
        print('BTC Miner: '+str(error),file=sys.stderr)
        return 1
    except (KeyboardInterrupt,EOFError):
        print('Cancelled. If an update was interrupted, run update --rollback.',file=sys.stderr)
        return 1
