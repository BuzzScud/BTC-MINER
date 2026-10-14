#!/usr/bin/env python3
"""Read-only Aristotle task monitoring, pinned Lean checks, and miner regression checks.

Remote updates are evidence, never executable Python patches. Changed source hashes
remain pending implementation review until the reviewed-source manifest matches.
"""
import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import urllib.parse
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from btcminer.platform_support import fcntl
OUT = ROOT / 'validation/aristotle-current'
TASK = 'acfd50e8-1951-4593-986d-30a11b056e92'
PROJECT = '9b854e2d-2ae1-4d55-9b53-bf308b5e3648'
API = 'https://aristotle.harmonic.fun/api/v3'
CHECK_INTERVAL = 3600
TARGETS = ['RequestProject.EllipseSearch', 'RequestProject.DynamicRods', 'RequestProject.CorePrimes']
LATEST_TARGETS = TARGETS + ['RequestProject.RodCircles', 'RequestProject.RodScaling',
                          'RequestProject.ShellEnrichment', 'RequestProject.TowerCollapse',
                          'RequestProject.BaseDensity']
BIN = ROOT / '.test-tools/lean-4.28.0-darwin_aarch64/bin'
PINNED = ROOT / 'validation/math-audit/aristotle-snapshot'


def stamp():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + '.pending')
    tmp.write_text(json.dumps(value, indent=2) + '\n')
    tmp.replace(path)


def get(route, params=None):
    url = API + route + ('?' + urllib.parse.urlencode(params) if params else '')
    with urllib.request.urlopen(url, timeout=30) as response:
        return json.load(response)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def implementation_fingerprint():
    if str(ROOT) not in sys.path:
        sys.path.insert(0,str(ROOT))
    from btcminer.mathrevision import FILES
    return {name:sha(ROOT/name) for name in FILES}


def validation_path(task_id):
    if not re.fullmatch(r'[A-Za-z0-9-]+', task_id):
        raise ValueError('Invalid task ID')
    return OUT/'latest-validation.json' if task_id == TASK else OUT/'task-validations'/(task_id+'.json')


def miner_is_running():
    # A held supervisor lock also covers startup/reconnect and manual pause.
    if str(ROOT) not in sys.path:
        sys.path.insert(0,str(ROOT))
    from btcminer import service
    return service.supervisor_running()


def run_lean(command, **kwargs):
    """Give mining priority if it starts during an otherwise idle proof audit."""
    timeout = kwargs.pop('timeout')
    if miner_is_running():
        raise RuntimeError('Proof audit deferred while miner is running')
    process = subprocess.Popen(command, **kwargs)
    deadline = time.monotonic()+timeout
    try:
        while process.poll() is None:
            if miner_is_running():
                raise RuntimeError('Proof audit interrupted to protect running miner')
            if time.monotonic() >= deadline:
                raise subprocess.TimeoutExpired(command,timeout)
            time.sleep(2)
        return subprocess.CompletedProcess(command,process.returncode)
    finally:
        if process.poll() is None:
            process.terminate()
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()


def cached_success(report, previous):
    """Failed retries must not erase access to earlier successful proof builds."""
    candidates = [previous]
    for path in (OUT/'revisions').glob('*/validation.json'):
        try:
            candidates.append(json.loads(path.read_text()))
        except (OSError,ValueError):
            continue
    usable = [r for r in candidates if r.get('ok') and
              r.get('lean_version') == report.get('lean_version') and
              r.get('dependency_manifest_sha256') == report.get('dependency_manifest_sha256') and
              set(r.get('axioms',[])) <= {'propext','Classical.choice','Quot.sound'}]
    return max(usable,key=lambda r:sum(r.get('sources',{}).get(p)==h for p,h in report['sources'].items()),
               default={})


def validate(task):
    if task['status'] != 'COMPLETE':
        raise ValueError('Only completed Aristotle revisions can be validated')
    if miner_is_running():
        raise RuntimeError('Proof audit deferred while miner is running')
    task_id = task['agent_task_id']
    targets = TARGETS if task_id == TASK else LATEST_TARGETS
    destination = validation_path(task_id)
    previous = json.loads(destination.read_text()) if destination.exists() else {}
    revision = OUT / 'revisions' / dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    source = revision / 'sources'
    source.mkdir(parents=True)
    save(revision / 'task.json', task)
    order, visiting, hashes = [], set(), {}

    def fetch(name):
        response = get(f'/task/{task_id}/file', {'file_path': name})
        body = response.get('output_content')
        if not isinstance(body, str) or response.get('content_encoding') != 'utf-8':
            raise ValueError('Missing UTF-8 output: ' + name)
        path = source / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(body)
        hashes[name] = sha(path)
        time.sleep(.25)
        return body

    def visit(module):
        if module in order:
            return
        if module in visiting:
            raise ValueError('Cyclic imports: ' + module)
        visiting.add(module)
        body = fetch(module.replace('.', '/') + '.lean')
        for dep in re.findall(r'^(?:public )?import ([\w.]+)', body, re.M):
            if dep.startswith(('RequestProject.', 'LatticeCalc.')):
                visit(dep)
        order.append(module)
        visiting.remove(module)

    for target in targets:
        visit(target)
    for name in ['CORE_PRIMES.md', 'ELLIPSE_AND_RODS.md']:
        fetch(name)
    if task_id != TASK:
        fetch('RODS_FLOWERS_TOWERS.md')
    # Fetch the task again so a changing remote revision cannot be marked valid.
    after = get(f'/task/{task_id}')
    if after != task:
        raise RuntimeError('Task changed during source capture; retry next cycle')
    report = {'checked_at_utc': stamp(), 'task_id': task_id, 'task_status': task['status'],
              'remote_updated_at': task['last_updated_at'], 'sources': hashes,
              'revision': str(revision), 'targets': targets, 'builds': [], 'ok': False,
              'scope': 'Selected miner-related modules and their local import closure; not the entire research project'}
    save(revision / 'validation.json', report)
    env = dict(os.environ, PATH=str(BIN) + os.pathsep + os.environ.get('PATH', ''),
               LEAN_NUM_THREADS='1', LC_ALL='C', PYTHONDONTWRITEBYTECODE='1')
    dependencies = subprocess.check_output([str(BIN/'lake'), 'env', 'printenv', 'LEAN_PATH'],
                                           cwd=PINNED, env=env, text=True).strip()
    # Relative search paths from lake must remain relative to the pinned project.
    paths = [str((PINNED / p).resolve()) if not Path(p).is_absolute() else p
             for p in dependencies.split(os.pathsep)]
    env['LEAN_PATH'] = str(source) + os.pathsep + os.pathsep.join(paths)
    report['lean_version'] = subprocess.check_output([str(BIN/'lean'), '--version'], env=env, text=True).strip()
    report['dependency_manifest_sha256'] = sha(PINNED/'lake-manifest.json')
    previous = cached_success(report, previous)
    reusable = {}
    cache_ok = (previous.get('ok') and previous.get('lean_version') == report['lean_version'] and
                previous.get('dependency_manifest_sha256') == report['dependency_manifest_sha256'])
    for module in order:
        relative = module.replace('.', '/') + '.lean'
        deps = [dep for dep in re.findall(r'^(?:public )?import ([\w.]+)', (source/relative).read_text(), re.M)
                if dep.startswith(('RequestProject.', 'LatticeCalc.'))]
        old = Path(previous.get('revision',''))/'sources'/relative
        reusable[module] = bool(cache_ok and previous.get('sources',{}).get(relative) == hashes[relative]
                                and all(reusable.get(dep,False) for dep in deps) and old.with_suffix('.olean').exists())
        if reusable[module]:
            for artifact in old.parent.glob(old.stem+'.olean*'):
                shutil.copy2(artifact, (source/relative).parent/artifact.name)
            if old.with_suffix('.ir').exists():
                shutil.copy2(old.with_suffix('.ir'), (source/relative).with_suffix('.ir'))
            report['builds'].append({'module':module,'exit_code':0,'reused_validated_artifact':True,
                                    'from_revision':previous['revision']})
            save(revision/'validation.json', report)
            print(module+': reused identical validated source and dependencies',flush=True)
            continue
        log = revision / (module + '.log')
        with log.open('w') as stream:
            run = run_lean([str(BIN/'lean'), '-j1', '-M2048', '-o', str((source/relative).with_suffix('.olean')), relative],
                                 cwd=source, env=env, stdout=stream, stderr=subprocess.STDOUT, timeout=1800)
        report['builds'].append({'module': module, 'exit_code': run.returncode})
        save(revision/'validation.json', report)
        print(module + ': ' + str(run.returncode), flush=True)
        if run.returncode:
            errors = log.read_text()
            report['failure_kind'] = ('resource_limit' if 'memory_exception' in errors or
                                      'excessive memory consumption' in errors else 'lean_build_error')
            save(revision/'validation.json',report)
            save(destination, report)
            raise RuntimeError('Lean failed: ' + module + '; see ' + str(log))
    template = (ROOT/'validation/math-audit/AxiomUnion.lean').read_text()
    body = template[template.index('  let indices :='):]
    driver = source/'Audit.lean'
    driver.write_text('\n'.join('import '+m for m in targets) +
        '\nopen Lean Elab Command\ndef auditEnv (env : Environment) (mods : Array Name) : IO Unit := do\n' +
        body + '\nrun_cmd do\n  liftIO <| auditEnv (← getEnv) #[' + ', '.join('`'+m for m in targets) + ']\n')
    with (revision/'axioms.tsv').open('w') as stream:
        run = run_lean([str(BIN/'lean'), '-j1', '-M2048', str(driver)], cwd=source, env=env,
                             stdout=stream, stderr=subprocess.STDOUT, timeout=1800)
    lines = (revision/'axioms.tsv').read_text().splitlines()
    axioms = sorted(x.split('\t')[1] for x in lines if x.startswith('axiom\t'))
    count = sum(x.startswith('theorem\t') for x in lines)
    report.update(axioms=axioms, theorem_count=count, axiom_audit_exit_code=run.returncode)
    with (revision/'miner-tests.log').open('w') as stream:
        run_tests = subprocess.run([sys.executable, '-B', '-m', 'unittest', 'discover', '-s', 'tests', '-v'],
                                   cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT, timeout=180)
    report['miner_tests_exit_code'] = run_tests.returncode
    report['ok'] = (run.returncode == 0 and count > 0 and run_tests.returncode == 0 and
                    set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'})
    report['completed_at_utc'] = stamp()
    save(revision/'validation.json', report)
    save(destination, report)
    return report


def latest_project_task():
    """Inspect every page so server ordering cannot hide a newer run."""
    tasks, cursors, params = [], set(), None
    while True:
        page = get(f'/project/{PROJECT}/tasks', params)
        tasks.extend(page['agent_tasks'])
        cursor = page.get('pagination_key')
        if not cursor:
            break
        if cursor in cursors:
            raise RuntimeError('Repeated project task pagination cursor')
        cursors.add(cursor)
        params = {'pagination_key': cursor}
    if not tasks:
        raise RuntimeError('Project returned no tasks')
    return max(tasks, key=lambda task: (task['created_at'], task['agent_task_id']))


def process_identity(pid):
    try:
        result = subprocess.run(['ps','-p',str(pid),'-o','lstart=','-o','stat='],
                                capture_output=True,text=True,timeout=5)
        value = result.stdout.strip()
        return value.rsplit(None,1)[0] if result.returncode == 0 and value and 'Z' not in value.split()[-1] else None
    except (OSError,subprocess.TimeoutExpired):
        return None


def queue_validation(task):
    if miner_is_running():
        deferred = {'task_id':task['agent_task_id'],'state':'deferred while miner is running','checked_at_utc':stamp()}
        save(OUT/'deferred-validation.json',deferred)
        return deferred
    path = OUT/'active-validation.json'
    active = json.loads(path.read_text()) if path.exists() else {}
    if active.get('pid') and active.get('identity') and process_identity(active['pid']) == active['identity']:
        return active
    with (OUT/'validation-worker.log').open('a') as log:
        worker = subprocess.Popen([sys.executable,'-B',str(Path(__file__).resolve()),
                                   '--validate-task',task['agent_task_id']],cwd=ROOT,
                                  stdin=subprocess.DEVNULL,stdout=log,stderr=log,start_new_session=True)
    active = {'pid':worker.pid,'identity':process_identity(worker.pid),
              'task_id':task['agent_task_id'],'started_at_utc':stamp()}
    save(path,active)
    return active


def audit_or_queue(task, background):
    if not background:
        return validate(task)
    queue_validation(task)
    path = validation_path(task['agent_task_id'])
    return json.loads(path.read_text()) if path.exists() else {}


def reviewed_update_candidate():
    """Keep a reviewed revision eligible while newer research is unfinished."""
    path = ROOT/'reference/aristotle-rods-towers/reviewed-sources.json'
    if not path.exists():
        return None
    manifest = json.loads(path.read_text())
    task_id = manifest.get('task_id')
    if not task_id or not manifest.get('implementation') or not manifest.get('sources'):
        return None
    # Only the explicit local math files may establish implementation identity.
    if manifest['implementation'] != implementation_fingerprint():
        return None
    task = get('/task/'+task_id)
    if task.get('status') != 'COMPLETE':
        return None
    path = validation_path(task_id)
    report = json.loads(path.read_text()) if path.exists() else {}
    if (not report.get('ok') or report.get('targets') != LATEST_TARGETS or
            report.get('remote_updated_at') != task.get('last_updated_at')):
        queue_validation(task)
        return None
    if (report.get('task_id') != task_id or report.get('task_status') != 'COMPLETE' or
            report.get('sources') != manifest['sources']):
        return None
    return task_id


def deploy_reviewed(state):
    task_id = (state.get('latest_task_id') if state.get('latest_task_validation_ok') and
               state.get('latest_task_implementation_review') == 'matches reviewed sources'
               else reviewed_update_candidate())
    if not task_id:
        return {'applied':False,'reason':'waiting for validated, reviewed implementation'}
    result = subprocess.run([sys.executable,'-B',str(ROOT/'scripts/apply_math_update.py'),
                             task_id],cwd=ROOT,capture_output=True,text=True,timeout=240)
    if result.returncode:
        return {'applied':False,'reason':'update helper failed','exit_code':result.returncode}
    return json.loads(result.stdout)


def cycle(background=False):
    task = get(f'/task/{TASK}')
    latest = latest_project_task()
    save(OUT/'latest-project-task.json', latest)
    report_path = OUT/'latest-validation.json'
    report = json.loads(report_path.read_text()) if report_path.exists() else {}
    if task['status'] == 'COMPLETE' and (not report.get('ok') or
            report.get('remote_updated_at') != task['last_updated_at']):
        report = audit_or_queue(task, background)
    reviewed = ROOT/'reference/aristotle-core-primes/reviewed-sources.json'
    accepted = json.loads(reviewed.read_text()) if reviewed.exists() else {}
    current = bool(report.get('ok') and task['status'] == 'COMPLETE' and
                   report.get('remote_updated_at') == task['last_updated_at'])
    implementation = implementation_fingerprint()
    integrated = bool(current and accepted.get('sources') == report.get('sources') and
                      accepted.get('implementation') == implementation)
    newer = latest['agent_task_id'] != TASK
    latest_report = report if not newer else {}
    if newer and latest['status'] == 'COMPLETE':
        path = validation_path(latest['agent_task_id'])
        latest_report = json.loads(path.read_text()) if path.exists() else {}
        if (not latest_report.get('ok') or
                latest_report.get('targets') != LATEST_TARGETS or
                latest_report.get('remote_updated_at') != latest['last_updated_at']):
            # Fetch the full task record for the stable-before/after capture check.
            latest = get(f"/task/{latest['agent_task_id']}")
            if latest['status'] == 'COMPLETE':
                latest_report = audit_or_queue(latest, background)
    latest_valid = bool(latest['status'] == 'COMPLETE' and latest_report.get('ok') and
                        (not newer or latest_report.get('targets') == LATEST_TARGETS) and
                        latest_report.get('task_id', TASK) == latest['agent_task_id'] and
                        latest_report.get('remote_updated_at') == latest.get('last_updated_at'))
    latest_manifest = ROOT/'reference/aristotle-rods-towers/reviewed-sources.json'
    latest_accepted = json.loads(latest_manifest.read_text()) if latest_manifest.exists() else {}
    latest_integrated = bool(latest_valid and
        latest_accepted.get('task_id') == latest['agent_task_id'] and
        latest_accepted.get('sources') == latest_report.get('sources') and
        latest_accepted.get('implementation') == implementation)
    latest_review = ('awaiting completion' if latest['status'] == 'IN_PROGRESS'
                     else ('selected math validated; pending implementation review' if latest_valid
                           else 'pending validation and implementation review')) if newer else (
                         'matches reviewed sources' if integrated else 'pending')
    if newer and latest_integrated:
        latest_review = 'matches reviewed sources'
    return {'checked_at_utc': stamp(), 'selected_task_id': TASK, 'task_status': task['status'],
            'percent_complete': task.get('percent_complete'), 'validation_ok': current,
            'implementation_review': 'matches reviewed sources' if integrated else 'pending',
            'revision': report.get('revision'), 'last_error': None,
            'latest_task_id': latest['agent_task_id'], 'latest_task_status': latest['status'],
            'latest_task_percent_complete': latest.get('percent_complete'),
            'latest_task_updated_at': latest.get('last_updated_at'),
            'latest_task_url': f'https://aristotle.harmonic.fun/projects/{PROJECT}?task=' + latest['agent_task_id'],
            'newer_project_run_detected': newer,
            'latest_task_validation_ok': latest_valid,
            'latest_task_validation_scope': list(LATEST_TARGETS if newer else TARGETS),
            'latest_task_validation_report': str(validation_path(latest['agent_task_id'])),
            'latest_task_implementation_review': latest_review}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--validate-task', help='Run one isolated proof audit and exit')
    parser.add_argument('--watch-hours', type=float, default=0)
    parser.add_argument('--watch-until', help='Fixed ISO UTC deadline; safe across login restarts')
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    if args.validate_task:
        with (OUT/'validation.lock').open('a') as lock:
            fcntl.flock(lock,fcntl.LOCK_EX | fcntl.LOCK_NB)
            try:
                report = validate(get('/task/'+args.validate_task))
                return 0 if report.get('ok') else 1
            except Exception as error:
                save(OUT/'validation-worker-error.json',{'task_id':args.validate_task,
                     'checked_at_utc':stamp(),'error':type(error).__name__+': '+str(error)})
                raise
    with (OUT/'monitor.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        deadline = (dt.datetime.fromisoformat(args.watch_until).timestamp() if args.watch_until
                    else time.time() + max(0, args.watch_hours) * 3600)
        if args.watch_until and deadline <= time.time():
            previous = json.loads((OUT/'status.json').read_text()) if (OUT/'status.json').exists() else {}
            previous.update(state='completed', monitor_finished_at_utc=stamp())
            save(OUT/'status.json', previous)
            return 0
        while True:
            cycle_started = time.monotonic()
            try:
                state = cycle(background=True)
                state["deployment"] = deploy_reviewed(state)
            except Exception as error:
                state = {'checked_at_utc': stamp(), 'last_error': type(error).__name__ + ': ' + str(error),
                         'validation_ok': False, 'implementation_review': 'pending'}
            state.update(pid=os.getpid(), interval_seconds=CHECK_INTERVAL,
                         scheduled_end_utc=dt.datetime.fromtimestamp(deadline, dt.timezone.utc).isoformat(),
                         state='running' if time.time() < deadline else 'completed')
            save(OUT/'status.json', state)
            with (OUT/'checks.jsonl').open('a') as log:
                log.write(json.dumps(state) + '\n')
            print(json.dumps(state), flush=True)
            if time.time() >= deadline:
                return 0 if state.get('validation_ok') else 1
            delay = min(max(0,CHECK_INTERVAL-(time.monotonic()-cycle_started)),max(0,deadline-time.time()))
            time.sleep(delay)
            if time.time() >= deadline:
                state.update(state='completed',monitor_finished_at_utc=stamp())
                save(OUT/'status.json',state)
                return 0


if __name__ == '__main__':
    raise SystemExit(main())
