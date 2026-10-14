#!/usr/bin/env python3
"""Apply a completed, reviewed math revision to an actively mining session."""
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from btcminer import service
from btcminer.mathrevision import fingerprint
from monitor_aristotle_math import LATEST_TARGETS, OUT, save, stamp, validation_path


def apply(task_id):
    report = json.loads(validation_path(task_id).read_text())
    manifest = json.loads((ROOT/'reference/aristotle-rods-towers/reviewed-sources.json').read_text())
    implementation = fingerprint()
    if not (report.get('ok') and report.get('task_status') == 'COMPLETE' and
            report.get('task_id') == task_id == manifest.get('task_id') and
            report.get('targets') == LATEST_TARGETS and
            report.get('sources') == manifest.get('sources') and
            manifest.get('implementation') == implementation):
        return {'applied':False, 'reason':'formal validation or implementation review pending'}
    before = service.status()
    if not before.get('running') or before.get('state') != 'MINING' or before.get('blocks_accepted',0):
        return {'applied':False, 'reason':'not actively mining or block already accepted'}
    if before.get('math_implementation') == implementation:
        return {'applied':False, 'reason':'already loaded'}
    with (OUT/'pre-apply-tests.log').open('w') as log:
        tests = subprocess.run([sys.executable,'-B','-m','unittest','discover','-s','tests'],
                               cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,timeout=180)
    if tests.returncode:
        return {'applied':False, 'reason':'pre-apply regression failed; miner untouched'}
    return service.restart_for_math(before['pid'],implementation)


if __name__ == '__main__':
    try:
        result = apply(sys.argv[1])
    except Exception as error:
        result = {'applied':False,'reason':type(error).__name__+': '+str(error)}
    result.update(task_id=sys.argv[1],checked_at_utc=stamp())
    save(OUT/'deployment.json',result)
    print(json.dumps(result),flush=True)
