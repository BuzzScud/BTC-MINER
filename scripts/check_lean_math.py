#!/usr/bin/env python3
"""Rebuild the unmodified Lean sources embedded in the supplied HTML."""
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'validation/math-audit'
LEAN=ROOT/'.test-tools/lean-4.34.0-darwin_aarch64/bin/lean'
SRC=OUT/'lean-check-extracted'
env=dict(os.environ,LEAN_PATH=str(SRC),PATH=str(LEAN.parent)+os.pathsep+os.environ.get('PATH',''))
results=[]
# --resume reuses only previously successful exact-version source builds.
prior_path=OUT/'lean-build.json'
prior=json.loads(prior_path.read_text()) if '--resume' in sys.argv and prior_path.exists() else {}
version=subprocess.check_output([str(LEAN),'--version'],text=True).strip()
def save():
    prior_path.write_text(json.dumps(dict(lean_version=version,
        time_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),results=results,
        passed=len(results)==15 and all(r['exit_code']==0 for r in results)),indent=2)+'\n')
paths=sorted((SRC/'Thesis2').glob('*.lean'))
# The grid census is expensive. Check independent modules first; the 4D
# module depends on it and must remain after it.
paths=[p for p in paths if p.stem not in ('T03Grids','T10Pack4D')]+[SRC/'Thesis2/T03Grids.lean',SRC/'Thesis2/T10Pack4D.lean']
for p in paths:
    from hashlib import sha256
    digest=sha256(p.read_bytes()).hexdigest()
    previous=next((r for r in prior.get('results',[]) if r.get('module')=='Thesis2.'+p.stem),None)
    if prior.get('lean_version')==version and previous and previous.get('exit_code')==0 and previous.get('sha256')==digest and p.with_suffix('.olean').exists():
        results.append(previous);save();continue
    start=time.monotonic()
    try:
        run=subprocess.run([str(LEAN),'-o',str(p.with_suffix('.olean')),str(p.relative_to(SRC))],
                           cwd=SRC,env=env,capture_output=True,text=True,timeout=1800)
        output=run.stdout+run.stderr;code=run.returncode
    except subprocess.TimeoutExpired as e:
        output='RESOURCE LIMIT: independent build exceeded 1800 seconds for this module.\n'
        for value in (e.stdout,e.stderr):
            if value:output+=value.decode() if isinstance(value,bytes) else value
        code=124
    (OUT/(p.stem+'.build.log')).write_text(output)
    result=dict(module='Thesis2.'+p.stem,exit_code=code,sha256=digest,
                elapsed_seconds=time.monotonic()-start,log=p.stem+'.build.log')
    results.append(result)
    save()
    print(json.dumps(result),flush=True)
audit=OUT/'ForensicAudit-local.lean'
if all(r['exit_code']==0 for r in results):
    run=subprocess.run([str(LEAN),'--run',str(audit)]+[r['module'] for r in results],
                       cwd=SRC,env=env,capture_output=True,text=True,timeout=600)
    (OUT/'embedded-proof-inventory.tsv').write_text(run.stdout)
    (OUT/'embedded-axiom-audit.log').write_text(run.stderr)
    results.append(dict(stage='axiom_inventory',exit_code=run.returncode))
summary=dict(lean_version=version,
             time_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),results=results,
             passed=all(r['exit_code']==0 for r in results))
(OUT/'lean-build.json').write_text(json.dumps(summary,indent=2)+'\n')
raise SystemExit(0 if summary['passed'] else 1)
