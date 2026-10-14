#!/usr/bin/env python3
"""User-authorized bounded rebuild of all eight referenced research modules.

This is a manual maintenance command: stops mining and restores it in finally,
except after an accepted block or a subsequent user stop. Never run unattended.
"""
import datetime as dt
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from btcminer.platform_support import fcntl
sys.path.insert(0,str(ROOT))
import monitor_aristotle_math as m
from btcminer import service
from btcminer.settings import LOGS


def run(command,cwd,env,log,deadline,limit=180):
    remaining=min(limit,deadline-time.monotonic())
    if remaining <= 0:return 124
    with log.open('w') as stream:
        child=subprocess.Popen(command,cwd=cwd,env=env,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
        try:
            return child.wait(timeout=remaining)
        except subprocess.TimeoutExpired:
            os.killpg(child.pid,signal.SIGKILL)
            child.wait()
            stream.write('\nRESOURCE LIMIT: bounded rebuild timeout.\n')
            return 124
        finally:
            if child.poll() is None:
                os.killpg(child.pid,signal.SIGKILL);child.wait()


def main():
    out=ROOT/'validation/miner-full-rebuild'
    out.mkdir(exist_ok=True)
    before=service.status()
    if before.get('blocks_accepted',0):
        raise RuntimeError('Accepted block in current/last session: automatic mining restoration is not allowed')
    if before.get('running'):service.stop(summary=False)
    stop_file=LOGS/'stop.request'
    stop_stamp=stop_file.stat().st_mtime_ns if stop_file.exists() else None
    report={'started_at_utc':m.stamp(),'budget_seconds':900,'lean_memory_limit_mb':3072,
            'task_id':'135b05b0-bc03-413d-9a18-5a0a1af1df7a',
            'targets':m.LATEST_TARGETS,'builds':[],'ok':False,
            'scope':'All eight miner-referenced Aristotle modules and their complete local import closure; not every unrelated module in the research project.'}
    deadline=time.monotonic()+900
    try:
        with (m.OUT/'validation.lock').open('a') as lock:
            fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
            m.save(m.OUT/'active-validation.json',{'pid':os.getpid(),'identity':m.process_identity(os.getpid()),
                  'task_id':report['task_id'],'manual_bounded_audit':True,'started_at_utc':m.stamp()})
            prior=json.loads(m.validation_path(report['task_id']).read_text())
            source=out/'sources'
            original=Path(prior['revision'])/'sources'
            for relative,digest in prior['sources'].items():
                assert m.sha(original/relative)==digest
                dest=source/relative;dest.parent.mkdir(parents=True,exist_ok=True)
                shutil.copy2(original/relative,dest)
            report['sources']=prior['sources']
            task=m.get('/task/'+report['task_id'])
            assert task['status']=='COMPLETE' and task['last_updated_at']==prior['remote_updated_at']
            report['remote_updated_at']=task['last_updated_at']
            report['task_status']='COMPLETE'
            report['revision']=str(out)
            env=dict(os.environ,PATH=str(m.BIN)+os.pathsep+os.environ['PATH'],PYTHONDONTWRITEBYTECODE='1',LC_ALL='C')
            for tool in ('lean','lake'):
                report[tool+'_version']=subprocess.check_output([str(m.BIN/tool),'--version'],env=env,text=True).strip()
            deps=subprocess.check_output([str(m.BIN/'lake'),'env','printenv','LEAN_PATH'],cwd=m.PINNED,env=env,text=True).strip()
            paths=[str((m.PINNED/p).resolve()) if not Path(p).is_absolute() else p for p in deps.split(os.pathsep)]
            env['LEAN_PATH']=str(source)+os.pathsep+os.pathsep.join(paths)
            report['dependency_manifest_sha256']=m.sha(m.PINNED/'lake-manifest.json')
            cached=m.cached_success(report,{})
            order=[];dependencies={}
            def visit(module):
                if module in order:return
                relative=module.replace('.','/')+'.lean'
                dependencies[module]=[d for d in re.findall(r'^(?:public )?import ([\w.]+)',(source/relative).read_text(),re.M)
                                      if d.startswith(('RequestProject.','LatticeCalc.'))]
                for dep in dependencies[module]:visit(dep)
                order.append(module)
            # Check independent shell/density results before expensive circle proofs.
            priority=['RequestProject.ShellEnrichment','RequestProject.BaseDensity']+m.LATEST_TARGETS
            for module in priority:visit(module)
            passed={};reusable={}
            for module in order:
                if service.supervisor_running():
                    raise RuntimeError('User restarted mining during maintenance; proof audit stopped')
                relative=module.replace('.','/')+'.lean'
                artifact=source/relative
                old=Path(cached.get('revision',''))/'sources'/relative
                can_reuse=(cached.get('sources',{}).get(relative)==report['sources'][relative] and
                           all(reusable.get(d,False) for d in dependencies[module]) and old.with_suffix('.olean').exists())
                reusable[module]=can_reuse
                if can_reuse:
                    for path in old.parent.glob(old.stem+'.olean*'):shutil.copy2(path,artifact.parent/path.name)
                    if old.with_suffix('.ir').exists():shutil.copy2(old.with_suffix('.ir'),artifact.with_suffix('.ir'))
                    result={'module':module,'exit_code':0,'reused_validated_artifact':True,'from_revision':cached['revision']}
                elif any(not passed.get(d,False) for d in dependencies[module]):
                    result={'module':module,'exit_code':None,'failure_kind':'dependency_failed'}
                else:
                    log=out/(module+'.log')
                    code=run([str(m.BIN/'lean'),'-j1','-M3072','-o',str(artifact.with_suffix('.olean')),relative],source,env,log,deadline)
                    text=log.read_text() if log.exists() else ''
                    result={'module':module,'exit_code':code,'log':str(log)}
                    if code:result['failure_kind']='resource_limit' if code==124 or 'memory_exception' in text or 'excessive memory consumption' in text else 'lean_build_error'
                passed[module]=result['exit_code']==0
                report['builds'].append(result)
                m.save(out/'report.json',report)
                print(json.dumps(result),flush=True)
            targets=[name for name in m.LATEST_TARGETS if passed.get(name)]
            report['passed_targets']=targets
            template=(ROOT/'validation/math-audit/AxiomUnion.lean').read_text()
            body=template[template.index('  let indices :='):]
            driver=source/'Audit.lean'
            driver.write_text('\n'.join('import '+name for name in targets)+'\nopen Lean Elab Command\ndef auditEnv (env : Environment) (mods : Array Name) : IO Unit := do\n'+body+'\nrun_cmd do\n  liftIO <| auditEnv (← getEnv) #['+', '.join('`'+name for name in targets)+']\n')
            code=run([str(m.BIN/'lean'),'-j1','-M3072',str(driver)],source,env,out/'axioms.tsv',deadline,120)
            lines=(out/'axioms.tsv').read_text().splitlines() if (out/'axioms.tsv').exists() else []
            axioms=sorted(x.split('\t')[1] for x in lines if x.startswith('axiom\t'))
            report.update(axiom_audit_exit_code=code,axioms=axioms,theorem_count=sum(x.startswith('theorem\t') for x in lines))
            tests=run([sys.executable,'-B','-m','unittest','discover','-s','tests','-v'],ROOT,env,out/'miner-tests.log',deadline,180)
            report['miner_tests_exit_code']=tests
            report['ok']=(len(targets)==len(m.LATEST_TARGETS) and code==0 and tests==0 and report['theorem_count']>0 and set(axioms)<={'propext','Classical.choice','Quot.sound'})
            report['completed_at_utc']=m.stamp()
            m.save(out/'report.json',report)
            if report['ok']:m.save(m.validation_path(report['task_id']),report)
    except Exception as error:
        report['error']=type(error).__name__+': '+str(error)
        print(report['error'],flush=True)
    finally:
        current=service.status()
        current_stamp=stop_file.stat().st_mtime_ns if stop_file.exists() else None
        if current.get('blocks_accepted',0):
            report['mining_restoration']='not restarted: accepted block'
        elif current.get('running'):
            report['mining_restoration']='already running'
        elif current_stamp!=stop_stamp:
            report['mining_restoration']='not restarted: user stop changed during audit'
        elif not before.get('running'):
            report['mining_restoration']='left stopped: mining was stopped before maintenance'
        else:
            try:
                started=service.start()
                report['mining_restoration']={'running':started.get('running'),'pid':started.get('pid')}
            except Exception as error:
                report['mining_restoration']={'error':str(error)}
        report['finished_at_utc']=m.stamp()
        m.save(out/'report.json',report)
        print(json.dumps({'ok':report['ok'],'mining_restoration':report['mining_restoration']}),flush=True)
    return 0 if report['ok'] else 1

if __name__=='__main__':raise SystemExit(main())
