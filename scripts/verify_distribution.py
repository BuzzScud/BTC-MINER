"""Reproduce distribution contracts, affected tests and optional separate-peer demo."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from btcminer.settings import atomic_json


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--demo',action='store_true')
    args=parser.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    lean=ROOT/'.test-tools/lean-4.28.0-darwin_aarch64/bin/lean'
    source=ROOT/'btcminer/distribution/Contracts.lean'
    proof=subprocess.run([str(lean),str(source)],cwd=ROOT,capture_output=True,text=True)
    (args.output/'contracts.log').write_text(proof.stdout+proof.stderr)
    if proof.returncode:raise RuntimeError('Partition contracts did not compile')
    negative=args.output/'FalseControl.lean'
    negative.write_text('import Std.Tactic\ntheorem false_partition : (100 : Nat) = 99 := by omega\n')
    control=subprocess.run([str(lean),str(negative.resolve())],cwd=ROOT,capture_output=True,text=True)
    (args.output/'false-control.log').write_text(control.stdout+control.stderr)
    if control.returncode==0:raise RuntimeError('False proof control was accepted')
    patterns=['test_distribution.py','test_engine.py','test_pruning.py','test_scale_graph.py',
              'test_geometry_codec.py','test_geometry_predictive.py','test_provider_runtime.py',
              'test_provider_jobs.py','test_provider_boundaries.py']
    suite=unittest.TestSuite()
    for pattern in patterns:suite.addTests(unittest.defaultTestLoader.discover(str(ROOT/'tests'),pattern=pattern))
    with (args.output/'tests.log').open('w') as stream:
        result=unittest.TextTestRunner(stream=stream,verbosity=2).run(suite)
    if not result.wasSuccessful():raise RuntimeError('Affected tests failed; see tests.log')
    demo=None
    if args.demo:
        from btcminer.distribution.demo import run
        demo=run(args.output/'peer-demo',provider=True)
    files=[*sorted((ROOT/'btcminer/distribution').glob('*.py')),source,
           ROOT/'src/workers/engine.py',ROOT/'src/config/settings.py',ROOT/'src/main/cli.py',
           ROOT/'tests/test_distribution.py',Path(__file__).resolve()]
    report=dict(ok=True,tests=result.testsRun,skipped=len(result.skipped),
                contracts=sum(line.startswith('theorem ') for line in source.read_text().splitlines()),
                false_control_rejected=True,peer_demo=demo,
                scope='Scoped mathematical contracts and executable implementation tests, not whole-program formal verification',
                sources={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files})
    atomic_json(args.output/'verification.json',report)
    print(json.dumps({k:v for k,v in report.items() if k not in ('sources','peer_demo')},indent=2))


if __name__=='__main__':main()
