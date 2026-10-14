#!/usr/bin/env python3
"""MUST verify immutable proof artifacts and current sources before publication.

This read-only gate SHALL NOT run Lean, mining, node commands or provider calls.
See ../MASTER_PLAN.md RELEASE-01/PROOF-01 and btcminer/proof_evidence.py.
"""
import argparse,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from btcminer.proof_evidence import verify

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=ROOT)
    args=parser.parse_args()
    result=verify(args.root)
    print(json.dumps({k:result[k] for k in ['status','manifest_sha256','theorem_count','named_theorem_count','objects_checked','scope']}))
    return 0

if __name__=='__main__':raise SystemExit(main())
