#!/usr/bin/env python3
"""Publish supported typed translations only after current proof admission.

MUST verify source, object and allowed-axiom evidence with proof_evidence.verify.
MUST retain all hypotheses/domains; SHALL reject old theorem-name-only logs and
unrecognized syntax. MAY publish proof-only registry entries separately. These
five closed product instances have no Bitcoin exclusion authority and do not
constitute universal C/Python refinement. See ../MASTER_PLAN.md PROOF-01/PUBLISH-01.
This workflow updates research metadata only; it never controls a miner or node.
"""
import argparse,hashlib,json,os,sys
from datetime import datetime,timezone
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from btcminer.proof_evidence import verify,constant_product_entries,verify_catalogue
from btcminer.theorem_calculations import instantiate
from btcminer.claim_calculus import ClaimCalculator


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=ROOT)
    args=parser.parse_args();root=args.root.resolve()
    evidence=verify(root);entries=constant_product_entries(root,evidence)
    calculator=ClaimCalculator(slots=64)
    for entry in entries:
        result=instantiate(entry,{},calculator)
        if not result['applicable'] or result['result']['truth'] is not True:
            raise ValueError('Native translation check failed: '+entry['theorem'])
        entry['instance_checks']=1;entry['instance_check_passed']=True
    catalogue={'schema':2,'status':'accepted_scoped_translations','count':len(entries),
               'created_at_utc':datetime.now(timezone.utc).isoformat(),
               'proof_manifest_sha256':evidence['manifest_sha256'],
               'scope':'Closed Nat multiplication equalities with current kernel proof evidence; native translation checked on every admitted instance. Other accepted theorems are proof-only, not guessed executable translations. No Bitcoin exclusion authority.',
               'theorems':entries}
    verify_catalogue(root,catalogue,evidence)
    target=root/'research/executable-theorems.json'
    if target.exists():
        old=hashlib.sha256(target.read_bytes()).hexdigest()
        history=root/'research/registry-history';history.mkdir(parents=True,exist_ok=True)
        (history/('executable-theorems-'+old+'.json')).write_bytes(target.read_bytes())
    temporary=target.with_suffix('.json.pending')
    temporary.write_text(json.dumps(catalogue,indent=2)+'\n');os.replace(temporary,target)
    print(json.dumps({'published':len(entries),'proof_manifest_sha256':evidence['manifest_sha256'],
                      'scope':catalogue['scope']}))

if __name__=='__main__':main()
