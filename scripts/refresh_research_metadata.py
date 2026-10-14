#!/usr/bin/env python3
"""Reconcile current source metadata without upgrading unproved claims.

MUST first validate the accepted kernel capsule and executable catalogue. SHALL
preserve old registries/manifests by content hash, keep evidence scope separate
from current file identity, and retain every provider coverage gap verbatim.
MAY snapshot a neighbouring observatory ledger as external research context;
that is not imported proof acceptance. No miner/node/session control is allowed.
See ../MASTER_PLAN.md ARCHIVE-01, PROOF-01, PUBLISH-01 and RELEASE-01.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from btcminer import VERSION
from btcminer.proof_evidence import verify, verify_catalogue
from build import release_files


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_preserved(root, relative, value):
    path = root / relative
    content = (json.dumps(value, indent=2, sort_keys=False) + '\n').encode()
    if path.exists():
        old = path.read_bytes()
        if old == content:
            return
        archive = root/'research/registry-history'/(path.stem+'-'+hashlib.sha256(old).hexdigest()+'.json')
        archive.parent.mkdir(parents=True, exist_ok=True)
        if not archive.exists():
            archive.write_bytes(old)
    path.parent.mkdir(parents=True, exist_ok=True)
    pending = path.with_suffix('.json.pending')
    pending.write_bytes(content)
    os.replace(pending, path)


def refresh(root, observatory=None):
    root = Path(root).resolve()
    proof = verify(root)
    catalogue = verify_catalogue(root, json.loads((root/'research/executable-theorems.json').read_text()), proof)
    supported = {entry['theorem'] for entry in catalogue['theorems']}
    entries = [{'theorem':name, 'module':module, 'proof_status':'accepted_scoped_kernel_statement',
                'source':'validation/miner-proof-repair-20261007/sources/'+module.replace('.', '/')+'.lean',
                'source_sha256':proof['source_manifest']['sources'][module.replace('.', '/')+'.lean'],
                'axioms':proof['theorem_roots'][name]['axioms'],
                'execution_status':'accepted_closed_Nat_translation' if name in supported else 'proof_only_translation_unimplemented',
                'bitcoin_exclusion_authority':False}
               for module,names in proof['required_named_theorems'].items() for name in names]
    registry = {'schema':1, 'status':'accepted_scoped_statements',
                'proof_manifest_sha256':proof['manifest_sha256'],
                'audited_root_count':proof['theorem_count'], 'named_theorem_count':len(entries),
                'executable_translation_count':len(supported), 'theorems':entries,
                'scope':proof['scope'], 'unproved_claims':'research/claims.json is unchanged; neither runtime refinement nor SHA search reduction follows.',
                'external_provider_coverage':'research/provider-coverage-ledger.json (context snapshot, not miner proof admission)'}
    # Cross-project receipts are navigation context only. Their compiler objects
    # remain under their own gate; never add these roots to miner admission.
    prior_registry = root/'research/proof-registry.json'
    registry['external_receipt_context'] = (json.loads(prior_registry.read_text()).get('external_receipt_context', [])
                                            if prior_registry.exists() else [])
    supplement = root.parent/'calculator-fix-kit-2026-10-06/lean-values/remaining-proof-work-20261007'
    if (supplement/'review.json').is_file() and (supplement/'proof-results.json').is_file():
        reviewed = json.loads((supplement/'review.json').read_text())
        receipt = json.loads((supplement/'proof-results.json').read_text())
        if reviewed.get('proof_receipt_sha256') != digest(supplement/'proof-results.json'):
            raise ValueError('External supplement review receipt binding differs')
        reference = {'project':'calculator_remaining_finite_outputs',
            'status':'external_receipt_reference_not_miner_admission',
            'receipt':str(supplement/'proof-results.json'), 'receipt_sha256':digest(supplement/'proof-results.json'),
            'review':str(supplement/'review.json'), 'review_sha256':digest(supplement/'review.json'),
            'reported_receipt_status':receipt.get('status'), 'reported_review_status':reviewed.get('status'),
            'reported_checked_roots':receipt.get('checked_roots'),
            'reported_historical_gap_count':receipt.get('historical_gap_count'),
            'reported_newly_checked_case_count':receipt.get('newly_checked_case_count'),
            'reported_remaining_unproved_case_count':receipt.get('remaining_unproved_case_count'),
            'whole_implementation_verified':False,
            'scope':'Referenced external finite-output supplement. This registry checks the receipt/review identity only; current source/object/axiom reconciliation remains owned by its separate review.py gate.'}
        registry['external_receipt_context'] = [r for r in registry['external_receipt_context'] if r.get('project') != reference['project']] + [reference]
    write_preserved(root, 'research/proof-registry.json', registry)
    if observatory is not None:
        ledger = Path(observatory)/'catalogue-study/proofs/coverage-ledger.json'
        raw = ledger.read_bytes()
        coverage = json.loads(raw)
        if coverage.get('provider_implementation_formally_verified') is not False:
            raise ValueError('Provider coverage scope requires explicit review')
        write_preserved(root, 'research/provider-coverage-ledger.json', coverage)
        write_preserved(root, 'research/provider-coverage-reference.json', {
            'schema':1, 'status':'external_scope_snapshot_not_proof_admission',
            'source':str(ledger), 'source_sha256':hashlib.sha256(raw).hexdigest(),
            'snapshot_sha256':digest(root/'research/provider-coverage-ledger.json'),
            'scope':'Formula-specific domains, finite results and remaining gaps retained verbatim. Fresh proof acceptance remains in the observatory gate.'})
    ledger = json.loads((root/'research/integration-status.json').read_text())
    ledger['as_of'] = datetime.now(timezone.utc).isoformat()
    ledger['miner_version'] = VERSION
    ledger['meaning'] = ('Added means present in current source, not loaded by the running process. Current source hashes are identity metadata; historical evidence is not silently revalidated. Mathematical acceptance is separately source/object/axiom bound.')
    for entry in ledger['items']:
        entry.setdefault('historical_source_sha256', entry.get('current_source_sha256', {}).copy())
        entry['current_source_sha256'] = {name:digest(root/name) for name in entry.get('source', [])}
        entry['evidence_status'] = 'historical_scoped_evidence; current file identity does not extend its validity'
        if entry['finding'] == 'Expanded whole selected-module Lean rebuild':
            entry['status'] = 'historical_incomplete; three_blockers_repaired_separately'
            entry['use'] = ('The old eight-target audit remains historical. Its three failed targets now pass the separate raw/Lake repair capsule; other five top-level targets were outside that replay.')
    finding = 'Current source/object/axiom bound repair and publication gate'
    ledger['items'] = [entry for entry in ledger['items'] if entry['finding'] != finding]
    sources = ['btcminer/proof_evidence.py', 'btcminer/theorem_calculations.py', 'scripts/build.py',
               'scripts/publish_archive_calculations.py', 'research/proof-registry.json']
    ledger['items'].append({'finding':finding, 'status':'accepted_scoped_kernel_evidence',
        'use':f"{proof['theorem_count']} audited roots; {len(entries)} named statements; {len(supported)} supported exact scalar translations. Unimplemented translations and other research gaps retained.",
        'source':sources, 'current_source_sha256':{name:digest(root/name) for name in sources},
        'evidence':'research/proof-evidence/manifest.json', 'evidence_status':'verified_current_mathematical_sources_and_retained_objects',
        'proof_manifest_sha256':proof['manifest_sha256']})
    write_preserved(root, 'research/integration-status.json', ledger)
    names = release_files(root, proof)
    write_preserved(root, 'FILES.sha256.json', {name:digest(root/name) for name in names})
    return {'status':'refreshed', 'files':len(names), 'named_theorems':len(entries), 'executable_translations':len(supported),
            'live_process_restarted':False, 'proof_manifest_sha256':proof['manifest_sha256']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--observatory', type=Path)
    args = parser.parse_args()
    print(json.dumps(refresh(args.root, args.observatory)))

if __name__ == '__main__':
    main()
