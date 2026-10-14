"""Instantiate admitted typed integer statements on the shared abacus.

MUST check current proof source/object/axiom bindings before exposing a published
catalogue. SHALL retain domains and premises; finite executions do not replace
universal implementation proofs. MAY accept directly supplied entries in isolated
translation tests, but the public calculate path uses only verified catalogue
entries. See ../MASTER_PLAN.md PUBLISH-01 and proof_evidence.py. This code MUST NOT
control mining, modify proof status or create Bitcoin exclusion authority.
"""
import json
from . import ROOT
from .claim_calculus import ClaimCalculator


def catalogue():
    path=ROOT/'research/executable-theorems.json'
    if not path.exists():
        raise RuntimeError('The verified archive calculation catalogue has not been generated yet')
    from .proof_evidence import verify_catalogue
    return verify_catalogue(ROOT, json.loads(path.read_text()))


def instantiate(entry, values, calculator=None):
    if not entry.get('supported') or entry.get('proof_check') != 'passed':
        raise ValueError('Statement has no checked executable translation')
    if not isinstance(values,dict):
        raise ValueError('Variable assignments must be a JSON object')
    variables=entry['variables']; names=[v['name'] for v in variables]
    if len(set(names)) != len(names) or set(values) != set(names):
        raise ValueError('Supply exactly the distinct variables listed by the statement')
    for var in variables:
        x=values[var['name']]
        if type(x) is not int or (var['domain']=='Nat' and x < 0):
            raise ValueError('Variable assignment violates its integer/natural domain')
    calc=calculator or ClaimCalculator(slots=512)
    premises=[calc.decide(c,values)['truth'] for c in entry['premises']]
    applicable=all(premises)
    result=calc.decide(entry['conclusion'],values) if applicable else None
    return {'theorem':entry['theorem'],'applicable':applicable,'premises':premises,
            'result':result,'bitcoin_exclusion_authority':False,
            'scope':'A concrete instance of an archived integer statement; no SHA implication supplied'}


def calculate(name, values):
    entry=next((r for r in catalogue()['theorems'] if r['theorem']==name),None)
    if entry is None:raise ValueError('The theorem is not in the supported executable catalogue')
    return instantiate(entry,values)
