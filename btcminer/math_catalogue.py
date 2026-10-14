"""Source-bound discovery catalogue; provider labels never grant proof acceptance."""
from collections import Counter
import hashlib
import json
from pathlib import Path
from . import ROOT


def catalogue(root=ROOT, query=None):
    root=Path(root)
    ref=json.loads((root/'research/math-catalogue-reference.json').read_text())
    if ref.get('schema')!='miner-math-catalogue-reference-v1':
        raise ValueError('Unsupported formula catalogue reference')
    path=root/'research/formula-catalogue.json'; raw=path.read_bytes()
    if hashlib.sha256(raw).hexdigest()!=ref.get('catalogue_sha256'):
        raise ValueError('Formula catalogue differs from its reviewed source snapshot')
    data=json.loads(raw); records=data['formulas']
    if (data.get('schema')!='provider-formula-inventory-v1' or
        len(records)!=ref['formula_count'] or len(records)!=data['total_available'] or
        len({r['id'] for r in records})!=len(records) or
        len({r['name'] for r in records})!=len(records)):
        raise ValueError('Incomplete or duplicate formula inventory')
    if query is not None and not isinstance(query,str):raise TypeError('Query must be text')
    selected=records if query is None else [r for r in records if query.casefold() in
        '\n'.join(r[k] for k in ('name','expression','specification','notes')).casefold()]
    result={'formula_count':len(records),'matched_count':len(selected),
            'provider_status_counts':dict(Counter(r['status'] for r in records)),
            'catalogue_sha256':ref['catalogue_sha256'],'captured_at':data['captured_at'],
            'catalogue_path':str(path),'workspace_cards':str(root/ref['workspace_cards']),
            'workspace_cards_available':(root/ref['workspace_cards']).is_file(),
            'selected_sources':str(root/ref['selected_sources']),
            'scope':data['scope'],'proof_acceptance_from_provider_records':False}
    if query is not None:result['formulas']=selected
    mapping=root/'research/math-consumers.json'
    if mapping.is_file():
        payload=mapping.read_bytes()
        if hashlib.sha256(payload).hexdigest()!=ref.get('consumer_map_sha256'):
            raise ValueError('Consumer map differs from its reviewed source snapshot')
        result['consumer_map']=json.loads(payload)
    return result
