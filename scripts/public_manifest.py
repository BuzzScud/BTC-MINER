"""Refresh reviewed public source identities without relabeling historical evidence."""
import hashlib
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT))
from btcminer.proof_evidence import verify

def main():
    verify(ROOT)
    names=json.loads((ROOT/'.github/manifests/PUBLIC_FILES.json').read_text())
    from audit_public import check_payload
    manifest={}
    for name in names:
        if name=='.github/manifests/FILES.sha256.json' or Path(name).is_absolute() or '..' in Path(name).parts:raise ValueError('Invalid inventory entry')
        raw=(ROOT/name).read_bytes();check_payload(name,raw)
        manifest[name]=hashlib.sha256(raw).hexdigest()
    (ROOT/'.github/manifests/FILES.sha256.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print('Refreshed %d reviewed source identities; no mathematical or historical acceptance changed.'%len(manifest))

if __name__=='__main__':main()
