"""Check the exact Git index against the reviewed public inventory; print no content."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT=Path(__file__).resolve().parent.parent
FORBIDDEN=re.compile(r'(^|/)(?:\.env(?:\..*)?|machine\.local\.json|network-profiles\.local\.json|wallet\.dat|\.cookie|\.venv|\.build|\.test-tools|logs|wallets|node)(/|$)|\.(?:pem|key|sqlite(?:-.*)?|db|pyc|dylib|dll|so)$',re.I)
PATTERNS=[rb'-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----',
          rb'gh[pousr]_[A-Za-z0-9]{30,}',rb'github_pat_[A-Za-z0-9_]{30,}',rb'AKIA[A-Z0-9]{16}']

def check_payload(name,raw):
    if FORBIDDEN.search(name): raise ValueError('Private/operational path in public inventory: '+name)
    if any(re.search(pattern,raw) for pattern in PATTERNS):raise ValueError('Credential marker detected in '+name)

def main():
    p=argparse.ArgumentParser();p.add_argument('--worktree',action='store_true');args=p.parse_args()
    def read(name):
        return (ROOT/name).read_bytes() if args.worktree else subprocess.check_output(['git','show',':'+name],cwd=ROOT)
    names=json.loads(read('PUBLIC_FILES.json'))
    expected=set(names)|{'FILES.sha256.json'}
    if not args.worktree:
        rows=subprocess.check_output(['git','ls-files','--stage','-z'],cwd=ROOT).decode().split('\0')
        actual=set()
        for row in filter(None,rows):
            meta,name=row.split('\t',1)
            if meta.split()[0] not in ('100644','100755'):raise ValueError('Unexpected Git object type: '+name)
            actual.add(name)
        if actual!=expected:raise ValueError('Staged paths differ from public inventory: '+str(sorted(actual^expected)))
    manifest=json.loads(read('FILES.sha256.json'))
    if set(manifest)!=set(names):raise ValueError('Source hash inventory differs')
    total=0
    for name in sorted(expected):
        path=Path(name)
        if path.is_absolute() or '..' in path.parts:raise ValueError('Unsafe public path')
        raw=read(name);check_payload(name,raw);total+=len(raw)
        if name in manifest and hashlib.sha256(raw).hexdigest()!=manifest[name]:raise ValueError('Unreviewed bytes: '+name)
    print(json.dumps({'ok':True,'files':len(expected),'bytes':total,'scope':'Exact public inventory and credential markers; also run Gitleaks and manual review'}))

if __name__=='__main__':main()
