"""Materialize/check identical compatibility paths; works without symlink privileges."""
import argparse,json,shutil
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
def sync(check=False):
    for entry in json.loads((ROOT/'docs/project-layout.json').read_text())['files']:
        source=ROOT/entry['source_path']; target=ROOT/entry['compatibility_path']
        if check:
            if target.read_bytes()!=source.read_bytes(): raise ValueError('Layout mismatch: '+entry['compatibility_path'])
        else:
            target.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(source,target)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');sync(p.parse_args().check)
