"""Verify unchanged mathematical bytes and selected arithmetic ASTs from the import."""
import ast
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent.parent

def definitions(source):
    result={}
    def visit(nodes,prefix=''):
        for node in nodes:
            if isinstance(node,(ast.FunctionDef,ast.AsyncFunctionDef,ast.ClassDef)):
                name=prefix+node.name
                if isinstance(node,ast.ClassDef):visit(node.body,name+'.')
                else:result[name]=hashlib.sha256(ast.dump(node,include_attributes=False).encode()).hexdigest()
    visit(ast.parse(source).body)
    return result

def main():
    manifest=json.loads((ROOT/'research/math-preservation.json').read_text())
    for name,expected in manifest['unchanged_files'].items():
        if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=expected:raise ValueError('Mathematical source changed: '+name)
    count=0
    for name,functions in manifest['unchanged_functions'].items():
        actual=definitions((ROOT/name).read_text())
        for function,expected in functions.items():
            if actual.get(function)!=expected:raise ValueError('Arithmetic function changed: '+name+':'+function)
            count+=1
    print(json.dumps({'ok':True,'unchanged_files':len(manifest['unchanged_files']),'unchanged_functions':count,
                      'scope':'Source preservation and executable checks, not whole-program formal verification'}))

if __name__=='__main__':main()
