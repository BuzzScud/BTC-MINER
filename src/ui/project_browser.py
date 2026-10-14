"""Offline project inventory and HTML browser. Never controls the miner.

All directory entries are indexed without following symbolic links. Only selected
source/documentation files get embedded text previews; operational files remain
metadata-only. Manifest comparisons are identity checks, not proof admission.
"""
import hashlib
import json
import os
from pathlib import Path
import shlex
import stat
import tempfile
import time
from datetime import datetime, timezone
import webbrowser

MARKER = '<!doctype html><!-- BTC MINER PROJECT BROWSER v1 -->'
STATE_NAME = '.project-browser-state.json'
TEXT_LIMIT = 64 * 1024
PREVIEW_BUDGET = 4 * 1024 * 1024
# Navigation ownership, not a claim that every research artifact is runtime code.
# SHA-256 scheduling, pruning and protocol consumers stay on the miner side.
MATH_MODULES = frozenset('''abacus abacus_lab archive_math capacity_reals claim_calculus
coreprimes exact_tower math_catalogue mathrevision pqmath prime_structure
product_tree_crt proof_evidence recurrence research_system rodmath scaled_abacus
shared_abacus theorem_calculations'''.split())
MATH_TESTS = MATH_MODULES | frozenset('''archive_calculations aristotle_monitor
hex_distance math_boundaries math_update_apply math_update_service resident_abacus
scaled_integration strict_audit'''.split())
MATH_SCRIPTS = frozenset('''abacus_sha_lab audit_archive_search benchmark_resident_abacus
capacity_real_report capture_archive_audit check_aristotle_math check_aristotle_rod_sieve
check_aristotle_updates check_lean_math check_miner_math_lean export_proof_evidence
geometry_audit math_audit monitor_aristotle_math prepare_archive_proofs
publish_archive_calculations refresh_research_metadata render_abacus_sha_lab
render_archive_audit study_qk_controls summarize_archive_proofs test_abacus_constraints
validate_shared_abacus_proofs verify_proof_evidence'''.split())
MATH_AUDITS = ('aristotle-', 'archive-audit', 'coprime-chain-', 'ellipse-rods',
               'flower-real-', 'math-', 'miner-lean-', 'miner-math-', 'miner-proof-',
               'resident-abacus', 'shared-abacus')


def project_part(relative):
    """Assign every file exactly once: 1 = math, 2 = miner/supporting files.

    Mixed directories appear in both browser panes with their respective children.
    New uncategorized implementation files default to supporting files until reviewed.
    """
    p = Path(relative)
    parts = p.parts
    if not parts:
        return 2
    top = parts[0]
    if top in ('research', 'reference', 'math-library'):
        return 1
    if top == 'btcminer' and len(parts) == 2 and p.stem in MATH_MODULES:
        return 1
    if top == 'native' and (parts[1:2] == ('latcalc',) or p.name in
            {'build_abacus.sh', 'build_rodsieve.sh', 'libabacus.dylib', 'librodsieve.dylib'}):
        return 1
    if top == 'tests' and p.stem.removeprefix('test_') in MATH_TESTS:
        return 1
    if top == 'scripts' and p.stem in MATH_SCRIPTS:
        return 1
    if top == 'validation' and len(parts) > 1:
        if parts[1].startswith('api-library-completion-'):
            return 1 if len(parts) > 2 and parts[2] in ('audit', 'library') else 2
        if parts[1].startswith(MATH_AUDITS):
            return 1
    if top not in {'.test-tools', 'logs', 'dist'} and p.suffix in {'.lean', '.olean', '.ilean'}:
        return 1
    if len(parts) == 1 and p.name.startswith(('MATH-', 'GEOMETRY-', 'ARISTOTLE-')):
        return 1
    return 2


DESCRIPTIONS = {
    'src': 'Miner source: main, config, pool, hash, workers, backends, stats and UI',
    'math-library': 'Exact Python mathematics and native C arithmetic',
    'btcminer': 'Mining application and exact arithmetic library',
    'native': 'C hashing engine and native arithmetic',
    'research': 'Formula catalogue, consumers and proof registry',
    'reference': 'Retained Aristotle reference sources',
    'validation': 'Versioned audits, proof artifacts and test evidence',
    'tests': 'Offline regression tests',
    'scripts': 'Build, diagnostic and research tools',
    'logs': 'Local runtime logs and status',
    'dist': 'Packaged releases',
    'reports': 'Reports and exports',
    'docs': 'Design documents',
    'bin': 'Miner launch and control commands',
    '.test-tools': 'Local test tools and their dependencies',
}


def _safe_relative(name):
    p = Path(name)
    return bool(name) and not p.is_absolute() and '..' not in p.parts


def _preview_allowed(relative):
    p = Path(relative)
    if p.suffix.lower() not in {'.py', '.c', '.h', '.lean', '.md', '.txt', '.sh'}:
        return False
    if any(word in p.name.lower() for word in ('secret', 'credential', 'cookie', '.local.')):
        return False
    return (len(p.parts) == 1 or p.parts[0] in
            {'src', 'math-library', 'btcminer', 'native', 'tests', 'scripts', 'docs', 'reference'})


def _atomic(path, content):
    fd, pending = tempfile.mkstemp(prefix='.project-browser-', dir=path.parent)
    try:
        with os.fdopen(fd, 'w', encoding='utf-8') as stream:
            stream.write(content)
        os.replace(pending, path)
    finally:
        if os.path.exists(pending):
            os.unlink(pending)


def inventory(root, *, excluded=(), previous=None):
    root = Path(root).resolve()
    excluded = {str(Path(p).absolute()) for p in excluded}
    previous = previous or {}
    old = previous.get('files', {}) if previous.get('root') == str(root) else {}
    prior = bool(previous) and previous.get('root') == str(root)
    manifest = {}
    issues = []
    aliases = {}
    layout_path = root / 'docs/project-layout.json'
    if layout_path.is_file() and not layout_path.is_symlink():
        try:
            layout = json.loads(layout_path.read_text())
            if layout.get('schema') != 'btc-project-layout/v1':
                raise ValueError('Unknown project layout')
            for entry in layout['files']:
                old_path, new_path = entry['compatibility_path'], entry['source_path']
                if (not _safe_relative(old_path) or not _safe_relative(new_path) or
                        Path(new_path).parts[0] not in ('src', 'math-library')):
                    raise ValueError('Invalid compatibility path')
                aliases[old_path] = new_path
        except (OSError, ValueError, KeyError, TypeError) as error:
            issues.append('Project layout unavailable: ' + str(error))
            aliases = {}
    manifest_path = root / 'FILES.sha256.json'
    try:
        if manifest_path.is_symlink():
            raise ValueError('Manifest is a symbolic link')
        if manifest_path.exists():
            manifest = json.loads(manifest_path.read_text())
            if not isinstance(manifest, dict) or any(
                not isinstance(k, str) or not _safe_relative(k) or
                not isinstance(v, str) or len(v) != 64 or
                any(c not in '0123456789abcdef' for c in v) for k, v in manifest.items()
            ):
                raise ValueError('Invalid manifest format')
    except (OSError, ValueError) as error:
        issues.append('Release manifest unavailable: ' + str(error))
        manifest = {}
    # Rows: parent index, name, kind, bytes, modification time, change status, part.
    rows = [[-1, root.name, 'directory', 0, 0, '', 2]]
    paths = {'': 0}
    current, hashes, previews, checks = {}, {}, {}, {}
    remaining = PREVIEW_BUDGET
    stack = [(root, '', 0)]
    while stack:
        directory, prefix, parent = stack.pop()
        try:
            with os.scandir(directory) as it:
                entries = sorted(it, key=lambda e: e.name.casefold())
        except OSError as error:
            issues.append(prefix + ': ' + str(error))
            rows[parent][5] = 'unreadable'
            continue
        descend = []
        for entry in entries:
            if entry.path in excluded or entry.name.startswith('.project-browser-'):
                continue
            relative = prefix + '/' + entry.name if prefix else entry.name
            try:
                info = entry.stat(follow_symlinks=False)
                kind = ('symlink' if stat.S_ISLNK(info.st_mode) else
                        'directory' if stat.S_ISDIR(info.st_mode) else
                        'file' if stat.S_ISREG(info.st_mode) else 'special')
                size = info.st_size if kind == 'file' else 0
                stamp = [kind, size, info.st_mtime_ns]
                change = ('added' if relative not in old else
                          'modified' if old[relative] != stamp else '') if prior else ''
                index = len(rows)
                paths[relative] = index
                rows.append([parent, entry.name, kind, size, int(info.st_mtime), change, project_part(relative)])
                current[relative] = stamp
                if kind == 'directory':
                    descend.append((Path(entry.path), relative, index))
                    continue
                if kind != 'file':
                    if relative in manifest:
                        checks[relative] = {'status': 'not_regular', 'expected': manifest[relative]}
                    continue
                want_preview = _preview_allowed(relative) and size <= TEXT_LIMIT and size <= remaining
                if relative not in manifest and not want_preview:
                    continue
                # Do not follow a substituted file symlink while reading previews/hashes.
                fd = os.open(entry.path, os.O_RDONLY | getattr(os, 'O_NOFOLLOW', 0))
                with os.fdopen(fd, 'rb') as stream:
                    before = os.fstat(stream.fileno())
                    if not stat.S_ISREG(before.st_mode):
                        raise ValueError('Entry is no longer a regular file')
                    digest = hashlib.sha256()
                    chunks = []
                    for chunk in iter(lambda: stream.read(128 * 1024), b''):
                        digest.update(chunk)
                        if want_preview:
                            chunks.append(chunk)
                            if sum(map(len, chunks)) > TEXT_LIMIT:
                                chunks = []; want_preview = False
                    after = os.fstat(stream.fileno())
                if (before.st_size, before.st_mtime_ns) != (after.st_size, after.st_mtime_ns):
                    raise ValueError('File changed while being read; regenerate the browser')
                hashes[relative] = digest.hexdigest()
                if relative in manifest:
                    checks[relative] = {'status': 'match' if digest.hexdigest() == manifest[relative]
                                        else 'mismatch', 'expected': manifest[relative], 'actual': digest.hexdigest()}
                if relative in old and relative in previous.get('hashes', {}) and previous['hashes'][relative] != digest.hexdigest():
                    rows[index][5] = 'modified'
                if want_preview:
                    raw = b''.join(chunks)
                    if b'\0' not in raw:
                        try:
                            previews[relative] = raw.decode('utf-8')
                            remaining -= len(raw)
                        except UnicodeDecodeError:
                            pass
            except (OSError, ValueError) as error:
                issues.append(relative + ': ' + str(error))
                if relative in manifest:
                    checks[relative] = {'status': 'unreadable', 'expected': manifest[relative]}
        stack.extend(reversed(descend))
    # Unreadable subtrees cannot establish deletion.
    # Compare declared aliases with already indexed regular source files. Never
    # open a symlink target; arbitrary and external symlinks remain metadata-only.
    for old_path, new_path in aliases.items():
        if old_path not in paths or new_path not in hashes or rows[paths[old_path]][2] != 'symlink':
            continue
        try:
            expected = os.path.relpath(root/new_path, (root/old_path).parent)
            if os.path.normpath(os.readlink(root/old_path)) == expected and old_path in manifest:
                checks[old_path] = {'status': 'match' if hashes[new_path] == manifest[old_path] else 'mismatch',
                               'expected': manifest[old_path], 'actual': hashes[new_path], 'source': new_path}
        except OSError as error:
            issues.append(old_path + ': ' + str(error))
    uncertain = [p for p, idx in paths.items() if rows[idx][5] == 'unreadable']
    for name in manifest:
        if name not in checks:
            status = 'unreadable' if any(not q or name.startswith(q + '/') for q in uncertain) else 'missing'
            checks[name] = {'status': status, 'expected': manifest[name]}
    removed = sorted(set(old) - set(current)) if prior else []
    removed = [p for p in removed if not any(not q or p.startswith(q + '/') for q in uncertain)]
    now = datetime.now(timezone.utc).isoformat()
    data = {'root': str(root), 'root_uri': root.as_uri() + '/', 'generated': now,
            'rows': rows, 'previews': previews, 'checks': checks, 'issues': issues, 'aliases': aliases,
            'removed': removed, 'previous': previous.get('generated') if prior else None,
            'absent_parts': {p: project_part(p) for p in set(removed) | set(manifest) if p not in paths},
            'part_files': [sum(r[2] == 'file' and r[6] == side for r in rows) for side in (1, 2)],
            'descriptions': DESCRIPTIONS, 'manifest_present': manifest_path.exists(),
            'regenerate': 'cd ' + shlex.quote(str(root)) + ' && ./bin/btc-miner files',
            'watch_command': 'cd ' + shlex.quote(str(root)) + ' && ./bin/btc-miner files --watch 30',
            'files': sum(r[2] == 'file' for r in rows),
            'directories': sum(r[2] == 'directory' for r in rows)}
    state = {'schema': 1, 'root': str(root), 'generated': now, 'files': current, 'hashes': hashes}
    return data, state


def generate(root, output=None, *, watch_seconds=0):
    root = Path(root).resolve()
    output = Path(output).expanduser().absolute() if output else root / 'PROJECT-BROWSER.html'
    if output.suffix.lower() != '.html':
        raise ValueError('Choose an .html output path')
    if output.is_symlink():
        raise ValueError('Output must not be a symbolic link')
    if output.exists():
        with output.open(encoding='utf-8') as stream:
            if stream.read(len(MARKER)) != MARKER:
                raise ValueError('Refusing to replace an HTML file not generated by this command')
    state_path = root / STATE_NAME
    previous = None
    if state_path.is_symlink():
        raise ValueError('Browser state must not be a symbolic link')
    if state_path.exists():
        previous = json.loads(state_path.read_text())
        if not isinstance(previous, dict) or previous.get('schema') != 1:
            raise ValueError('Invalid browser state; preserve or move it before regenerating')
    data, state = inventory(root, excluded=[output, state_path], previous=previous)
    data['watch_seconds'] = watch_seconds
    # Escape HTML parser delimiters even inside application/json script elements.
    payload = json.dumps(data, ensure_ascii=True, separators=(',', ':')).replace('<', '\\u003c').replace('>', '\\u003e').replace('&', '\\u0026')
    html = PAGE.replace('__DATA__', payload)
    output.parent.mkdir(parents=True, exist_ok=True)
    _atomic(output, html)
    _atomic(state_path, json.dumps(state, separators=(',', ':')) + '\n')
    return {'ok': True, 'path': str(output), 'files': data['files'], 'folders': data['directories'],
            'manifest_mismatches': sum(c['status'] != 'match' for c in data['checks'].values()),
            'scan_issues': len(data['issues']), 'generated': data['generated']}


def launch(root, output=None, *, open_browser=True, watch=0):
    if watch and watch < 10:
        raise ValueError('Watch interval must be at least 10 seconds')
    result = generate(root, output, watch_seconds=watch)
    if open_browser:
        result['browser_open_requested'] = webbrowser.open(Path(result['path']).as_uri())
    if not watch:
        return result
    print(json.dumps(result, indent=2), flush=True)
    print('Watching project files. Ctrl+C stops this watcher.', flush=True)
    while True:
        time.sleep(watch)
        result = generate(root, output, watch_seconds=watch)
        print(json.dumps(result), flush=True)


PAGE = MARKER + r'''
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>BTC Miner · Project browser</title>
<style>
:root{color-scheme:dark;--bg:#0c111b;--panel:#141c2a;--line:#29364b;--text:#e3eaf5;--muted:#9eafc7;--accent:#7fe2c2;--blue:#9bc4ff;--warn:#ffd18a}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--text);font:15px/1.55 system-ui,sans-serif}button,input,select{font:inherit}button,a{touch-action:manipulation}button{color:inherit;border:1px solid var(--line);background:var(--panel);padding:8px 12px;border-radius:8px;cursor:pointer}button:hover,a:hover{color:var(--accent);border-color:var(--accent)}button:focus-visible,a:focus-visible,input:focus-visible,select:focus-visible{outline:2px solid var(--accent);outline-offset:3px}a{color:var(--blue);text-decoration:none}header{padding:30px 36px 24px;border-bottom:1px solid var(--line)}.eyebrow{color:var(--accent);font-size:12px;letter-spacing:.16em;text-transform:uppercase}h1{font-size:30px;letter-spacing:-.04em;margin:5px 0}h2{font-size:19px;margin:0 0 14px}.muted{color:var(--muted)}.small{font-size:12px}.layout{display:grid;grid-template-columns:225px minmax(0,1fr)}aside{padding:24px 18px;border-right:1px solid var(--line)}aside button{display:block;width:100%;text-align:left;margin:7px 0}aside .label{margin:24px 8px 8px;color:var(--muted);font-size:12px;text-transform:uppercase;letter-spacing:.08em}main{padding:25px 30px;min-width:0}.stats{display:flex;gap:12px;flex-wrap:wrap;margin:0 0 22px}.stat{padding:12px 18px;background:var(--panel);border:1px solid var(--line);border-radius:10px;min-width:145px}.stat strong{display:block;font-size:24px;color:var(--accent)}.toolbar{display:flex;gap:10px;margin:15px 0;flex-wrap:wrap}input,select{background:var(--panel);border:1px solid var(--line);border-radius:8px;color:var(--text);padding:10px}input{flex:1;min-width:180px}.crumb{display:flex;gap:6px;flex-wrap:wrap;align-items:center;min-height:35px}.crumb button{background:none;border-color:transparent;padding:3px 7px}.table-wrap{overflow:auto;border:1px solid var(--line);border-radius:10px}table{width:100%;border-collapse:collapse;text-align:left}th{font-weight:500;color:var(--muted);font-size:12px;background:var(--panel)}td,th{padding:11px 14px;border-bottom:1px solid var(--line)}tbody tr:last-child td{border-bottom:0}tbody tr:hover{background:#182235}.entry{background:none;border:0;padding:0;text-align:left;word-break:break-word;color:var(--blue)}.folder{color:var(--accent)}.badge{font-size:11px;border:1px solid var(--line);border-radius:12px;padding:2px 8px;white-space:nowrap}.warn{color:var(--warn)}.pager{display:flex;justify-content:space-between;align-items:center;margin:13px 0}.detail{margin-top:25px;padding:22px;background:var(--panel);border:1px solid var(--line);border-radius:12px}.path{overflow-wrap:anywhere;font:12px/1.7 ui-monospace,monospace}.actions{display:flex;flex-wrap:wrap;gap:10px;margin:16px 0}.actions a{border:1px solid var(--line);border-radius:8px;padding:8px 12px}pre{white-space:pre;overflow:auto;max-height:600px;padding:18px;background:#090e17;border:1px solid var(--line);border-radius:8px;font:12px/1.7 ui-monospace,monospace;tab-size:4}details{margin-top:16px}summary{cursor:pointer;color:var(--blue)}#notice{min-height:24px;color:var(--accent)}footer{padding:25px 0;color:var(--muted);font-size:12px}#empty{padding:24px;display:none}.hidden{display:none!important}@media(max-width:850px){.layout{grid-template-columns:1fr}aside{border-right:0;border-bottom:1px solid var(--line);display:flex;gap:7px;overflow:auto;padding:12px}aside button{white-space:nowrap;width:auto;margin:0}aside .label,aside .aside-note{display:none}main{padding:18px}header{padding:22px}td:nth-child(4),th:nth-child(4){display:none}.stat{min-width:115px}}
.split{display:grid;grid-template-columns:minmax(0,1fr) minmax(0,1fr);gap:20px}.part{min-width:0;border-top:3px solid var(--accent);padding-top:16px}.part.other{border-color:var(--blue)}.part h2{margin:0 0 4px}.part-intro{min-height:64px}.part .table-wrap{max-height:570px;overflow:auto}.part th{position:sticky;top:0}.part td,.part th{padding:10px}.part .crumb{font-size:12px;margin:8px 0;min-height:44px}.empty{padding:24px;display:none}.part .pager{gap:8px;flex-wrap:wrap}.part .pager button{font-size:12px;padding:6px 9px}.part-summary{font-size:12px;color:var(--muted);margin-top:6px}@media(max-width:1150px){.layout{grid-template-columns:180px minmax(0,1fr)}main{padding:20px 16px}.split{gap:12px}.part td:nth-child(2),.part th:nth-child(2){display:none}}@media(max-width:850px){.layout{grid-template-columns:1fr}.split{grid-template-columns:1fr}.part-intro{min-height:0}.part td:nth-child(2),.part th:nth-child(2){display:table-cell}}
.scan-summary{margin:0 0 16px}.scan-summary .stats{margin:14px 0}.root-group{margin:0}.root-group summary{display:flex;align-items:center;gap:10px;padding:10px 4px;color:var(--text);font-weight:500}.root-group summary:before{content:'▸';color:var(--accent)}.root-group[open]>summary:before{content:'▾'}.root-group summary span:first-of-type{flex:1}.root-group>table{margin-top:5px}.root-group>table td{font-size:13px}.part .table-wrap:has(.root-group){border-color:var(--line)}
</style></head><body>
<header><div class="eyebrow">BTC Miner / workspace</div><h1>Project browser</h1><div class="muted">Explore the source, follow the evidence, and review file changes.</div><div id="snapshot" class="small muted"></div></header>
<div class="layout"><aside id="sidebar"><div class="label">Project</div></aside><main>
<details class="scan-summary"><summary>Project totals and audit status</summary><div class="stats" id="stats"></div></details>
<div id="description" class="muted">Expand a group, then open a folder. These are compact views of the existing project paths.</div>
<div class="toolbar"><input id="search" type="search" aria-label="Search all project paths" placeholder="Search both sides…"><select id="filter" aria-label="Filter files"><option value="all">All entries</option><option value="changed">Changed since last scan</option><option value="mismatch">Release manifest differences</option><option value="source">Source files</option></select></div>
<div id="notice" role="status"></div>
<div class="split">
<section class="part" id="math-panel" aria-label="Math library"><div class="part-intro"><h2>Math library</h2><div class="small muted">Arithmetic code, math tests, proofs and research references.</div><div class="part-summary" id="math-total"></div></div><nav class="crumb" id="crumb" aria-label="Math folder breadcrumb"></nav>
<div class="table-wrap"><table><thead><tr><th>Name</th><th>Size</th><th>Review</th></tr></thead><tbody id="entries"></tbody></table><div id="empty" class="empty muted">No matching entries on this side.</div></div>
<div class="pager"><span id="count" class="small muted"></span><div><button id="prev">Previous</button> <button id="next">Next</button></div></div>
</section>
<section class="part other" id="other-panel" aria-label="Miner and supporting files"><div class="part-intro"><h2>Miner &amp; supporting files</h2><div class="small muted">Mining, networking, UI, configuration, operations and build tools.</div><div class="part-summary" id="other-total"></div></div><nav class="crumb" id="crumb-other" aria-label="Miner folder breadcrumb"></nav>
<div class="table-wrap"><table><thead><tr><th>Name</th><th>Size</th><th>Review</th></tr></thead><tbody id="entries-other"></tbody></table><div id="empty-other" class="empty muted">No matching entries on this side.</div></div>
<div class="pager"><span id="count-other" class="small muted"></span><div><button id="prev-other">Previous</button> <button id="next-other">Next</button></div></div>
</section></div>
<section id="detail" class="detail hidden" aria-label="Selected file"></section>
<details><summary>Audit workflow and scan details</summary><p>After editing a file, regenerate this page to compare it with the previous scan. Release checks compare SHA-256 hashes with FILES.sha256.json; a matching hash does not prove correctness.</p><p class="muted">Run from Terminal:</p><pre id="commands"></pre><button id="copyRefresh">Copy refresh command</button><p id="scope" class="small muted"></p><pre id="issues"></pre></details>
<footer>Local snapshot. Folder navigation and search work offline. Source previews are embedded as text; other files open from their original local paths. The page provides paths for editing in your editor.</footer>
</main></div><script id="project-data" type="application/json">__DATA__</script><script>
'use strict';
const D=JSON.parse(document.getElementById('project-data').textContent),R=D.rows,$=id=>document.getElementById(id);
const children=Array.from({length:R.length},()=>[]),paths=Array(R.length),byPath=new Map();
paths[0]='';byPath.set('',0);
for(let i=1;i<R.length;i++){
 const r=R[i];children[r[0]].push(i);
 paths[i]=(paths[r[0]]?paths[r[0]]+'/':'')+r[1];byPath.set(paths[i],i);
}
for(const p of new Set([...D.removed,...Object.keys(D.checks).filter(p=>D.checks[p].status==='missing')])){
 if(!byPath.has(p)){
  const i=R.length;R.push([0,p,'missing',0,0,D.removed.includes(p)?'removed':'',D.absent_parts[p]||2]);
  children.push([]);paths.push(p);byPath.set(p,i);
 }
}
// A directory is visible on each side containing one of its descendants.
const masks=R.map((r,i)=>r[2]==='directory'&&children[i].length?0:r[6]);
for(let i=R.length-1;i>0;i--)masks[R[i][0]]|=masks[i];
const belongs=(i,side)=>!!(masks[i]&(1<<side));
const partName=side=>side===0?'Math library':'Miner & supporting files';
let current=[0,0],pages=[0,0],selected=-1;const pageSize=100,openGroups=[new Set(),new Set()];
const get=(id,side)=>$(id+(side?'-other':''));
const el=(tag,text,cls)=>{const e=document.createElement(tag);if(text!==undefined)e.textContent=text;if(cls)e.className=cls;return e};
const button=(label,fn,cls)=>{const e=el('button',label,cls);e.type='button';e.onclick=fn;return e};
const fmt=n=>n<1024?n+' B':n<1048576?(n/1024).toFixed(1)+' KB':n<1073741824?(n/1048576).toFixed(1)+' MB':(n/1073741824).toFixed(2)+' GB';
const fileURI=p=>D.root_uri+p.split('/').map(encodeURIComponent).join('/');
const quote=s=>"'"+s.replaceAll("'","'\\''")+"'";
async function copy(text){try{await navigator.clipboard.writeText(text);$('notice').textContent='Copied to clipboard.'}catch(e){window.prompt('Copy this text:',text)}}
function writeRoute(){
 const p=new URLSearchParams({math:paths[current[0]],miner:paths[current[1]]});
 if(selected>=0)p.set('file',paths[selected]);
 location.hash=p.toString();render();if(selected>=0)showFile(selected);
}
function navigate(i,side){
 $('search').value='';$('filter').value='all';selected=-1;pages[side]=0;
 current[side]=belongs(i,side)?i:0;writeRoute();
}
function jump(path){
 const i=byPath.get(path);if(i===undefined)return;
 $('search').value='';$('filter').value='all';selected=-1;pages=[0,0];
 for(let s=0;s<2;s++)if(i===0||belongs(i,s))current[s]=i;
 writeRoute();
}
function route(){
 const raw=location.hash.slice(1);selected=-1;current=[0,0];pages=[0,0];
 if(!raw)current=[byPath.get('math-library')||0,byPath.get('src')||0];
 if(raw.startsWith('math=')){
  const p=new URLSearchParams(raw);
  for(let s=0;s<2;s++){const i=byPath.get(p.get(s?'miner':'math')||'');if(i!==undefined&&R[i][2]==='directory'&&belongs(i,s))current[s]=i}
  const f=byPath.get(p.get('file'));if(f!==undefined&&R[f][2]!=='directory')selected=f;
 }else if(raw){
  let p;try{p=decodeURIComponent(raw)}catch(e){p=''}
  const i=byPath.get(p);if(i!==undefined){
   if(R[i][2]==='directory'){for(let s=0;s<2;s++)if(belongs(i,s))current[s]=i}
   else{selected=i;current[R[i][6]===1?0:1]=R[i][0]}
  }
 }
 render();if(selected>=0)showFile(selected);
}
function openFile(i){selected=i;current[R[i][6]===1?0:1]=R[i][0];writeRoute()}
function badge(i){const c=D.checks[paths[i]];return c&&c.status!=='match'?'manifest '+c.status:R[i][5]||(c?'hash matches':'')}
function showFile(i){
 selected=i;const r=R[i],p=paths[i],box=$('detail');box.replaceChildren();box.classList.remove('hidden');
 box.append(el('div',partName(r[6]===1?0:1),'eyebrow'),el('h2',r[1]),el('div',D.root+'/'+p,'path'));
 const check=D.checks[p];box.append(el('p',r[2]+' · '+fmt(r[3])+(badge(i)?' · '+badge(i):'')+(r[4]?' · '+new Date(r[4]*1000).toLocaleString():''),'muted'));
 const actions=el('div',undefined,'actions');
 if(D.aliases&&D.aliases[p]&&byPath.has(D.aliases[p]))actions.append(button('Open source in new layout',()=>openFile(byPath.get(D.aliases[p]))));
 if(r[2]==='file'){const a=el('a','Open original file');a.href=fileURI(p);a.target='_blank';a.rel='noopener noreferrer';actions.append(a)}
 actions.append(button('Copy file path',()=>copy(D.root+'/'+p)),button('Copy editor command',()=>copy('open -t '+quote(D.root+'/'+p))),button('Show folder',()=>navigate(r[0],r[6]===1?0:1)));box.append(actions);
 if(check)box.append(el('div','Release manifest: '+check.status,'small'),el('div','Expected SHA-256: '+check.expected,'path'),el('div','Current SHA-256: '+(check.actual||'unavailable'),'path'));
 if(D.previews[p]!==undefined)box.append(el('h3','Source preview'),el('pre',D.previews[p]));
 else box.append(el('p',r[2]==='symlink'?'Symbolic link listed without following its target.':'Content is not embedded for this file. Use Open original file to inspect it locally.','muted'));
 box.scrollIntoView({block:'start',behavior:'smooth'});
}
function rootGroup(i,side){
 const name=R[i][1];
 if(['src','math-library','btcminer','native','bin','BTC Miner.app'].includes(name)||name.endsWith('.command'))return side===0?'Library code':'Application & launch';
 if(['tests','scripts','.test-tools','optional'].includes(name))return 'Tests & tools';
 if(['research','reference','validation','logs','dist','reports'].includes(name))return side===0?'Proofs & research':'Runs & releases';
 return side===0?'Documentation':'Docs & configuration';
}
function renderPanel(side,query,filter){
 let ids=(query||filter!=='all')?R.map((_,i)=>i).slice(1):children[current[side]].slice();
 ids=ids.filter(i=>belongs(i,side)&&(!query||paths[i].toLowerCase().includes(query))&&(filter!=='changed'||!!R[i][5])&&(filter!=='mismatch'||(D.checks[paths[i]]&&D.checks[paths[i]].status!=='match'))&&(filter!=='source'||/\.(py|c|h|lean|sh)$/.test(R[i][1])));
 ids.sort((a,b)=>(R[a][2]==='directory'?0:1)-(R[b][2]==='directory'?0:1)||paths[a].localeCompare(paths[b]));
 const max=Math.max(0,Math.ceil(ids.length/pageSize)-1);pages[side]=Math.min(pages[side],max);
 const tbody=get('entries',side);tbody.replaceChildren();
 const compact=current[side]===0&&!query&&filter==='all';
 tbody.closest('table').querySelector('thead').hidden=compact;
 const groups=new Map();
 if(compact){
  const names=side===0?['Library code','Tests & tools','Proofs & research','Documentation']:['Application & launch','Tests & tools','Runs & releases','Docs & configuration'];
  const visible=ids.slice(pages[side]*pageSize,(pages[side]+1)*pageSize);
  for(const name of names){
   const members=visible.filter(i=>rootGroup(i,side)===name);if(!members.length)continue;
   const row=el('tr'),cell=el('td'),details=el('details',undefined,'root-group');cell.colSpan=3;
   details.open=openGroups[side].has(name);details.ontoggle=()=>{if(details.open)openGroups[side].add(name);else openGroups[side].delete(name)};
   const summary=el('summary');summary.append(el('span',name),el('span',members.length+' items','small muted'));
   const table=el('table'),body=el('tbody');table.setAttribute('aria-label',name+' files');table.append(body);details.append(summary,table);cell.append(details);row.append(cell);tbody.append(row);groups.set(name,body);
  }
 }
 for(const i of ids.slice(pages[side]*pageSize,(pages[side]+1)*pageSize)){
  const r=R[i],tr=el('tr'),td=el('td');
  td.append(button((r[2]==='directory'?'▸ ':r[2]==='symlink'?'↗ ':'')+r[1],()=>r[2]==='directory'?navigate(i,side):openFile(i),'entry '+(r[2]==='directory'?'folder':'')));
  if(query||filter!=='all')td.append(el('div',paths[i],'small muted'));
  tr.append(td,el('td',r[2]==='directory'?children[i].filter(j=>belongs(j,side)).length+' entries':fmt(r[3]),'small muted'));
  const status=el('td');if(badge(i))status.append(el('span',badge(i),'badge '+(badge(i).includes('mismatch')?'warn':'')));tr.append(status);(compact?groups.get(rootGroup(i,side)):tbody).append(tr);
 }
 get('empty',side).style.display=ids.length?'none':'block';
 get('count',side).textContent=compact?groups.size+' groups · '+ids.length.toLocaleString()+' top-level entries'+(max?' · page '+(pages[side]+1)+' of '+(max+1):''):ids.length.toLocaleString()+' entries'+(ids.length?' · page '+(pages[side]+1)+' of '+(max+1):'');
 get('prev',side).disabled=pages[side]===0;get('next',side).disabled=pages[side]>=max;
 const crumb=get('crumb',side);crumb.replaceChildren(button('Root',()=>navigate(0,side)));let cursor='';
 for(const part of paths[current[side]].split('/').filter(Boolean)){
  cursor+=(cursor?'/':'')+part;const index=byPath.get(cursor);crumb.append(el('span','/','muted'),button(part,()=>navigate(index,side)));
 }
}
function render(){const q=$('search').value.toLowerCase().trim(),f=$('filter').value;renderPanel(0,q,f);renderPanel(1,q,f);if(selected<0)$('detail').classList.add('hidden')}
const mismatches=Object.values(D.checks).filter(x=>x.status!=='match').length;
for(const [n,label] of [[D.files,'files indexed'],[D.directories,'folders'],[Object.keys(D.checks).length,'manifest entries'],[mismatches,'manifest differences'],[D.issues.length,'scan issues']]){
 const s=el('div',undefined,'stat');s.append(el('strong',n.toLocaleString()),el('span',label,'small muted'));$('stats').append(s);
}
$('math-total').textContent=D.part_files[0].toLocaleString()+' files across nested folders · includes research history';
$('other-total').textContent=D.part_files[1].toLocaleString()+' files across nested folders · includes tools and dependencies';
const side=$('sidebar');
for(const [label,path] of [['All project files',''],['Miner source','src'],['Math library','math-library'],['Tests','tests'],['Research registry','research'],['Audit evidence','validation'],['Reference sources','reference'],['Scripts','scripts']])if(byPath.has(path))side.append(button(label,()=>jump(path)));
side.append(el('div','Review','label'),button('Release differences',()=>{$('search').value='';$('filter').value='mismatch';pages=[0,0];render()}),button('Recent changes',()=>{$('search').value='';$('filter').value='changed';pages=[0,0];render()}),button('Copy refresh command',()=>copy(D.regenerate)),el('p','Math consumers such as mining strategies stay with the miner. Proofs and references retain their own verification scope.','small muted aside-note'));
$('snapshot').textContent='Generated '+new Date(D.generated).toLocaleString()+(D.watch_seconds?' · refreshes while the watcher runs':' · regenerate to see edits');
if(D.issues.length)$('notice').textContent='Some entries could not be checked. See scan details below.';
else if(!D.manifest_present)$('notice').textContent='No release manifest found. File navigation is available; release identity checks are unavailable.';
$('commands').textContent=D.regenerate+'\n\n# Refresh continuously; Ctrl+C stops the watcher\n'+D.watch_command;
$('scope').textContent=(D.previous?'Compared with '+new Date(D.previous).toLocaleString()+'.':'First scan: no previous snapshot for change comparison.')+' Every file belongs to one side. Mixed folders appear on both sides with different contents. The navigation map is in btcminer/project_browser.py; newly added unclassified code goes to supporting files. All normal and hidden folders are indexed. Symlinks are not followed. Generated browser/state files are excluded. Changes use size/time metadata, supplemented by SHA-256 for tracked files and source previews. Operational configuration and logs are not embedded as previews.';
$('issues').textContent=[...D.issues,...D.removed.map(p=>'Removed since previous scan: '+p),...Object.entries(D.checks).filter(([p,c])=>c.status==='missing').map(([p])=>'Missing release input: '+p)].join('\n')||'No scan errors, removed paths or missing release inputs recorded.';
$('copyRefresh').onclick=()=>copy(D.regenerate);
for(let s=0;s<2;s++){get('prev',s).onclick=()=>{pages[s]--;render()};get('next',s).onclick=()=>{pages[s]++;render()}}
let timer;$('search').oninput=()=>{clearTimeout(timer);timer=setTimeout(()=>{pages=[0,0];render()},180)};
$('filter').onchange=()=>{pages=[0,0];render()};window.addEventListener('hashchange',route);route();
if(D.watch_seconds)setTimeout(()=>location.reload(),(D.watch_seconds+5)*1000);
</script></body></html>
'''
