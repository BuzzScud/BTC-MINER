"""Portable admission gate for the miner's scoped mathematical evidence.

MUST verify source/object hashes and both raw axiom inventories; a pass flag or a
name in an old log is insufficient. SHALL preserve all explicit theorem names and
reject nonstandard assumptions. MAY reuse already kernel-checked, immutable
artifacts; this does not re-run Lean or prove C/Python refinement or SHA shortcuts.
See ../MASTER_PLAN.md: PROOF-01, RELEASE-01 and research/proof-evidence/manifest.json.
This module is read-only and MUST NOT control mining, nodes or the provider API.
"""
import hashlib
import json
from pathlib import Path, PurePosixPath

ALLOWED_AXIOMS = frozenset({'propext', 'Classical.choice', 'Quot.sound'})
TARGETS = ['RequestProject.RodCircles', 'RequestProject.RodScaling',
           'RequestProject.TowerCollapse', 'RequestProject.ApiSupportNumbers']


class EvidenceError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise EvidenceError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def parse_axioms(text, required):
    roots, totals = {}, []
    for line in text.splitlines():
        if line.startswith('ROOT\t'):
            fields = line.split('\t')
            require(len(fields) == 4, 'Malformed theorem assumption record')
            _, module, name, raw = fields
            require(module in required and name not in roots, 'Unexpected or duplicate theorem root')
            axioms = sorted(set(filter(None, raw.split(','))))
            require(set(axioms) <= ALLOWED_AXIOMS, 'Forbidden theorem assumption: ' + name)
            roots[name] = {'module': module, 'axioms': axioms}
        elif line.startswith('TOTAL\t'):
            try:
                totals.append(int(line.split('\t')[1]))
            except ValueError as error:
                raise EvidenceError('Malformed assumption total') from error
    require(bool(roots) and totals == [len(roots)], 'Incomplete theorem assumption inventory')
    for module, names in required.items():
        require(all(name in roots and roots[name]['module'] == module for name in names),
                'Missing required theorem: ' + module)
    counts = {module: sum(row['module'] == module for row in roots.values()) for module in required}
    return roots, counts


def verify(root=None, *, evidence_directory=None):
    """Check a content-addressed proof capsule and its current workspace sources.

    The release includes proof artifacts; the pinned external Lean/mathlib
    toolchain remains a recorded prerequisite for fresh compilation. Those
    external caches are not silently copied into the release or counted as fresh.
    """
    if root is None:
        from . import ROOT
        root = ROOT
    root = Path(root).resolve()
    directory = Path(evidence_directory) if evidence_directory is not None else root / 'research/proof-evidence'
    manifest_path = directory / 'manifest.json'
    try:
        manifest_data = manifest_path.read_bytes()
        manifest = json.loads(manifest_data)
        require(manifest.get('schema') == 'miner-portable-proof-evidence-v1', 'Unsupported proof capsule')
        require(manifest.get('status') == 'accepted', 'Proof capsule is not accepted')
        objects = {}
        for relative, expected in manifest['objects'].items():
            path = directory / relative
            require(relative == 'objects/' + expected and not path.is_symlink(), 'Invalid evidence object path')
            data = path.read_bytes()
            require(digest(data) == expected, 'Changed evidence object: ' + relative)
            objects[relative] = data
        actual = {p.relative_to(directory).as_posix() for p in (directory / 'objects').iterdir() if p.is_file()}
        # Old immutable objects MAY remain after atomic manifest replacement.
        # Only the complete manifest-referenced set is admitted or shipped.
        require(set(objects) <= actual, 'Proof object inventory incomplete')

        def original(path):
            key = manifest['original_files'].get(str(path))
            require(key in objects, 'Missing bound evidence file: ' + str(path))
            return objects[key]

        def bound(path, sha):
            data = original(path)
            require(digest(data) == sha, 'Receipt binding differs: ' + str(path))
            return data

        raw = json.loads(original(manifest['raw_report']))
        lake = json.loads(original(manifest['lake_report']))
        review = json.loads(original(manifest['final_review']))
        source_manifest = json.loads(original(manifest['source_manifest']))
        require(digest(original(manifest['raw_report'])) == lake['raw_report_sha256'], 'Lake/raw binding differs')
        require(review['raw_gate']['sha256'] == digest(original(manifest['raw_report'])) and
                review['lake_gate']['sha256'] == digest(original(manifest['lake_report'])), 'Final review receipt binding differs')
        for receipt in (raw, lake, review):
            require(receipt.get('status') == 'passed' and receipt.get('ok') is True, 'Unaccepted proof receipt')
        # The independent final review binds every local gate, input, log and
        # object. External toolchain/cache identities are recorded separately;
        # they were used by the original build, not recompiled by this verifier.
        local_bindings, external_bindings = {}, {}
        for filename, expected in review['verified_file_bindings'].items():
            path = PurePosixPath(filename)
            local = any(PurePosixPath(manifest[key]) in path.parents for key in ('repair_root', 'historical_root'))
            if local:
                bound(filename, expected)
                local_bindings[filename] = expected
            else:
                external_bindings[filename] = expected
        require(manifest['external_prerequisite_bindings'] == external_bindings,
                'External prerequisite identities differ')
        bound(review['html_report'], review['html_report_sha256'])
        require(set(manifest['original_files']) == set(local_bindings) | {
            manifest['final_review'], review['html_report']}, 'Local evidence binding inventory differs')
        require(set(manifest['original_files'].values()) == set(objects), 'Unbound proof capsule objects')
        require(set(review['allowed_logical_axioms']) == ALLOWED_AXIOMS and
                set(review['actual_axioms']) <= ALLOWED_AXIOMS, 'Final review assumption contract differs')
        require(raw.get('all_requested_modules_compiled') is True, 'Raw proof build incomplete')
        require(raw['targets'] == lake['targets'] == TARGETS, 'Proof target scope differs')
        require(raw['sources'] == lake['sources'] == source_manifest['sources'], 'Proof source inventories differ')
        require(raw['build_order'] == lake['local_closure'], 'Proof import closures differ')
        required = raw['required_named_theorems']
        require(required == lake['required_named_theorems'] and set(required) == set(raw['build_order']),
                'Required theorem inventory differs')
        require(len(required['RequestProject.RodScaling']) == 25, 'RodScaling certificate inventory incomplete')
        source_root = PurePosixPath(manifest['source_root'])
        for relative, expected in raw['sources'].items():
            bound(source_root / relative, expected)
        for relative, expected in manifest['workspace_sources'].items():
            path = root / relative
            require(not Path(relative).is_absolute() and '..' not in Path(relative).parts,
                    'Workspace source path escapes release')
            require(path.is_file() and digest(path.read_bytes()) == expected, 'Stale proof source: ' + relative)
        require(manifest['workspace_sources'] == {
            'validation/miner-proof-repair-20261007/sources/' + rel: sha
            for rel, sha in source_manifest['sources'].items()}, 'Workspace source inventory omitted an input')
        require(len(raw['builds']) == len(raw['build_order']), 'Raw build closure incomplete')
        for name, build in zip(raw['build_order'], raw['builds']):
            require(build['module'] == name and build['exit_code'] == 0, 'Raw module did not compile')
            bound(build['log'], build['log_sha256'])
            module_path = name.replace('.', '/')
            source = original(source_root / (module_path + '.lean')).decode()
            extensions = ['.olean', '.olean.private', '.olean.server', '.ir'] if source.startswith('module\n') else ['.olean']
            require(all(module_path + suffix in build['artifacts'] for suffix in extensions),
                    'Missing compiled module companion')
            for relative, expected in build['artifacts'].items():
                bound(PurePosixPath(raw['object_directory']) / relative, expected)
        require([b['target'] for b in lake['builds']] == TARGETS, 'Lake build target inventory differs')
        for build in lake['builds']:
            require(build['exit_code'] == 0, 'Lake module did not compile')
            bound(build['log'], build['log_sha256'])
        for relative, expected in lake['artifacts'].items():
            bound(PurePosixPath(lake['workspace']) / relative, expected)
        parsed = []
        for receipt in (raw, lake):
            audit = receipt['axiom_audit']
            require(audit['exit_code'] == 0, 'Theorem assumption audit failed')
            text = bound(audit['log'], audit['log_sha256']).decode()
            roots, counts = parse_axioms(text, required)
            require(roots == receipt['theorem_roots'] and counts == receipt['module_theorem_counts'] and
                    len(roots) == receipt['theorem_count'], 'Raw theorem inventory and receipt differ')
            parsed.append((roots, counts))
        require(parsed[0] == parsed[1], 'Raw and Lake assumptions differ')
        raw_dir = PurePosixPath(manifest['raw_report']).parent
        control = raw['negative_control']
        bound(raw_dir / 'WrongArithmetic.lean', control['source_sha256'])
        text = bound(control['log'], control['log_sha256']).decode()
        require(control['exit_code'] == 1 and control['expected_rejection'] is True and
                'error:' in text and '0 = 1' in text, 'False arithmetic rejection missing')
        control = raw['assumption_controls']
        bound(raw_dir / 'AssumptionControls.lean', control['source_sha256'])
        text = bound(control['log'], control['log_sha256']).decode()
        require(control['exit_code'] == 0 and control['rejected'] == {
            'rejected_custom_root': True, 'rejected_sorry_root': True}, 'Assumption rejection controls missing')
        require('rejected_custom_axiom' in text and 'sorryAx' in text, 'Assumption control log differs')
        roots, counts = parsed[0]
        require(review['theorem_count'] == len(roots) and
                review['named_theorem_count'] == sum(map(len, required.values())), 'Final review theorem counts differ')
        require(manifest_path.read_bytes() == manifest_data, 'Proof manifest changed during verification')
        return {'status': 'passed', 'manifest_sha256': digest(manifest_data),
                'theorem_count': len(roots), 'named_theorem_count': sum(map(len, required.values())),
                'required_named_theorems': required, 'theorem_roots': roots,
                'module_theorem_counts': counts, 'source_manifest': source_manifest,
                'raw_receipt': raw, 'objects_checked': len(objects),
                'preserved_historical_headers': review['historical_theorem_headers_preserved'],
                'scope': review['scope'], 'original_files': manifest['original_files'],
                'directory': str(directory), 'manifest': manifest}
    except (OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        raise EvidenceError('Missing or invalid proof evidence: ' + str(error)) from error


def constant_product_entries(root, evidence):
    """Translate only closed Nat multiplication equalities with admitted roots.

    MUST reject arbitrary Lean syntax rather than guess its meaning. Other proved
    statements remain proof-only until a supported typed translation exists.
    """
    import re
    path = Path(root) / 'validation/miner-proof-repair-20261007/sources/RequestProject/ApiSupportNumbers.lean'
    source = path.read_text()
    pattern = r'^theorem (returned_\d+) : \(([0-9]+(?: \* [0-9]+)*) : Nat\) = ([0-9]+) := by decide$'
    matches = list(re.finditer(pattern, source, re.M))
    names = {'ApiSupportNumbers.' + m[1] for m in matches}
    require(names == set(evidence['required_named_theorems']['RequestProject.ApiSupportNumbers']),
            'Unsupported or missing executable theorem translation')
    entries = []
    for match in matches:
        factors = [int(x) for x in match[2].split(' * ')]
        expression = factors[0]
        product = factors[0]
        for factor in factors[1:]:
            expression = ['mul', expression, factor]
            product *= factor
        expected = int(match[3])
        require(product == expected, 'Theorem translation arithmetic disagrees')
        name = 'ApiSupportNumbers.' + match[1]
        require(name in evidence['theorem_roots'], 'Translation has no accepted proof root')
        entries.append({'theorem': name, 'supported': True, 'proof_check': 'passed',
                        'source_module': 'RequestProject.ApiSupportNumbers',
                        'source_sha256': digest(path.read_bytes()),
                        'statement': match[0].split(' := by')[0],
                        'variables': [], 'premises': [], 'conclusion': ['eq', expression, expected],
                        'translation_domain': 'closed natural-number multiplication equality',
                        'bitcoin_exclusion_authority': False})
    return entries


def verify_catalogue(root, catalogue, evidence=None):
    evidence = evidence or verify(root)
    require(catalogue.get('schema') == 2 and catalogue.get('status') == 'accepted_scoped_translations',
            'Executable catalogue has no current acceptance contract')
    require(catalogue.get('proof_manifest_sha256') == evidence['manifest_sha256'], 'Stale executable catalogue proof binding')
    expected = constant_product_entries(root, evidence)
    actual = catalogue.get('theorems')
    require(isinstance(actual, list) and len(actual) == len(expected) == catalogue.get('count'),
            'Executable catalogue inventory differs')
    for wanted, entry in zip(expected, actual):
        require(all(entry.get(k) == v for k, v in wanted.items()), 'Executable theorem/type/premises changed')
        require(entry.get('instance_checks') == 1 and entry.get('instance_check_passed') is True,
                'Required bounded translation check missing')
    return catalogue
