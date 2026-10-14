#!/usr/bin/env python3
"""Build a gated portable miner release from isolated staging.

MUST admit current proof sources, objects, assumptions and typed translations
before publication. SHALL recheck them in the copied stage and record scope in
BUILD-INFO. MUST exclude credentials, logs and live settings, and MUST NOT start
or control the user's miner/node. Offline tests run only in temporary staging.
See ../MASTER_PLAN.md RELEASE-01, PROOF-01, PUBLISH-01 and LIVE-01.
"""
import argparse
import datetime
import hashlib
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from btcminer import VERSION
from btcminer.proof_evidence import verify, verify_catalogue, require, digest


def run(args, cwd, env, logfile=None):
    if logfile is None:
        return subprocess.run(args, cwd=cwd, env=env, check=True)
    result = subprocess.run(args, cwd=cwd, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    logfile.parent.mkdir(parents=True, exist_ok=True)
    logfile.write_text(result.stdout)
    print(result.stdout, end='', flush=True)
    result.check_returncode()
    return result


def release_files(root, evidence):
    """The explicit export boundary excludes operational/private files."""
    public = root/'PUBLIC_FILES.json'
    if public.is_file():
        files = json.loads(public.read_text())
        require(isinstance(files,list) and len(files)==len(set(files)), 'Invalid public export inventory')
        require(all(not Path(name).is_absolute() and '..' not in Path(name).parts for name in files), 'Unsafe export path')
        return sorted(files)
    # Explicit inputs prevent saved credentials, session logs and optional
    # third-party libraries from entering a distributable archive.
    files = ["README.md", "LICENSE", "SOURCE-NOTES.md", ".gitignore",
             "BUILD-ASSESSMENT.md", "IMPLEMENTATION-PLAN.md",
             "Start BTC Miner.command", "install.command",
             "THESIS2 Implementation Report.html", "optional/README.md",
             "native/build.sh", "native/hasher_fast.c", "scripts/build.py", "scripts/regtest.py",
             "bin/btc-miner", "bin/minerctl.sh", "bin/miner-ui.sh",
             "BTC Miner.app/Contents/Info.plist", "BTC Miner.app/Contents/MacOS/launcher"]
    files += [str(path.relative_to(root)) for path in (root / "btcminer").rglob("*.py")]
    files += ["docs/GEOMETRY-CODEC.txt", "research/geometry-codec-contract.json"]
    files += ["docs/SCALE-GRAPH-TRAVERSAL.txt", "research/scale-graph-runtime.json"]
    files += ["src/ui/modelling.html", "docs/LIVE-MODELLING.txt"]
    files += ["docs/PROVIDER-API.txt"]
    files += [str(path.relative_to(root)) for path in (root/'reference/fractal-abacus').iterdir() if path.is_file()]
    files += ["docs/project-layout.json", "docs/PROJECT-STRUCTURE.txt",
              "native/latcalc/PROVENANCE.json", "math-library/native/latcalc/PROVENANCE.json"]
    files += [str(path.relative_to(root)) for folder in ("src", "math-library")
              for path in (root / folder).rglob("*")
              if path.is_file() and path.suffix in (".py", ".c", ".h")]
    files += [str(path.relative_to(root)) for path in (root / "tests").rglob("*.py")]
    files += ['docs/PRODUCTION-BLOCK-VALIDATION.txt',
              'docs/RESOURCE-CONTROL.txt','docs/PROVIDER-SYSTEM-METRICS.txt',
              'tests/fixtures/core-accepted-block/decoded.json',
              'tests/fixtures/core-accepted-block/raw.hex']
    files += ["native/build_rodsieve.sh", "native/build_abacus.sh", "research/claims.json",
              "research/study-policy.json", "research/integration-status.json", "research/executable-theorems.json",
              "research/formula-catalogue.json", "research/math-catalogue-reference.json", "research/math-consumers.json"]
    files += [str(path.relative_to(root)) for path in (root / "native/latcalc").rglob("*")
              if path.is_file() and path.suffix in (".c", ".h")]
    files += ["reference/thesis2-math-in-pictures.html", "scripts/capacity_real_report.py"]
    files += [str(path.relative_to(root)) for path in (root / "validation").glob("*.json")]
    files += ["VALIDATION.md", "TERMINAL-COMMANDS.md", "MATH-IMPLEMENTATION.md"]
    files += ["EMBER-IMPLEMENTATION.md", "validation/ember/pty-check.json",
              "scripts/check_ember_terminal.py"]
    files += ["scripts/check_loop_terminal.py", "validation/fullscreen-loop-20261011/pty-check.json"]
    files += ["scripts/check_copper_terminal.py", "scripts/check_copper_hub.py",
              "validation/copper/pty-check.json", "validation/copper/hub-check.json"]
    files += ["DIFFICULTY.md", "validation/difficulty/regtest.json"]
    files += ["ARISTOTLE-MONITOR.md", "scripts/monitor_aristotle_math.py", "scripts/apply_math_update.py"]
    files += [str(path.relative_to(root)) for path in
              (root / "reference/aristotle-core-primes").glob("*") if path.is_file()]
    files += [str(path.relative_to(root)) for path in
              (root / "reference/aristotle-rods-towers").glob("*") if path.is_file()]
    files += ["reference/aristotle-ellipse-rods/" + name for name in
              ("EllipseSearch.lean", "DynamicRods.lean", "ELLIPSE_AND_RODS.md")]
    files += ["validation/ellipse-rods/" + name for name in
              ("source-provenance.json", "unit-tests.log", "math-inspect.json", "regtest.json")]
    files += ["MASTER_PLAN.md", "scripts/verify_proof_evidence.py", "scripts/publish_archive_calculations.py",
              "scripts/refresh_research_metadata.py", "scripts/bounded_miner_proof_audit.py", "research/proof-registry.json",
              "research/provider-coverage-ledger.json", "research/provider-coverage-reference.json",
              "research/proof-evidence/manifest.json", "research/proof-evidence/report.html"]
    files += list(evidence['manifest']['workspace_sources'])
    files += ["research/proof-evidence/" + relative for relative in evidence['manifest']['objects']]
    return sorted(set(files))


def check_release_inputs(root, *, check_manifest=True):
    """Fail closed on stale mathematical evidence, registry or source inventory."""
    proof = verify(root)
    layout = json.loads((root/'docs/project-layout.json').read_text())
    require(layout.get('schema') == 'btc-project-layout/v1', 'Unknown project layout')
    seen = set()
    for entry in layout['files']:
        old, new = entry['compatibility_path'], entry['source_path']
        require(old not in seen, 'Duplicate compatibility path')
        seen.add(old)
        for name in (old, new):
            require(not Path(name).is_absolute() and '..' not in Path(name).parts,
                    'Invalid layout path')
        require((root/old).is_file() and (root/new).is_file() and
                digest((root/old).read_bytes()) == digest((root/new).read_bytes()),
                'Stale release input: layout alias differs from source: '+old)
    catalogue = json.loads((root/'research/executable-theorems.json').read_text())
    verify_catalogue(root, catalogue, proof)
    registry = json.loads((root/'research/proof-registry.json').read_text())
    require(registry['proof_manifest_sha256'] == proof['manifest_sha256'], 'Stale proof registry')
    named = {name:module for module,names in proof['required_named_theorems'].items() for name in names}
    require({entry['theorem']:entry['module'] for entry in registry['theorems']} == named and
            len(registry['theorems']) == len(named), 'Proof registry theorem inventory differs')
    require(registry['named_theorem_count'] == len(named) and registry['audited_root_count'] == proof['theorem_count'],
            'Proof registry root count differs')
    supported = {entry['theorem'] for entry in catalogue['theorems']}
    for entry in registry['theorems']:
        relative = entry['module'].replace('.', '/')+'.lean'
        require(entry['source'] == 'validation/miner-proof-repair-20261007/sources/'+relative and
                entry['source_sha256'] == proof['source_manifest']['sources'][relative] and
                entry['axioms'] == proof['theorem_roots'][entry['theorem']]['axioms'], 'Proof registry source or assumptions differ')
        require(entry['proof_status'] == 'accepted_scoped_kernel_statement' and
                entry['execution_status'] == ('accepted_closed_Nat_translation' if entry['theorem'] in supported else 'proof_only_translation_unimplemented') and
                entry['bitcoin_exclusion_authority'] is False, 'Proof registry scope differs')
    if check_manifest:
        manifest = json.loads((root/'FILES.sha256.json').read_text())
        expected = release_files(root, proof)
        require(set(expected) <= set(manifest), 'Release source inventory differs; refresh metadata after review')
        for relative in expected:
            require(digest((root/relative).read_bytes()) == manifest[relative], 'Stale release input: '+relative)
    return proof


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "dist")
    args = parser.parse_args()
    proof = check_release_inputs(ROOT)
    output = args.output.expanduser().resolve()
    output.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    with tempfile.TemporaryDirectory(prefix="btc-miner-build-") as temp:
        stage = Path(temp) / "BTC MINER"
        stage.mkdir()
        files = release_files(ROOT, proof)
        for name in files:
            dest = stage / name
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / name, dest)
        # Copied artifacts MUST independently pass; source check alone is not a
        # release acceptance. The stage gets its own generated full-file manifest.
        shutil.copy2(ROOT / "FILES.sha256.json", stage / "FILES.sha256.json")
        staged_proof = check_release_inputs(stage)
        require(staged_proof['manifest_sha256'] == proof['manifest_sha256'], 'Stage proof differs')
        (stage / "logs").mkdir()
        (stage / "logs/.gitkeep").touch()
        print("Building native SHA256d in a clean staging folder...", flush=True)
        run([sys.executable, "scripts/build_native.py"], stage, env)
        if platform.system() == "Darwin":
            run(["codesign", "--force", "--sign", "-", "BTC Miner.app"], stage, env)
        print("Checking native hashing and the regression suite...", flush=True)
        run([sys.executable, "-B", "-m", "btcminer", "self-test", "--require-native"], stage, env)
        unit_result = run([sys.executable, "-B", "-m", "unittest", "discover", "-s", "tests"], stage, env,
                          stage/'validation/package-regression.log')
        test_total = re.search(r'Ran (\d+) tests?', unit_result.stdout)
        skip_total = re.search(r'OK \(skipped=(\d+)\)', unit_result.stdout)
        regtest = {}
        if (stage / "validation/regtest.json").is_file():
            regtest = json.loads((stage / "validation/regtest.json").read_text())
        matching_evidence = (regtest.get("ok") is True and regtest.get("miner_version") == VERSION and
                             bool(regtest.get("source_sha256")) and
                             all((stage/name).is_file() and hashlib.sha256((stage/name).read_bytes()).hexdigest()==digest
                                 for name,digest in regtest.get("source_sha256",{}).items()))
        info = {"version":VERSION, "built_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),
                "platform":platform.system(), "architecture":platform.machine(),
                "python":platform.python_version(), "native_self_test":"passed",
                "offline_regression_suite":"passed", "core_regtest_validated":matching_evidence,
                "offline_test_count":int(test_total[1]) if test_total else None,
                "offline_skipped_count":int(skip_total[1]) if skip_total else 0,
                "offline_test_log":"validation/package-regression.log",
                "mainnet_validated":False, "live_pool_validated":False,
                "mathematical_evidence":{"status":"verified_existing_kernel_artifacts",
                    "proof_manifest_sha256":proof['manifest_sha256'],
                    "audited_roots":proof['theorem_count'],"named_theorems":proof['named_theorem_count'],
                    "executable_translations":len(json.loads((stage/'research/executable-theorems.json').read_text())['theorems']),
                    "fresh_lean_run_in_package_build":False,"scope":proof['scope']}}
        (stage / "BUILD-INFO.json").write_text(json.dumps(info, indent=2)+"\n")
        package_names = sorted(set(files + ['BUILD-INFO.json', 'validation/package-regression.log'] +
            [p.relative_to(stage).as_posix() for p in (stage/'native').iterdir()
             if p.suffix in ('.dylib','.so','.dll')]))
        manifest = {name:hashlib.sha256((stage/name).read_bytes()).hexdigest() for name in package_names}
        (stage / "FILES.sha256.json").write_text(json.dumps(manifest, indent=2)+"\n")
        name = f"BTC-Miner-{VERSION}-{platform.system().lower()}-{platform.machine()}.zip"
        archive = Path(temp) / name
        with zipfile.ZipFile(archive, "w", zipfile.ZIP_DEFLATED) as bundle:
            for relative in package_names + ['FILES.sha256.json']:
                path = stage/relative
                bundle.write(path, path.relative_to(stage.parent))
        # Publish only after compilation and tests succeed. The temporary file
        # is on the destination filesystem so the final replacement is atomic.
        fd, pending = tempfile.mkstemp(prefix=".btc-build-", dir=output)
        os.close(fd)
        try:
            shutil.copyfile(archive, pending)
            os.replace(pending, output / name)
        finally:
            if os.path.exists(pending):
                os.unlink(pending)
        print(f"Built: {output / name}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
