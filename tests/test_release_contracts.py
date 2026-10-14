"""RELEASE-01 package and registry gate checks; see ../MASTER_PLAN.md.

MUST copy only explicit public inputs to disposable staging. These tests never
start the live miner/node, invoke Lean or update the original metadata.
"""
import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from btcminer import ROOT
from btcminer.proof_evidence import EvidenceError, verify

SPEC = importlib.util.spec_from_file_location('miner_release_build', ROOT/'scripts/build.py')
build = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(build)


class ReleaseContracts(unittest.TestCase):
    def fixture(self):
        temporary = tempfile.TemporaryDirectory(prefix='miner-release-contract-')
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        proof = verify(ROOT)
        for name in build.release_files(ROOT,proof)+['FILES.sha256.json']:
            destination = root/name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT/name,destination)
        return root

    def test_explicit_export_includes_report_gate_and_sources(self):
        proof = verify(ROOT)
        names = set(build.release_files(ROOT,proof))
        self.assertIn('research/proof-evidence/report.html',names)
        self.assertIn('scripts/verify_proof_evidence.py',names)
        self.assertTrue(set(proof['manifest']['workspace_sources']) <= names)
        self.assertTrue(all('research/proof-evidence/'+r in names for r in proof['manifest']['objects']))
        self.assertFalse(any(Path(name).parts[0] in ('logs','node','.venv') or name.endswith('settings.json') for name in names))

    def test_staged_release_is_portable(self):
        result = build.check_release_inputs(self.fixture())
        self.assertEqual(result['status'],'passed')

    def test_layout_sources_and_compatibility_paths_cannot_diverge(self):
        root=self.fixture()
        layout=json.loads((root/'docs/project-layout.json').read_text())
        self.assertTrue(layout['files'])
        entry=layout['files'][0]
        source=root/entry['source_path']
        source.write_text(source.read_text()+'\n# mismatched canonical source\n')
        with self.assertRaisesRegex(EvidenceError,'layout alias differs'):
            build.check_release_inputs(root,check_manifest=False)

    def test_every_runtime_source_is_exported_in_both_layout_paths(self):
        names=set(build.release_files(ROOT,verify(ROOT)))
        for entry in json.loads((ROOT/'docs/project-layout.json').read_text())['files']:
            self.assertIn(entry['source_path'],names)
            self.assertIn(entry['compatibility_path'],names)
            self.assertEqual((ROOT/entry['source_path']).read_bytes(),
                             (ROOT/entry['compatibility_path']).read_bytes())

    def test_source_change_blocks_release(self):
        root = self.fixture()
        with (root/'btcminer/research_system.py').open('a') as stream:
            stream.write('\n# unreviewed source change\n')
        with self.assertRaisesRegex(EvidenceError,'Stale release input'):
            build.check_release_inputs(root)

    def test_missing_registry_root_blocks_release(self):
        root = self.fixture()
        path = root/'research/proof-registry.json'
        registry = json.loads(path.read_text())
        registry['theorems'].pop()
        path.write_text(json.dumps(registry))
        with self.assertRaisesRegex(EvidenceError,'Proof registry theorem inventory'):
            build.check_release_inputs(root,check_manifest=False)

    def test_unimplemented_translation_cannot_be_promoted(self):
        root = self.fixture()
        path = root/'research/proof-registry.json'
        registry = json.loads(path.read_text())
        row = next(row for row in registry['theorems'] if row['execution_status']=='proof_only_translation_unimplemented')
        row['execution_status']='accepted_closed_Nat_translation'
        path.write_text(json.dumps(registry))
        with self.assertRaisesRegex(EvidenceError,'Proof registry scope'):
            build.check_release_inputs(root,check_manifest=False)
