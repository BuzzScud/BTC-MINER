"""Project browser fixtures never read operational settings or control mining."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from btcminer import project_browser as browser
from btcminer import cli


class ProjectBrowserTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        (self.root / 'btcminer').mkdir()
        self.source = self.root / 'btcminer/example.py'
        self.source.write_text('value = 19\n')
        (self.root / 'FILES.sha256.json').write_text(json.dumps({
            'btcminer/example.py': hashlib.sha256(self.source.read_bytes()).hexdigest(),
            'missing.py': '0' * 64,
        }))

    def data(self, path):
        text = Path(path).read_text()
        payload = text.split('<script id="project-data" type="application/json">', 1)[1].split('</script>', 1)[0]
        return json.loads(payload), text

    def test_inventory_hidden_nested_and_symlinks(self):
        (self.root / '.hidden').mkdir()
        (self.root / '.hidden/note.txt').write_text('hi')
        (self.root / 'loop').symlink_to(self.root, target_is_directory=True)
        result, _ = browser.inventory(self.root)
        self.assertEqual(result['files'], 3)
        self.assertEqual(sum(r[2] == 'symlink' for r in result['rows']), 1)
        self.assertEqual(result['checks']['btcminer/example.py']['status'], 'match')
        self.assertEqual(result['checks']['missing.py']['status'], 'missing')

    def test_math_ownership_keeps_mining_consumers_separate(self):
        for name in ('btcminer/product_tree_crt.py', 'btcminer/capacity_reals.py',
                     'math-library/python/product_tree_crt.py',
                     'math-library/native/latcalc/src/bigint.c',
                     'native/latcalc/src/bigint.c', 'tests/test_shared_abacus.py',
                     'research/formula-catalogue.json', 'reference/example.lean',
                     'validation/api-library-completion-example/audit/cards.json'):
            self.assertEqual(browser.project_part(name), 1, name)
        for name in ('btcminer/engine.py', 'btcminer/thesis2.py', 'btcminer/pruning.py',
                     'src/workers/engine.py', 'src/pool/protocol.py',
                     'native/hasher_fast.c', 'tests/test_pool_failover.py',
                     'machine.local.json', '.test-tools/tool/bin/example',
                     'validation/api-library-completion-example/api/login.json',
                     'validation/api-library-completion-example/release/miner.zip'):
            self.assertEqual(browser.project_part(name), 2, name)

    def test_declared_alias_checks_indexed_source_and_navigates_to_it(self):
        (self.root/'src/workers').mkdir(parents=True)
        target=self.root/'src/workers/example.py'
        self.source.rename(target)
        self.source.symlink_to('../src/workers/example.py')
        (self.root/'docs').mkdir()
        (self.root/'docs/project-layout.json').write_text(json.dumps({
            'schema':'btc-project-layout/v1', 'files':[{
                'compatibility_path':'btcminer/example.py',
                'source_path':'src/workers/example.py'}]}))
        data,_=browser.inventory(self.root)
        self.assertEqual(data['checks']['btcminer/example.py']['status'],'match')
        self.assertEqual(data['aliases']['btcminer/example.py'],'src/workers/example.py')
        self.assertIn('src/workers/example.py',data['previews'])
        browser.generate(self.root)
        regenerated=browser.generate(self.root)
        current,_=self.data(regenerated['path'])
        self.assertIsNotNone(current['previous'])
        self.assertEqual(current['checks']['btcminer/example.py']['status'],'match')
        target.write_text('value = 20\n')
        data,_=browser.inventory(self.root)
        self.assertEqual(data['checks']['btcminer/example.py']['status'],'mismatch')
        self.source.unlink()
        self.source.symlink_to('../machine.local.json')
        data,_=browser.inventory(self.root)
        self.assertEqual(data['checks']['btcminer/example.py']['status'],'not_regular')

    def test_partition_covers_all_files_once_and_missing_paths(self):
        (self.root/'btcminer/pqmath.py').write_text('value = 19')
        (self.root/'FILES.sha256.json').write_text(json.dumps({'btcminer/rodmath.py': '0'*64}))
        data, _ = browser.inventory(self.root)
        rows = [r for r in data['rows'] if r[2] == 'file']
        self.assertTrue(all(r[6] in (1, 2) for r in rows))
        self.assertEqual(sum(data['part_files']), data['files'])
        self.assertEqual(data['part_files'][0], 1)
        self.assertEqual(data['absent_parts']['btcminer/rodmath.py'], 1)

    def test_sensitive_files_not_embedded_and_html_escaped(self):
        (self.root / 'machine.local.json').write_text('{"password":"PRIVATE_SENTINEL"}')
        (self.root / 'logs').mkdir()
        (self.root / 'logs/account.txt').write_text('LOG_SECRET')
        self.source.write_text('# </script><script>window.attacked=true</script>\n')
        result = browser.generate(self.root)
        data, html = self.data(result['path'])
        self.assertNotIn('PRIVATE_SENTINEL', html)
        self.assertNotIn('LOG_SECRET', html)
        self.assertNotIn('</script><script>window.attacked', html)
        self.assertIn('window.attacked', data['previews']['btcminer/example.py'])

    def test_changes_add_remove_and_tracked_hash(self):
        _, state = browser.inventory(self.root)
        self.source.write_text('value = 71\n')
        (self.root / 'added.txt').write_text('added')
        data, _ = browser.inventory(self.root, previous=state)
        self.assertEqual(data['checks']['btcminer/example.py']['status'], 'mismatch')
        self.assertEqual(next(r[5] for r in data['rows'] if r[1] == 'added.txt'), 'added')
        self.source.unlink()
        data, _ = browser.inventory(self.root, previous=state)
        self.assertIn('btcminer/example.py', data['removed'])
        self.assertEqual(data['checks']['btcminer/example.py']['status'], 'missing')

    def test_existing_html_preserved_and_output_not_indexed(self):
        target = self.root / 'report.html'
        target.write_text('user work')
        with self.assertRaisesRegex(ValueError, 'Refusing'):
            browser.generate(self.root, target)
        self.assertEqual(target.read_text(), 'user work')
        result = browser.generate(self.root)
        result = browser.generate(self.root)
        data, _ = self.data(result['path'])
        self.assertNotIn('PROJECT-BROWSER.html', [r[1] for r in data['rows']])
        self.assertNotIn(browser.STATE_NAME, [r[1] for r in data['rows']])
        self.assertIsNotNone(data['previous'])

    def test_symlink_content_and_invalid_manifest_not_read(self):
        with tempfile.TemporaryDirectory() as external:
            secret = Path(external) / 'secret'
            secret.write_text('OUTSIDE_SECRET')
            self.source.unlink()
            self.source.symlink_to(secret)
            data, _ = browser.inventory(self.root)
            self.assertEqual(data['checks']['btcminer/example.py']['status'], 'not_regular')
            self.assertNotIn('btcminer/example.py', data['previews'])
            (self.root / 'FILES.sha256.json').write_text(json.dumps({'../secret': '0'*64}))
            data, _ = browser.inventory(self.root)
            self.assertEqual(data['checks'], {})
            self.assertIn('Invalid manifest', data['issues'][0])

    def test_preview_limit_and_binary_files(self):
        self.source.write_bytes(b'\0binary')
        (self.root / 'large.py').write_text('x' * (browser.TEXT_LIMIT + 1))
        data, _ = browser.inventory(self.root)
        self.assertEqual(data['previews'], {})

    def test_cli_is_independent_of_miner_settings(self):
        with patch.object(cli, 'ROOT', self.root), patch.object(cli, 'load', side_effect=AssertionError('settings read')), patch.object(browser.webbrowser, 'open') as opened, patch.object(cli, 'print_result') as output:
            self.assertEqual(cli.main(['files', '--no-open']), 0)
            opened.assert_not_called()
            self.assertTrue(output.call_args.args[0]['ok'])

    def test_watch_bounds_and_browser_open(self):
        with self.assertRaisesRegex(ValueError, 'at least 10'):
            browser.launch(self.root, watch=1)
        with patch.object(browser.webbrowser, 'open', return_value=True) as opened:
            result = browser.launch(self.root)
            opened.assert_called_once_with(Path(result['path']).as_uri())
        with patch.object(browser.time, 'sleep', side_effect=KeyboardInterrupt), patch('builtins.print'):
            with self.assertRaises(KeyboardInterrupt):
                browser.launch(self.root, open_browser=False, watch=10)


if __name__ == '__main__':
    unittest.main()
