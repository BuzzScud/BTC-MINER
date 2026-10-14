"""The recorded viewer command must remain independent of mining controls."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch

from btcminer.cli import main
from btcminer.tui import App


class TargetViewTests(unittest.TestCase):
    def test_command_opens_only_the_local_recorded_page(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            page = root/'src/ui/network_difficulty.html'
            page.parent.mkdir(parents=True)
            page.write_text('<!doctype html><title>Recorded snapshot</title>')
            with patch('btcminer.cli.ROOT', root), patch('webbrowser.open', return_value=True) as browser, \
                 patch('btcminer.cli.load', side_effect=AssertionError('settings access')), \
                 patch('btcminer.cli.service') as service, contextlib.redirect_stdout(io.StringIO()) as out:
                self.assertEqual(main(['target','dif']), 0)
                browser.assert_called_once_with(page.as_uri())
                self.assertEqual(service.mock_calls, [])
                self.assertEqual(json.loads(out.getvalue())['mode'], 'recorded prototype')

    def test_no_open_and_missing_page(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            with patch('btcminer.cli.ROOT', root), patch('webbrowser.open') as browser, \
                 patch('btcminer.cli.load', side_effect=AssertionError('settings access')), \
                 contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(main(['target','dif','--no-open']), 1)
                browser.assert_not_called()
            page = root/'src/ui/network_difficulty.html'
            page.parent.mkdir(parents=True)
            page.write_text('snapshot')
            with patch('btcminer.cli.ROOT', root), patch('webbrowser.open') as browser, \
                 contextlib.redirect_stdout(io.StringIO()) as out:
                self.assertEqual(main(['target','dif','--no-open']), 0)
                browser.assert_not_called()
                self.assertFalse(json.loads(out.getvalue())['browser_open_requested'])

    def test_typed_slash_command_preserves_arguments(self):
        app = App.__new__(App)
        app.execute = Mock()
        app.command('/target dif')
        app.execute.assert_called_once_with(['target','dif'], '/target')

    def test_invalid_target_view_cannot_dispatch(self):
        with patch('btcminer.cli.service') as service, contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit) as error:
                main(['target', 'up'])
            self.assertEqual(error.exception.code, 2)
            self.assertEqual(service.mock_calls, [])


if __name__ == '__main__':
    unittest.main()
