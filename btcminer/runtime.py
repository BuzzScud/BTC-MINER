"""Select a validated update environment without modifying the original .venv."""
import json
import os
from pathlib import Path
import subprocess
import sys


def interpreter(root):
    root = Path(root).resolve()
    pointer = root / '.runtime.local.json'
    if not pointer.exists():
        return sys.executable
    value = json.loads(pointer.read_text())['environment']
    relative = Path(value)
    if relative.is_absolute() or '..' in relative.parts or relative.parts[:1] != ('.updates',):
        raise ValueError('Invalid local runtime selection; run update --rollback or setup.')
    folder = (root / relative).resolve()
    if root / '.updates' not in folder.parents:
        raise ValueError('Runtime environment must stay inside this installation.')
    python = folder / ('Scripts/python.exe' if os.name == 'nt' else 'bin/python')
    if not python.is_file():
        raise ValueError('Selected runtime is missing; run update --rollback or setup.')
    return str(python)


def handoff(python, argv, *, updated=False):
    env = dict(os.environ)
    if updated:
        from . import ROOT
        env['BTC_UPDATE_DONE'] = str(ROOT)
    command = [str(python), '-m', 'btcminer', *argv]
    if os.name == 'nt':
        return subprocess.call(command, env=env)
    os.execve(str(python), command, env)


def main(argv=None):
    from . import ROOT
    argv = list(sys.argv[1:] if argv is None else argv)
    # Recovery must work even when a selected environment has disappeared.
    recovery = argv[:1] == ['update'] and '--rollback' in argv
    if not recovery and not os.environ.get('BTC_VALIDATE_RUNTIME'):
        python = interpreter(ROOT)
        if os.path.abspath(python) != os.path.abspath(sys.executable):
            return handoff(python, argv)
    if argv[:1] in (['role'], ['release'], ['update']):
        from .releases import main as release_main
        return release_main(argv)
    if (not argv or argv == ['ui']) and os.environ.get('BTC_UPDATE_DONE') != str(ROOT):
        from .releases import Repository, UpdateError
        repo = Repository(ROOT)
        try:
            if repo.available() and repo.role() == 'follower':
                repo.update(on_open=True)
        except (UpdateError, OSError, ValueError) as error:
            repo.notice('Update postponed: ' + str(error))
        return handoff(interpreter(ROOT), argv, updated=True)
    if (ROOT/'.updates/transaction.json').exists() and (not argv or argv[:1] in (['ui'],['start'],['restart'])):
        print('An update is switching files or needs recovery. Wait for it, or run btc-miner update --rollback.',file=sys.stderr)
        return 1
    from .cli import main as cli_main
    return cli_main(argv)
