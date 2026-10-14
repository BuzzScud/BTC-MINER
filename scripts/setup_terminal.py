"""Repeatable, prompted installation. Never starts a miner or Bitcoin Core."""
import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys
import venv

ROOT = Path(__file__).resolve().parent.parent

def yes(prompt, automatic=False):
    if automatic: return True
    if not sys.stdin.isatty(): return False
    return input(prompt+' [y/N]: ').strip().lower() in ('y','yes')

def run(command): subprocess.run(command, cwd=ROOT, check=True)

def compiler_ready():
    if os.name == 'nt':
        vswhere=Path(os.environ.get('ProgramFiles(x86)', 'C:/Program Files (x86)'))/'Microsoft Visual Studio/Installer/vswhere.exe'
        if not vswhere.is_file(): return False
        result=subprocess.run([str(vswhere),'-latest','-products','*','-requires',
            'Microsoft.VisualStudio.Component.VC.Llvm.ClangToolset','-property','installationPath'],capture_output=True,text=True)
        return bool(result.stdout.strip())
    return bool(shutil.which('cc') or shutil.which('clang'))

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--yes',action='store_true',help='Explicitly approve dependency installation (automation)')
    parser.add_argument('--no-wizard',action='store_true',help='Install and validate only')
    parser.add_argument('--environment',type=Path,help='Use an isolated update environment at this path')
    parser.add_argument('--no-install',action='store_true',help='Postpone if dependencies are missing; never install')
    parser.add_argument('--no-compiler-install',action='store_true',help='Never install system compiler packages')
    args=parser.parse_args()
    if sys.version_info<(3,9): raise SystemExit('Python 3.9+ required; install it and rerun setup.')
    if os.name == 'nt' and not sys.flags.utf8_mode:
        os.environ['PYTHONUTF8']='1'
        return subprocess.call([sys.executable,'-X','utf8',str(Path(__file__).resolve()),*sys.argv[1:]])
    os.chdir(ROOT)
    os.environ['BTC_VALIDATE_RUNTIME']='1'
    if not compiler_ready():
        if sys.platform=='darwin': command=['xcode-select','--install']
        elif os.name=='nt': command=['winget','install','--exact','--id','Microsoft.VisualStudio.2022.BuildTools',
            '--override','--wait --passive --add Microsoft.VisualStudio.Workload.VCTools --includeRecommended --add Microsoft.VisualStudio.Component.VC.Llvm.Clang --add Microsoft.VisualStudio.Component.VC.Llvm.ClangToolset']
        elif shutil.which('apt-get'): command=['sudo','apt-get','install','build-essential','python3-venv']
        else: raise SystemExit('Install a C11 compiler and Python venv support using your OS package manager, then rerun setup.')
        print('Compiler dependency command:', ' '.join(command))
        if args.no_install or args.no_compiler_install or not yes('Install compiler tools?',args.yes): raise SystemExit('Compiler tools are missing. Run setup to review and install the system compiler.')
        run(command)
        if not compiler_ready(): raise SystemExit('Finish the compiler installation, open a new terminal, and rerun setup.')
    env=(args.environment or ROOT/'.venv').resolve(); python=env/('Scripts/python.exe' if os.name=='nt' else 'bin/python')
    if not python.is_file():
        if args.no_install: raise SystemExit('Environment is missing; run a manual update or setup.')
        try: venv.EnvBuilder(with_pip=True).create(env)
        except Exception as error:
            raise SystemExit('Cannot create .venv. Install your OS Python venv/ensurepip package, then rerun. '+type(error).__name__)
    check=subprocess.run([str(python),'-c', "from importlib.metadata import version; from pathlib import Path; pairs=[line.split('==') for line in Path('scripts/requirements.txt').read_text().splitlines() if '==' in line]; assert all(version(name)==expected for name,expected in pairs)"],cwd=ROOT,capture_output=True)
    if check.returncode:
        print('The private .venv needs the pinned packages listed in scripts/requirements.txt.')
        if args.no_install or not yes('Download and install these dependencies?',args.yes): raise SystemExit('Dependencies need installation; run a manual update or setup.')
        run([str(python),'-m','pip','install','--disable-pip-version-check','-r','scripts/requirements.txt'])
    run([str(python),'scripts/sync_layout.py','--check'])
    run([str(python),'scripts/build_native.py'])
    run([str(python),'-B','-m','btcminer','self-test','--require-native'])
    run([str(python),'-B','scripts/verify_proof_evidence.py'])
    if args.environment is None:
        (ROOT/'.runtime.local.json').unlink(missing_ok=True)
    print('\nInstallation validated. Mining has NOT started.')
    if not args.no_wizard and sys.stdin.isatty(): run([str(python),'-m','btcminer','setup'])
    print('Next: '+('.\\btc-miner.cmd ui' if os.name=='nt' else './bin/btc-miner ui'))

if __name__=='__main__':
    try: raise SystemExit(main())
    except (KeyboardInterrupt,EOFError): raise SystemExit('\nSetup cancelled; rerun to resume.')
    except subprocess.CalledProcessError as error: raise SystemExit('Setup step failed (exit %s). Correct the error above and rerun.' % error.returncode)
