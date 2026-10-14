"""Build the unchanged C sources using the platform compiler, then install locally."""
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent

def main():
    cmake = shutil.which('cmake')
    sibling = Path(sys.executable).parent/('cmake.exe' if os.name == 'nt' else 'cmake')
    if sibling.is_file(): cmake = str(sibling)
    if not cmake: raise SystemExit('CMake missing. Run setup again.')
    build = ROOT/'.build'/('native-'+platform.system()+'-'+platform.machine())
    command = [cmake, '-S', str(ROOT), '-B', str(build), '-DCMAKE_BUILD_TYPE=Release']
    if os.name == 'nt':
        command += ['-G', 'Visual Studio 17 2022', '-A', 'x64', '-T', 'ClangCL']
    subprocess.run(command, check=True)
    subprocess.run([cmake, '--build', str(build), '--config', 'Release', '--parallel', '2'], check=True)
    subprocess.run([cmake, '--install', str(build), '--config', 'Release', '--prefix', str(ROOT)], check=True)
    if sys.platform == 'darwin':
        for name in ('hasher_fast','abacus','rodsieve'):
            subprocess.run(['codesign','--force','--sign','-',str(ROOT/'native'/('lib'+name+'.dylib'))],check=True)

if __name__ == '__main__': main()
