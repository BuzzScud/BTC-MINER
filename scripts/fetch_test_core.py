"""CI-only explicit download of a pinned Core test binary; never starts it."""
import hashlib
import io
from pathlib import Path
import platform
import tarfile
import urllib.request
import zipfile
ROOT=Path(__file__).resolve().parent.parent
VERSION='31.1'
BASE='https://bitcoincore.org/bin/bitcoin-core-'+VERSION+'/'
def fetch(name):
    with urllib.request.urlopen(BASE+name,timeout=120) as response:return response.read()
def main():
    system=platform.system();machine=platform.machine().lower()
    if system=='Windows':suffix='win64.zip'; executable='bitcoind.exe'
    elif system=='Darwin':suffix=('arm64' if machine in ('arm64','aarch64') else 'x86_64')+'-apple-darwin.tar.gz';executable='bitcoind'
    else:suffix=('aarch64' if machine in ('arm64','aarch64') else 'x86_64')+'-linux-gnu.tar.gz';executable='bitcoind'
    name='bitcoin-'+VERSION+'-'+suffix
    checks={line.split()[-1].lstrip('*'):line.split()[0] for line in fetch('SHA256SUMS').decode().splitlines() if line.strip()}
    raw=fetch(name)
    if hashlib.sha256(raw).hexdigest()!=checks[name]:raise ValueError('Official archive checksum mismatch')
    member='bitcoin-'+VERSION+'/bin/'+executable
    if name.endswith('.zip'):
        with zipfile.ZipFile(io.BytesIO(raw)) as archive:data=archive.read(member)
    else:
        with tarfile.open(fileobj=io.BytesIO(raw),mode='r:gz') as archive:data=archive.extractfile(member).read()
    # Extract only the one expected regular executable, never arbitrary paths.
    path=ROOT/'.build'/'test-core'/executable;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data);path.chmod(0o755)
    (ROOT/'.build/core-path.txt').write_text(str(path)+'\n')
    print('Pinned Core test executable verified against checksums fetched from official HTTPS origin; no node started.')
if __name__=='__main__':main()
