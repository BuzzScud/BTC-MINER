#!/usr/bin/env python3
"""Validate real Core acceptance and miner lifecycle on a disposable private chain."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import socket
import subprocess
import sys
import tempfile
import time
import fcntl
import pty
import select
import struct
import termios
from concurrent.futures import ThreadPoolExecutor

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from btcminer.native import Hasher, hash256
from btcminer import VERSION
from btcminer.protocol import core_work
from btcminer.connections import CoreConnection
from btcminer.difficulty import KEY
from btcminer.rpc import RPC
from btcminer.settings import DEFAULTS, atomic_json
from btcminer.thesis2 import Traversal


def wait_for(check, timeout=20):
    deadline = time.monotonic()+timeout
    while time.monotonic()<deadline:
        result = check()
        if result:
            return result
        time.sleep(.1)
    raise TimeoutError("Timed out waiting for regtest condition")


def control(project, command="status", **params):
    digest = hashlib.sha256(str(project.resolve()).encode()).hexdigest()[:16]
    path = Path(tempfile.gettempdir()) / f"btc-miner-{os.getuid()}-{digest}.sock"
    with socket.socket(socket.AF_UNIX,socket.SOCK_STREAM) as sock:
        sock.settimeout(3)
        sock.connect(str(path))
        sock.sendall((json.dumps({"command":command,**params})+"\n").encode())
        data = b""
        while b"\n" not in data:
            chunk = sock.recv(65536)
            if not chunk:
                raise RuntimeError("Miner control socket closed without a response")
            data += chunk
        return json.loads(data)


def terminal_smoke(project, env):
    master, slave = pty.openpty()
    fcntl.ioctl(slave,termios.TIOCSWINSZ,struct.pack("HHHH",40,120,0,0))
    ui = subprocess.Popen([sys.executable,"-B","-m","btcminer","ui"],cwd=project,
                          env=env,stdin=slave,stdout=slave,stderr=slave,start_new_session=True)
    os.close(slave)
    received = bytearray()
    def screen_contains(text):
        while select.select([master],[],[],.01)[0]:
            try:
                chunk = os.read(master,65536)
            except OSError:
                break  # PTYs may signal EOF as EIO after the child exits.
            if not chunk:
                break
            received.extend(chunk)
        return text in received
    try:
        wait_for(lambda: screen_contains(b"s start"),10)
        os.write(master,b"/difficulty up\r")
        wait_for(lambda: screen_contains(b"Saved; applies on next start."),10)
        wait_for(lambda: screen_contains("Test difficulty ×2".encode()),10)
        assert json.loads((project/"machine.local.json").read_text())[KEY] == 2
        try:
            assert not control(project).get("running")
        except OSError:
            pass
        os.write(master,b"\x1b")
        os.write(master,b"s")
        def running():
            screen_contains(b"BTC Miner")
            try:
                return control(project).get("blocks_accepted",0)>0
            except (OSError,ValueError):
                return False
        wait_for(running,15)
        wait_for(lambda: screen_contains(b"BTC miner started"),10)
        for action, expected in (("up",4),("down",2),("reset",1)):
            previous_pid = control(project)["pid"]
            received.clear()
            os.write(master,("/difficulty " + action + "\r").encode())
            wait_for(lambda: screen_contains(b"Miner restarted; session counters reset."),20)
            wait_for(lambda: screen_contains(f"Test difficulty ×{expected}".encode()),10)
            wait_for(running,15)
            snapshot = control(project)
            assert snapshot[KEY] == expected and snapshot["pid"] != previous_pid
            os.write(master,b"\x1b")
        # Stop via CLI to suppress the Desktop summary in an automated test.
        # The t shortcut's routing/queuing are covered by test_tui.py.
        subprocess.run([sys.executable,"-B","-m","btcminer","stop","--no-summary"],
                       cwd=project,env=env,check=True,capture_output=True,timeout=30)
        os.write(master,b"q")
        def closed():
            screen_contains(b"view closed")
            return ui.poll() is not None
        wait_for(closed,5)
        assert ui.returncode == 0
    finally:
        if ui.poll() is None:
            ui.terminate()
            try:
                ui.wait(timeout=5)
            except subprocess.TimeoutExpired:
                ui.kill(); ui.wait(timeout=5)
        os.close(master)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bitcoind", type=Path,
                        default=Path(shutil.which("bitcoind") or ROOT/".test-tools/bitcoin-31.1/bin/bitcoind"))
    parser.add_argument("--report", type=Path, default=ROOT/"validation/regtest.json")
    args = parser.parse_args()
    binary = args.bitcoind.expanduser().resolve()
    if not binary.is_file():
        parser.error("Supply --bitcoind /path/to/bitcoind; no existing node will be used")
    hasher = Hasher()
    if not hasher.lib or not hasher.fill_nonces:
        parser.error("Rebuild native hashing first: bash native/build.sh")
    evidence = {"network":"regtest", "strategy":"thesis2", "public_peers":False,
                "miner_version":VERSION,
                "core_version":subprocess.check_output([str(binary),"-version"],text=True).splitlines()[0],
                "checks":[]}
    with tempfile.TemporaryDirectory(prefix="btc-regtest-") as temp:
        folder = Path(temp)
        datadir = folder/"node"; datadir.mkdir()
        project = folder/"miner"; project.mkdir()
        for name in ("btcminer", "native", "bin", "research"):
            shutil.copytree(ROOT/name, project/name, ignore=shutil.ignore_patterns("__pycache__"))
        (project/"logs").mkdir()
        # Ask the OS for a free loopback port; Core will fail safely if another
        # process acquires it in the short interval before startup.
        with socket.socket() as port_socket:
            port_socket.bind(("127.0.0.1",0))
            port = port_socket.getsockname()[1]
        config = dict(DEFAULTS, network="regtest", connection="core", rpc_datadir=str(datadir),
                      rpc_port=port, strategy="thesis2", pause_on_active=0, keep_awake=False,
                      yield_cpu=False, supt_log=False, nonce_log=False, workers=2)
        rpc = RPC(config)
        env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
        def cli(*args, expected_code=0):
            result = subprocess.run([sys.executable,"-B","-m","btcminer",*args],cwd=project,
                                    env=env,capture_output=True,text=True,timeout=30)
            if result.returncode != expected_code:
                raise RuntimeError(result.stderr or result.stdout)
            if expected_code:
                return result.stderr
            return json.loads(result.stdout)
        def ready():
            try:
                return rpc.call("getblockchaininfo")
            except (ValueError,RuntimeError):
                if node.poll() is not None:
                    raise RuntimeError((folder/"node-output.log").read_text())
                return None
        node_log = (folder/"node-output.log").open("w")
        node = subprocess.Popen([str(binary),"-regtest",f"-datadir={datadir}","-server=1",
                                 "-listen=0","-connect=0","-dnsseed=0","-discover=0",
                                 "-rpcbind=127.0.0.1",f"-rpcport={port}","-fallbackfee=0.0002",
                                 "-printtoconsole=1"],stdout=node_log,stderr=subprocess.STDOUT)
        try:
            wait_for(ready)
            rpc.call("createwallet", ["miner-regtest"])
            address = rpc.call("getnewaddress", ["", "bech32"])
            config["address"] = address
            rpc.call("generatetoaddress", [101,address])
            destination = rpc.call("getnewaddress", ["", "bech32"])
            txid = rpc.call("sendtoaddress", [destination,1])
            tx = rpc.call("getrawtransaction", [txid,True])
            assert any(vin.get("txinwitness") for vin in tx["vin"]), "Expected a witness spend"
            template = rpc.call("getblocktemplate", [{"rules":["segwit"]}])
            assert txid in [tx["txid"] for tx in template["transactions"]]
            work = core_work(template,address,"regtest",bytes.fromhex("0102030405060708"),1)
            plan = Traversal(work.header,config["thesis2_step"],config["thesis2_prime"])
            nonce = None
            for task in hasher.traversal_batches(plan,16384):
                _, nonce = hasher.scan(work.header,work.target,**task)
                if nonce is not None:
                    break
            assert nonce is not None
            header = work.header[:76]+nonce.to_bytes(4,"little")
            block_hash = hash256(header)[::-1].hex()
            assert rpc.call("submitblock", [(header+work.data["body"]).hex()]) is None
            assert rpc.call("getbestblockhash") == block_hash
            assert txid in rpc.call("getblock", [block_hash])["tx"]
            evidence.update(accepted_block=block_hash, witness_txid=txid, nonce=nonce)
            evidence["checks"].append("THESIS2-built block with witness transaction accepted as active tip")
            print("PASS: Core accepted the THESIS2 block with a witness transaction",flush=True)

            # Exercise the production connection's stricter work target. Core's
            # actual header nBits and consensus target must remain untouched.
            stricter = CoreConnection(dict(config, **{KEY: 256}), lambda *a, **kw: None)
            stricter.template = rpc.call("getblocktemplate", [{"rules":["segwit"]}])
            stricter.connected = True
            work = stricter.work()
            assert work.target == work.network_target // 256
            assert work.header[72:76] == int(work.bits,16).to_bytes(4,"little")
            plan = Traversal(work.header,config["thesis2_step"],config["thesis2_prime"])
            nonce = None
            attempts = 0
            for task in hasher.traversal_batches(plan,16384):
                count, nonce = hasher.scan(work.header,work.target,**task)
                attempts += count
                if nonce is not None or attempts >= 1000000:
                    break
            assert nonce is not None, "No solution within bounded difficulty test"
            header = work.header[:76]+nonce.to_bytes(4,"little")
            digest = hashlib.sha256(hashlib.sha256(header).digest()).digest()
            assert int.from_bytes(digest,"little") <= work.target
            accepted, _, _ = stricter.submit(work,nonce)
            assert accepted and rpc.call("getbestblockhash") == digest[::-1].hex()
            evidence["difficulty_block"] = {"multiplier":256,"hash":digest[::-1].hex(),
                                            "mining_target":f"{work.target:064x}",
                                            "network_target":f"{work.network_target:064x}","bits":work.bits}
            evidence["checks"].append("Core accepted a production-connection block at local multiplier 256; hashlib independently verified stricter PoW and unchanged nBits")
            print("PASS: Core accepted stricter regtest work at ×256",flush=True)

            wrong = dict(config,network="mainnet",rpc_cookie=str(rpc.cookie()))
            try:
                RPC(wrong).check()
            except ValueError as e:
                assert "Network mismatch" in str(e)
            else:
                raise AssertionError("Wrong network was accepted")
            try:
                RPC(dict(config,rpc_cookie=str(folder/"missing-cookie"))).check()
            except ValueError as e:
                assert "cookie not found" in str(e)
            else:
                raise AssertionError("Missing cookie was accepted")
            evidence["checks"].append("Wrong-network and missing-cookie checks rejected")

            atomic_json(project/"machine.local.json",config)
            # Exercise the public CLI's non-mining readiness path against Core,
            # including a witness transaction and an unchanged active tip.
            rpc.call("sendtoaddress",[destination,0.1])
            tip_before = rpc.call("getbestblockhash")
            readiness = cli("doctor","--connect")
            assert readiness["core_ready"] and readiness["template_transactions"] > 0
            assert readiness["proposal"] == {"valid":True,"pow_checked":False,"broadcast":False}
            assert rpc.call("getbestblockhash") == tip_before
            assert not cli("status","--json").get("running")
            assert cli("workers","1")["config"]["workers"] == 1
            assert cli("workers","up")["config"]["workers"] == 2
            assert cli("workers","down")["config"]["workers"] == 1
            assert cli("workers")["workers"] == 1
            assert not cli("status","--json").get("running")
            evidence["checks"].append("Core proposal validates witness block without changing tip or starting miner; workers up/down while stopped")
            print("PASS: Candidate preflight and stopped worker controls",flush=True)
            for action, expected in (("up",2),("up",4),("down",2),("256",256),("reset",1)):
                result = cli("difficulty",action)
                assert result["multiplier"] == expected and not result["mining_restarted"]
                assert not cli("status","--json").get("running")
            evidence["checks"].append("Difficulty up/down/numeric/reset persisted while stopped without starting mining")
            for action, expected in ((str(1<<32),1<<32),("up",1<<32),("reset",1),("down",1)):
                result = cli("difficulty",action)
                assert result["multiplier"] == expected and not result["mining_restarted"]
            cli("difficulty","256")
            regtest_profile = json.loads((project/"machine.local.json").read_text())
            cli("network","testnet4")
            assert not cli("status","--json").get("running")
            report = cli("difficulty")
            assert not report["available"] and report["multiplier"]==1 and report["saved_multiplier"]==256
            for action in ("up","down","reset","2"):
                assert "require Bitcoin Core on regtest" in cli("difficulty",action,expected_code=1)
            cli("network","regtest","--check")
            restored = json.loads((project/"machine.local.json").read_text())
            assert restored == regtest_profile
            assert not cli("status","--json").get("running")
            cli("difficulty","reset")
            with ThreadPoolExecutor(max_workers=2) as executor:
                updates = list(executor.map(lambda _: cli("difficulty","up"), range(2)))
            assert sorted(r["multiplier"] for r in updates)==[2,4]
            assert cli("difficulty")["multiplier"]==4
            cli("difficulty","reset")
            evidence["checks"].append("Real CLI limits, public-network guards, regtest profile round trip, and concurrent stopped updates passed")
            with ThreadPoolExecutor(max_workers=2) as executor:
                starts = list(executor.map(lambda _: cli("start"), range(2)))
            assert starts[0]["pid"] == starts[1]["pid"], "Concurrent starts created different services"
            wait_for(lambda: control(project).get("blocks_accepted",0)>0)
            original_pid = control(project)["pid"]
            assert cli("start")["pid"] == original_pid
            assert control(project,"pause")["ok"]
            wait_for(lambda: control(project).get("state")=="PAUSED")
            paused_count = control(project)["hashes"]
            time.sleep(.3)
            assert control(project)["hashes"] == paused_count
            assert control(project,"resume")["ok"]
            wait_for(lambda: control(project).get("hashes",0)>paused_count)
            wait_for(lambda: control(project).get('resident_abacus',{}).get('chain_tip_changes',0)>0)
            resident=control(project)['resident_abacus']
            assert resident['resident'] and resident['native_projection']
            assert resident['jobs_bound']>1 and resident['core_primes']==[11,19,71,97,109]
            evidence['resident_abacus']=resident
            evidence['checks'].append('Resident model reused across Core jobs and actual parent-hash changes')
            pruning=control(project)['pruning']
            assert pruning['enabled'] and pruning['model']=='bitcoin-sha256d-v1'
            assert pruning['jobs_checked']>0 and pruning['candidates_checked']>0
            evidence['pruning']=pruning
            evidence['checks'].append('Enabled full-SHA pruning path processed real Core jobs; unknown work retained and blocks accepted')
            evidence["checks"].append("Concurrent start/attach/pause/resume with real Core work")
            print("PASS: Start, attach, pause, and resume",flush=True)
            # Malformed local messages must not terminate a running service.
            digest = hashlib.sha256(str(project.resolve()).encode()).hexdigest()[:16]
            socket_path = Path(tempfile.gettempdir())/f"btc-miner-{os.getuid()}-{digest}.sock"
            with socket.socket(socket.AF_UNIX,socket.SOCK_STREAM) as client:
                client.settimeout(3); client.connect(str(socket_path)); client.sendall(b"[]\n")
                assert json.loads(client.recv(4096))["ok"] is False
            assert control(project)["pid"] == original_pid
            evidence["checks"].append("Malformed control message did not interrupt mining")
            restarted = cli("restart")
            assert restarted["pid"] != original_pid
            original_pid = restarted["pid"]
            wait_for(lambda: control(project).get("blocks_accepted",0)>0)
            evidence["checks"].append("Restart replaced the service and resumed Core mining")
            cli("workers","2")
            wait_for(lambda: control(project).get("workers")==2 and
                     control(project).get("blocks_accepted",0)>0)
            assert control(project)["pid"] != original_pid
            original_pid = control(project)["pid"]
            evidence["checks"].append("Worker change while mining restarted once and resumed with two workers")
            for action, expected in (("256",256),("up",512),("down",256),("reset",1)):
                result = cli("difficulty",action)
                assert result["mining_restarted"] and result["multiplier"] == expected
                snapshot = wait_for(lambda: (s if s.get(KEY)==expected and s.get("blocks_accepted",0)>0 else None)
                                    if (s := control(project)) else None)
                assert snapshot["pid"] != original_pid
                original_pid = snapshot["pid"]
                unchanged = cli("difficulty",str(expected))
                assert not unchanged["changed"] and not unchanged["mining_restarted"]
                for bad in ("0","1.5","4294967297"):
                    cli("difficulty",bad,expected_code=1)
                assert control(project)["pid"] == original_pid
                assert control(project)[KEY] == expected
            evidence["checks"].append("Live difficulty numeric/up/down/reset restarted mining with matching snapshot multipliers and new Core-accepted blocks")
            with ThreadPoolExecutor(max_workers=2) as executor:
                updates = list(executor.map(lambda _: cli("difficulty","up"), range(2)))
            assert sorted(r["multiplier"] for r in updates)==[2,4]
            wait_for(lambda: control(project).get(KEY)==4 and control(project).get("blocks_accepted",0)>0)
            cli("difficulty","reset")
            evidence["checks"].append("Live no-op and invalid difficulty commands preserved the process; concurrent up commands serialized without lost updates")
            print("PASS: Difficulty controls while stopped and mining",flush=True)
            # Stop without writing a test summary onto the user's Desktop.
            cli("stop","--no-summary")
            wait_for(lambda: not cli("status","--json").get("running"))
            # The normal restart path must also wait for supervisor lock release.
            cli("start")
            assert control(project)["pid"] != original_pid
            cli("stop","--no-summary")
            wait_for(lambda: not cli("status","--json").get("running"))
            time.sleep(.5)
            assert not cli("status","--json").get("running")
            evidence["checks"].append("Stop, subsequent start, and final stopped state")
            print("PASS: Stop and subsequent start; service remains stopped",flush=True)
            # Verify the configured automatic stop through the real supervisor.
            # Keep its automatically generated summary inside this disposable fixture.
            service_file = project/"btcminer/service.py"
            service_source = service_file.read_text()
            assert 'write_summary = [True]' in service_source
            service_file.write_text(service_source.replace('write_summary = [True]', 'write_summary = [False]', 1))
            before_height = rpc.call('getblockcount')
            before_tip = rpc.call('getbestblockhash')
            cli('config','set','stop_after_block=on')
            cli('start')
            wait_for(lambda: not cli('status','--json').get('running'),20)
            stopped = cli('status','--json')
            assert stopped['blocks_accepted'] == 1, stopped
            assert rpc.call('getblockcount') == before_height+1
            accepted_tip=rpc.call('getbestblockhash')
            assert rpc.call('getblockheader',[accepted_tip])['previousblockhash']==before_tip
            assert stopped['resident_abacus']['previous_block_hash']==before_tip
            evidence['resident_chain_link']={'parent':before_tip,'accepted_child':accepted_tip,
                                             'model_parent_matches':True}
            # Supervisor exits on the engine's clean return, instead of restarting.
            lock_path = project/'logs/supervisor.lock'
            def supervisor_finished():
                with lock_path.open('a+') as lock:
                    try:
                        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
                    except BlockingIOError:
                        return False
                    return True
            wait_for(supervisor_finished)
            assert not cli('status','--json').get('running')
            evidence['checks'].append('stop_after_block: exactly one real Core block accepted, engine stopped, supervisor exited without restart; fixture only suppressed Desktop summary')
            print('PASS: Exactly one accepted block automatically stops miner and supervisor',flush=True)
            cli('config','set','stop_after_block=off')
            service_file.write_text(service_source)
            terminal_smoke(project,env)
            evidence["checks"].append("Real PTY: stopped /difficulty up saved without mining; s started mining; live /difficulty up/down/reset updated the header and produced accepted blocks; scripted stop and q closed cleanly")
            print("PASS: Terminal dashboard, start, and typed difficulty controls against regtest",flush=True)
            evidence["ok"] = True
            evidence["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ",time.gmtime())
            sources = list((ROOT/"btcminer").rglob("*.py")) + [ROOT/"native/hasher_fast.c"]
            evidence["source_sha256"] = {str(path.relative_to(ROOT)):hashlib.sha256(path.read_bytes()).hexdigest()
                                         for path in sorted(sources)}
            evidence["test_script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        finally:
            try:
                cli("stop","--no-summary")
            except (OSError,ValueError,RuntimeError,subprocess.TimeoutExpired):
                pass
            # Record stop even when the service is between watchdog attempts.
            (project/"logs/stop.request").touch()
            try:
                rpc.call("stop")
            except (OSError,ValueError,RuntimeError):
                node.terminate()
            try:
                node.wait(timeout=15)
            except subprocess.TimeoutExpired:
                node.kill(); node.wait(timeout=5)
            node_log.close()
    args.report.parent.mkdir(parents=True,exist_ok=True)
    args.report.write_text(json.dumps(evidence,indent=2)+"\n")
    print(f"Evidence: {args.report}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
