import argparse
import getpass
import json
import os
import shlex
import subprocess
import sys
from pathlib import Path
from . import ROOT, VERSION
from . import service
from .settings import CONFIG, DEFAULTS, LOGS, load, save, changes, public, ALIASES

def print_result(value):
    print(json.dumps(value,indent=2,ensure_ascii=False))

def configure(assignments=None, unset=None, reset=False):
    c = load()
    if reset:
        c = dict(DEFAULTS)
    elif unset:
        for key in unset:
            key = ALIASES.get(key.lower(),key.lower())
            if key not in DEFAULTS:
                raise ValueError(f"Unknown setting: {key}")
            c[key] = DEFAULTS[key]
    else:
        c = changes(c,assignments or [])
    running = service.status().get("running",False)
    save(c)
    if running:
        try:
            service.validate_start(c)
        except ValueError:
            service.stop(summary=False)
            return {"message":"Saved. Miner stopped because the new connection needs setup.","config":public(c)}
        service.restart()
    return {"message":"Saved; running miner restarted" if running else "Saved; applies on next start", "config":public(c)}

def performance(value):
    c = load(); cores = os.cpu_count() or 8
    value = value.lower()
    if value == "up":
        n = min(cores,c["workers"]+1)
    elif value == "down":
        n = max(1,c["workers"]-1)
    elif value in ("eco","auto","max"):
        n = {"eco":1,"auto":min(2,cores),"max":cores}[value]
    elif value.endswith("%"):
        percentage = int(value[:-1])
        if not 1<=percentage<=100:
            raise ValueError("CPU share must be 1–100%")
        n = max(1,round(cores*percentage/100))
    else:
        n = int(value)
    if c.get('resource_control') and service.status().get('running'):
        return service.request('resource_workers',workers=n)
    return configure([f"workers={n}"])

def setup():
    from .onboarding import wizard
    return wizard()


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    if argv[:1] == ['cluster']:
        from .distribution.cli import main as cluster_main
        return cluster_main(argv[1:])
    parser = argparse.ArgumentParser(prog="btc-miner",description="BTC Miner · native Apple Silicon mining and thesis math")
    parser.add_argument("--version",action="version",version=VERSION)
    sub = parser.add_subparsers(dest="command")
    sub.add_parser("ui"); sub.add_parser("setup")
    sub.add_parser('cluster',help='Fractal node workers, duplex buffers and isolated peer tests')
    p = sub.add_parser("hub", help="Open the local Bitcoin Algorithm Observatory")
    p.add_argument('--path'); p.add_argument('--no-open', action='store_true')
    p.add_argument('--port', type=int, default=63218)
    p = sub.add_parser("lab", help="Open the live local scale and difficulty modelling lab")
    p.add_argument('--no-open', action='store_true')
    p.add_argument('--port', type=int, default=63219)
    p = sub.add_parser("target", help="Open the recorded network difficulty HTML prototype")
    p.add_argument('view', choices=('dif',))
    p.add_argument('--no-open', action='store_true', help='Print the local page path without opening a browser')
    p = sub.add_parser("start"); p.add_argument("--connection",choices=("core","pool")); p.add_argument("--strategy",choices=("thesis2","thesis","linear","hybrid")); p.add_argument("--workers",type=int); p.add_argument("--dry-run",action="store_true")
    p = sub.add_parser("stop"); p.add_argument("--no-summary",action="store_true")
    sub.add_parser("restart"); sub.add_parser("pause"); sub.add_parser("resume")
    p = sub.add_parser("status"); p.add_argument("--json",action="store_true")
    p = sub.add_parser("perf",aliases=["workers"]); p.add_argument("value",nargs="?")
    p = sub.add_parser("difficulty",help="Show or change the local Core regtest work multiplier")
    p.add_argument("value",nargs="?",help="up, down, reset, or an integer multiplier (minimum 1)")
    p = sub.add_parser("network",help="Show or switch network; a switch stops mining")
    p.add_argument("name",nargs="?",choices=("mainnet","testnet4","testnet","regtest"))
    p.add_argument("--check",action="store_true",help="Test Core RPC and selected chain without starting mining")
    p = sub.add_parser("config"); p.add_argument("action",choices=("show","set","unset","reset","edit","path"),nargs="?",default="show"); p.add_argument("values",nargs="*")
    p = sub.add_parser("logs"); p.add_argument("--lines",type=int,default=30); p.add_argument("--service",action="store_true")
    p = sub.add_parser("doctor"); p.add_argument("--connect",action="store_true")
    p = sub.add_parser("self-test"); p.add_argument("--require-native",action="store_true")
    sub.add_parser("pruning",help="Show live lossless filter settings and counters")
    p = sub.add_parser("provider", help="Discover and use the Thesis calculator API")
    p.add_argument("action", choices=("capabilities", "refresh", "formulas", "calculate", "watch", "check", "hash"), nargs="?", default="capabilities")
    p.add_argument("--base-url", default=os.environ.get("BTC_PROVIDER_URL", ""))
    p.add_argument("--user", default="")
    p.add_argument("--query", help="Search formulas visible to the selected account")
    p.add_argument("--expression", help="Expression for provider calculate")
    p.add_argument("--variables", default="{}", help="JSON object for expression variables")
    p.add_argument("--header-hex", help="Exact 80-byte Bitcoin header as 160 hex characters for provider hash")
    p.add_argument("--hash-mode", choices=("compare", "remote"), default="compare",
                   help="Compare remote SHA256d with local hashing, or return the remote computation alone")
    p.add_argument("--seconds", type=float, default=10, help="Bounded watch duration, maximum 60 seconds")
    p.add_argument("--output", help="Save redacted JSON; refresh defaults to logs/provider/latest.json")
    p = sub.add_parser("abacus",help="Resident math, compression, recurrence and scoped toy checks")
    p.add_argument("action",choices=("inspect","precision","compression","recurrence","toy","study","claims","calculate","carries","theorems","formulas"),nargs="?",default="inspect")
    p.add_argument("--query",help="Search the retained formula catalogue without executing provider prose")
    p.add_argument("--theorem",help="Fully qualified name from the executable archive catalogue")
    p.add_argument("--claim",help="JSON claim, e.g. [\"eq\",[\"mul\",\"x\",\"x\"],361]")
    p.add_argument("--variables",default="{}",help="JSON integer variable assignments")
    p.add_argument("--precision-bits",type=int,default=8192)
    p.add_argument("--width",type=int,default=32); p.add_argument("--rounds",type=int,default=32)
    p.add_argument("--nonce-bits",type=int,default=10); p.add_argument("--difficulty",type=int,default=10)
    p.add_argument("--budget-ms",type=int,default=2000); p.add_argument("--seed",type=int,default=30)
    p.add_argument("--scale",type=int,default=0)
    p = sub.add_parser("math"); p.add_argument("action",choices=("inspect",),nargs="?",default="inspect"); p.add_argument("--height",type=int,default=900000); p.add_argument("--bits",default="17034219"); p.add_argument("--strategy",choices=("thesis2","thesis","linear","hybrid"))
    p = sub.add_parser("benchmark",aliases=["bench"]); p.add_argument("--seconds",type=float,default=3); p.add_argument("--sweep",action="store_true"); p.add_argument("--strategy",choices=("thesis2","linear"))
    p = sub.add_parser("backtest"); p.add_argument("--blocks",type=int,default=100); p.add_argument("--strategy",choices=("thesis2","thesis"))
    p = sub.add_parser("probe"); p.add_argument("--window",choices=("71","512","all"),default="512"); p.add_argument("--source",choices=("both","stream_a","stream_b"),default="both"); p.add_argument("--compare",action="store_true"); p.add_argument("--z0",action="store_true")
    p = sub.add_parser("files", help="Generate and open the local HTML project browser")
    p.add_argument("--output", help="HTML destination (default: PROJECT-BROWSER.html)")
    p.add_argument("--no-open", action="store_true", help="Generate without opening a browser")
    p.add_argument("--watch", type=int, default=0, metavar="SECONDS", help="Regenerate continuously (minimum 10 seconds)")
    args = parser.parse_args(argv)
    try:
        if args.command == "provider":
            from .provider import run_command
            result = run_command(args)
            print_result(result)
            return 0 if result.get('ok', True) else 1
        if args.command == "target":
            import webbrowser
            page = ROOT/'src/ui/network_difficulty.html'
            if not page.is_file():
                raise ValueError('Network difficulty prototype is missing from src/ui/network_difficulty.html')
            opened = False if args.no_open else webbrowser.open(page.as_uri())
            print_result({'ok': True, 'path': str(page), 'mode': 'recorded prototype',
                          'browser_open_requested': opened,
                          'message': 'Recorded network difficulty page; use its three tabs and source switch. No automatic refresh.'})
            return 0
        if args.command == "files":
            from .project_browser import launch
            print_result(launch(ROOT, args.output, open_browser=not args.no_open, watch=args.watch))
            return 0
        c = load(); command = args.command or "ui"
        if command == "ui":
            from .tui import run
            return run()
        if command == "hub":
            from .hub import launch
            print_result(launch(args.path, not args.no_open, args.port))
            return 0
        if command == "lab":
            from .modelling import launch
            print_result(launch(args.port, not args.no_open))
            return 0
        if command == "setup":
            result = setup()
        elif command == "start":
            if args.dry_run:
                from .diagnostics import doctor
                print_result(doctor(c))
                return 0
            pairs = [f"{k}={getattr(args,k)}" for k in ("connection","strategy","workers") if getattr(args,k) is not None]
            if pairs:
                configure(pairs)
            result = service.start()
            result = {k:v for k,v in result.items() if k not in ("events",)}
        elif command == "stop":
            result = service.stop(summary=not args.no_summary)
        elif command == "restart":
            result = service.restart()
        elif command in ("pause","resume"):
            result = service.request(command)
        elif command == "status":
            result = service.status()
            if not args.json:
                print(f"BTC MINER · {result['state']}\nConnection: {result.get('connection',c['connection'])} · {result.get('endpoint','—')}\n"
                      f"Strategy: {result.get('strategy',c['strategy'])} · Workers: {result.get('workers',c['workers'])}\n"
                      f"Hashes: {result.get('hashes',0):,} · 10s: {result.get('rates',{}).get('10',0):,.0f} H/s\n"
                      f"Shares: {result.get('shares_accepted',0):,} accepted / {result.get('shares_rejected',0):,} rejected · Blocks: {result.get('blocks_accepted',0)}")
                if result.get("paused_reason"):
                    print("Paused: " + result["paused_reason"])
                from .difficulty import KEY, available, active_multiplier
                effective = result if result.get("running") and "network" in result else c
                if available(effective):
                    print(f"Test difficulty: ×{active_multiplier(effective):,} (local regtest multiplier)")
                return 0
        elif command in ("perf","workers"):
            result = performance(args.value) if args.value else {"workers":c["workers"],"logical_cpus":os.cpu_count(),"cpu_duty":c["cpu_duty"],"options":"up / down / eco / auto / max / N / N%"}
        elif command == "difficulty":
            from .difficulty import change
            result = change(args.value)
        elif command == "network":
            from .networks import select, check_connection
            result = select(args.name)
            if args.check:
                check = check_connection(load())
                result.update(ok=check['ok'], connection_check=check, message=check['message'])
        elif command == "pruning":
            current=service.status()
            result={"enabled":c['pruning_enabled'],"budget_ms":c['pruning_budget_ms'],
                    "candidates_per_job":c['pruning_candidates'],"running":current.get('running',False),
                    "model":"Full Bitcoin SHA256d; necessary target-prefix condition",
                    "counters":current.get('pruning',{}),
                    "scope":"Unresolved candidates are retained. Counts describe actual exclusions; no toy percentage is assumed for Bitcoin."}
        elif command == "abacus":
            from .abacus_lab import precision_check, compression_check, toy_check
            if args.action == 'inspect':
                from .abacus import resident_model
                current=service.status()
                result={**resident_model().description(), 'live_priority':current.get('priority',{}),
                        'live_pruning':current.get('pruning',{})}
            elif args.action == 'study':
                from .research_system import progressive_study
                result=progressive_study(args.precision_bits)
            elif args.action == 'claims':
                from .research_system import claims, inventory
                result={**claims(),'inventory':inventory()}
            elif args.action == 'formulas':
                from .math_catalogue import catalogue
                result=catalogue(query=args.query)
            elif args.action == 'calculate':
                from .abacus import resident_model
                if not args.claim: raise ValueError('Supply --claim as a JSON arithmetic claim')
                model=resident_model()
                result=model.claim_calculator_type(pool=model.shared_pool).decide(
                    json.loads(args.claim),json.loads(args.variables))
            elif args.action == 'carries':
                from .research_system import audit_sha_carries
                result=audit_sha_carries(args.width,args.rounds,args.seed)
            elif args.action == 'theorems':
                from .theorem_calculations import calculate, catalogue
                result=calculate(args.theorem,json.loads(args.variables)) if args.theorem else catalogue()
            elif args.action == 'precision':
                result=precision_check(args.precision_bits)
            elif args.action == 'compression':
                result=compression_check()
            elif args.action == 'recurrence':
                from .recurrence import published_certificates
                result=published_certificates()
                result={**result,'ok':all(r['valid'] for r in result.values())}
            else:
                from .constraintmodel import z3
                bundled=ROOT/'.test-tools/abacus-solver/bin/python'
                if z3 is None and bundled.is_file() and str(bundled)!=sys.executable:
                    return subprocess.call([str(bundled),'-m','btcminer',*(sys.argv[1:] if argv is None else argv)],cwd=ROOT)
                result=toy_check(args.width,args.rounds,args.nonce_bits,args.difficulty,args.budget_ms,args.seed,args.scale)
        elif command == "config":
            if args.action == "show":
                result = public(c)
            elif args.action == "set":
                result = configure(args.values)
            elif args.action == "unset":
                result = configure(unset=args.values)
            elif args.action == "reset":
                result = configure(reset=True)
            elif args.action == "path":
                print(CONFIG); return 0
            else:
                if not CONFIG.exists():
                    save(c)
                subprocess.run(shlex.split(os.environ.get("EDITOR","nano"))+[str(CONFIG)],check=True)
                result = configure([])
        elif command == "logs":
            from collections import deque
            path = LOGS/("service.log" if args.service else "events.jsonl")
            if path.exists():
                with path.open(errors="replace") as f:
                    print("".join(deque(f,maxlen=max(1,min(1000,args.lines)))),end="")
            else:
                print("No log entries yet.")
            return 0
        else:
            from . import diagnostics as d
            if command == "doctor":
                result = d.doctor(c,args.connect)
            elif command == "self-test":
                result = d.self_test(c,args.require_native)
            elif command == "math":
                if not 0<=args.height<=100000000:
                    raise ValueError("height must be between 0 and 100,000,000")
                result = d.inspect_math(c,args.height,args.bits,args.strategy)
            elif command in ("benchmark","bench"):
                if service.status().get("running"):
                    raise ValueError("Stop the miner before an offline benchmark")
                if not .1<=args.seconds<=60:
                    raise ValueError("seconds must be 0.1–60")
                result = d.benchmark(c,args.seconds,args.sweep,args.strategy)
            elif command == "backtest":
                if not 1<=args.blocks<=500:
                    raise ValueError("blocks must be 1–500")
                result = d.backtest(c,args.blocks,args.strategy)
            elif command == "probe":
                result = d.probe(c,args.window,args.source,args.compare,args.z0)
            else:
                parser.print_help(); return 0
        print_result(result)
        return 0 if not isinstance(result,dict) or result.get("ok",True) else 1
    except KeyboardInterrupt:
        print("\nCancelled.",file=sys.stderr); return 130
    except (ValueError,RuntimeError,OSError,KeyError) as e:
        print(f"BTC Miner: {e}",file=sys.stderr); return 1

if __name__ == "__main__":
    raise SystemExit(main())
