"""Copper Console: responsive, read-only loop observations and miner controls.

See MASTER_PLAN.md LIVE-01; copper.py renders, ui_support.py decodes input and
reads bounded telemetry, hub.py launches the independent local Observatory.
"""
from collections import deque
import copy
import json
import os
import queue
import re
import select
import shlex
import shutil
import signal
import subprocess
import sys
import threading
import time
import unicodedata
from . import ROOT
from .platform_support import Terminal
from . import service
from .settings import load, save, validate, CONFIG, DEFAULTS, LOGS, atomic_json
from .ui_support import Keys, Observations, Painter

ESC = "\033["
RESET = ESC+"0m"
# Apple Terminal supports indexed colors. RGB SGR sequences can be interpreted
# as unrelated attributes there (e.g. 106 becomes a bright cyan background).
INK = ESC+"38;5;253m"; DIM = ESC+"38;5;246m"; FAINT = ESC+"38;5;242m"
ACCENT = ESC+"38;5;216m"; BLUE = DATA = ACCENT
GREEN = ESC+"38;5;151m"; RED = ESC+"38;5;174m"
YELLOW = ESC+"38;5;222m"; BOLD = ESC+"1m"
ANSI = re.compile(r"\x1b\[[0-9;?]*[A-Za-z]")
COMMANDS = [
    ("/hub","Open Algorithm Observatory in the local browser"),
    ("/target dif","Open the recorded BTC network difficulty HTML page"),
    ("/loop","Full-screen four-step loop with editable settings"),
    ("/dashboard","Return to the standard dashboard"),
    ("/usage","Live session and connection"), ("/config","Every BTC setting"),
    ("/setup","Connection setup wizard"), ("/logs","Recent miner events"),
    ("/start","Start this miner"), ("/stop","Stop and write Desktop summary"),
    ("/restart","Restart with saved settings"), ("/perf","CPU worker settings"),
    ("/workers","Show workers; up, down, or a count"),
    ("/network","Choose network and test its connection"),
    ("/difficulty","Regtest work multiplier: up, down, reset, or N"),
    ("/math","Inspect THESIS2 formulas and traversal"), ("/probe","SUPT diagnostic streams"),
    ("/pruning","Lossless filter settings and exclusion counters"),
    ("/abacus","Scaled Q, precision, recurrence and toy checks"),
    ("/provider","Thesis API discovery, calculation, stream and codec checks"),
    ("/backtest","Historical nonce membership"), ("/bench","Offline hashing benchmark"),
    ("/doctor","Mac and connection diagnostics"), ("/help","Commands and keys"),
    ("/quit","Close view; miner continues"),
]

def plain(s):
    return ANSI.sub("",str(s))

def safe(s):
    return "".join(c if c.isprintable() else " " for c in str(s))

def cell_width(s):
    # Combining accents occupy no cell; CJK/full-width characters occupy two.
    return sum(0 if unicodedata.combining(c) else
               2 if unicodedata.east_asian_width(c) in ("W", "F") else 1
               for c in plain(s))

def clipped(s, width):
    """Fit styled text to terminal cells without leaking styles into its neighbor."""
    if width <= 0:
        return ""
    used = cell_width(s)
    if used <= width:
        return s + RESET + " "*(width-used)
    out = []; used = 0
    for token in re.split(r"(\x1b\[[0-9;?]*[A-Za-z])",s):
        if ANSI.fullmatch(token):
            out.append(token)
            continue
        for char in token:
            cells = cell_width(char)
            if used+cells > width-1:
                return "".join(out) + "…" + RESET + " "*(width-used-1)
            out.append(char); used += cells
    return "".join(out) + RESET

def rate(value):
    value = float(value or 0)
    for unit in ("H/s","kH/s","MH/s","GH/s"):
        if value<1000 or unit=="GH/s":
            return f"{value:,.1f} {unit}"
        value /= 1000

def duration(seconds):
    seconds = int(seconds or 0)
    return f"{seconds//3600}h {(seconds//60)%60:02}m {seconds%60:02}s"

def memory():
    try:
        if sys.platform != 'darwin':
            import psutil
            sample=psutil.virtual_memory()
            return f"mem {sample.available/2**30:.1f} GB available / {sample.total/2**30:.0f} GB"
        text = subprocess.check_output(["/usr/bin/vm_stat"],text=True,timeout=2)
        page = int(re.search(r"page size of (\d+)",text).group(1))
        values = {k:int(v) for k,v in re.findall(r"([^\n:]+):\s+(\d+)\.",text)}
        available = sum(values.get(k,0) for k in ("Pages free","Pages inactive","Pages speculative","Pages purgeable"))*page
        total = int(subprocess.check_output(["/usr/sbin/sysctl","-n","hw.memsize"],text=True,timeout=2))
        return f"mem {available/2**30:.1f} GB available / {total/2**30:.0f} GB"
    except Exception:
        return ""

class App:
    def __init__(self):
        self.alive = True; self.stop_poll = threading.Event()
        self.s = {"state":"STOPPED"}; self.c = load()
        self.messages = deque(maxlen=200)
        self.seen = set(); self.spark = deque(maxlen=26)
        self.mem = ""; self.buf = None; self.palette = 0
        self.overlay = None; self.scroll = 0; self.busy = False
        self.network_choice = None
        self.pending_stop = False
        self.process = None; self.setup_fields = []; self.setup_draft = None
        self.perf_target = None; self.perf_deadline = 0
        self.recent = []
        self.sample = None; self.observed_at = 0; self.frozen = None
        self.show_events = False; self.hub_busy = False
        from .loop_view import load_labels
        self.loop_mode = False; self.loop_selected = 0; self.loop_editor = None
        self.loop_labels = load_labels(LOGS)
        self.mailbox = threading.Lock(); self.latest = None
        self.completions = queue.Queue(maxsize=8)
        self.active_args = []; self.command_started = 0
        try:
            self.recent = json.loads((LOGS/"ui.json").read_text()).get("recent",[])[:3]
        except (OSError,ValueError):
            pass
        self.note("BTC Miner ready. s starts · /setup connects · q closes this view", "notice")
        try:
            notice=json.loads((ROOT/'.updates/last-result.json').read_text())
            self.note(notice['message'],'notice')
        except (OSError,ValueError,KeyError,TypeError):
            pass
        if not CONFIG.exists():
            self.note("First run: type /setup to enter your BTC connection details.","notice")

    def note(self,text,kind="notice"):
        self.messages.append((time.strftime("%H:%M:%S"),kind,safe(text)))

    def poll(self):
        reader = Observations(LOGS)
        while not self.stop_poll.is_set():
            try:
                status = service.status()
                update = (status, load(), reader.read(status), time.time())
                with self.mailbox:
                    self.latest = update
            except Exception as e:
                with self.mailbox:
                    self.latest = ({**self.s, 'error':safe(e)}, None, None, 0)
            self.stop_poll.wait(.5)

    def poll_memory(self):
        while not self.stop_poll.is_set():
            value = memory()
            with self.mailbox:
                self.pending_memory = value
            self.stop_poll.wait(5)

    def drain_updates(self):
        with self.mailbox:
            update, self.latest = self.latest, None
            if hasattr(self, 'pending_memory'):
                self.mem = self.pending_memory
        if update:
            self.s, config, self.sample, self.observed_at = update
            if config is not None:
                self.c = config
            for event in self.s.get('events', []):
                key = (event.get('ts'), event.get('message'))
                if key not in self.seen:
                    self.seen.add(key)
                    self.messages.append((time.strftime('%H:%M:%S', time.localtime(event['ts'])),
                                          event['kind'], safe(event['message'])))
            if len(self.seen)>500:
                self.seen = {(e['ts'], e['message']) for e in self.s.get('events', [])}
            self.spark.append(self.s.get('rates', {}).get('10', 0) if self.s.get('running') else 0)
        while True:
            try:
                callback = self.completions.get_nowait()
            except queue.Empty:
                break
            callback()

    def freeze(self):
        self.frozen = None if self.frozen else dict(status=copy.deepcopy(self.s),
            sample=copy.deepcopy(self.sample), spark=list(self.spark), at=time.time(),
            messages=list(self.messages), observed_at=self.observed_at)

    def open_hub(self, args):
        if self.hub_busy:
            self.note('Hub is opening…'); return
        self.hub_busy = True; self.note('Opening local Algorithm Observatory…')
        def launch():
            try:
                from .hub import launch as open_local
                if args and (len(args)!=2 or args[0]!='--path'):
                    raise ValueError('Use /hub or /hub --path /path/to/observatory')
                result = open_local(args[1] if args else None)
                message, kind = result['message'], 'notice'
                show_url = not result['browser_opened']
            except Exception as error:
                message, kind = str(error), 'error'
                show_url = True
            def complete():
                self.hub_busy = False; self.note(message, kind)
                if show_url:
                    self.overlay = ('Hub', [message])
            self.completions.put_nowait(complete)
        threading.Thread(target=launch, daemon=True).start()

    def execute(self,args,title=None):
        if self.busy:
            if args[0] == "stop":
                self.pending_stop = True
                self.perf_target = None
                self.note("Stop queued; waiting for the current command to finish.","notice")
                if self.active_args and self.active_args[0] in ('doctor','logs','status','math','probe','backtest','benchmark','provider'):
                    if self.process is not None:
                        try:
                            self.process.terminate()
                        except OSError:
                            pass
                return
            self.note("A command is still running.","notice"); return
        self.busy = True
        self.active_args = args; self.command_started = time.monotonic()
        label = title or args[0]
        self.note(label + "…")
        if args[0] not in ("status","logs"):
            recent_command = "/target dif" if args[:2] == ["target", "dif"] else "/"+args[0]
            self.recent = [recent_command] + [r for r in self.recent if r != recent_command]
            self.recent = self.recent[:3]
        recent = list(self.recent)
        def action():
            try:
                if args[0] not in ('status','logs'):
                    try:
                        atomic_json(LOGS/'ui.json', {'recent':recent})
                    except OSError:
                        pass
                self.process = subprocess.Popen([sys.executable,"-m","btcminer",*args],cwd=ROOT,
                                                stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
                if self.pending_stop and args[0] in ('doctor','logs','status','math','probe','backtest','benchmark','provider'):
                    self.process.terminate()
                output,_ = self.process.communicate()
                code = self.process.returncode
                self.completions.put_nowait(lambda: self.complete_command(args, label, output, code))
            except Exception as e:
                self.completions.put_nowait(lambda error=str(e): self.complete_command(args, label, error, 1))
        threading.Thread(target=action,daemon=True).start()

    def complete_command(self, args, label, output, code):
        try:
            lines = [safe(line) for line in output.splitlines()]
            try:
                result = json.loads(output)
            except ValueError:
                result = None
            if code:
                message = result.get("message") if isinstance(result,dict) else None
                self.note(message or (lines[-1] if lines else "Command failed"),"error")
            else:
                if isinstance(result,dict) and result.get("message"):
                    self.note(result["message"],"accepted")
                elif args[0] in ("start","restart","stop","pause","resume"):
                    self.note(label + " complete","accepted")
                else:
                    self.note(label + " complete","accepted")
            if args[0]=="network" and isinstance(result,dict) and "connection_check" in result:
                self.c = load()
                check = result['connection_check']
                lines = ["Selected network: " + result['network'], "", check['message']]
                if check.get('rpc'):
                    lines += ["", "RPC: " + check['rpc']]
                if check.get('connected'):
                    lines += ["Node chain: " + str(check.get('chain')),
                              "Blocks / headers: " + str(check.get('blocks')) + " / " + str(check.get('headers')),
                              "Peers: " + str(check.get('peers', 'unknown'))]
                lines += ["", "Esc returns · /setup edits connection and payout settings"]
            if args[0] not in ("start","stop","restart","pause","resume") and not (args[0]=="config" and len(args)>1 and args[1]!="show") and not (args[0]=="perf" and len(args)>1):
                self.overlay = (label,lines or ["No output."])
                self.scroll = 0
        except Exception as e:
            self.note(e, 'error')
        finally:
            self.busy = False; self.process = None
            if self.pending_stop:
                self.pending_stop = False
                self.execute(["stop"])


    def network_begin(self):
        if self.busy:
            self.note("Wait for the current command before selecting a network."); return
        from .settings import CHOICES
        self.network_choice = CHOICES["network"].index(self.c["network"])
        self.perf_target = None
        self.overlay = None; self.scroll = 0; self.buf = None

    def setup_begin(self):
        if self.s.get("running"):
            self.note("Stop mining with t before changing connection setup.","notice"); return
        self.setup_draft = dict(self.c)
        self.setup_fields = [("connection","Connection: core or pool",self.c["connection"])]
        self.overlay = ("Connection setup",["Enter each value below. Enter keeps the default. Esc cancels.","Setup does not start mining."])
        self.buf = ""

    def setup_answer(self):
        key,label,default = self.setup_fields.pop(0)
        value = self.buf.strip() or default
        if key=="connection":
            if value not in ("core","pool"):
                self.note("Choose core or pool.","error"); self.setup_fields.insert(0,(key,label,default)); self.buf=""; return
            fields = [("network","Network: mainnet / testnet4 / testnet / regtest",self.c["network"])]
            if value=="core":
                fields += [("address","Your BTC payout address",self.c["address"]),
                           ("rpc_host","Bitcoin Core RPC host",self.c["rpc_host"]),
                           ("rpc_port","RPC port; 0 means network default",str(self.c["rpc_port"])),
                           ("rpc_datadir","Core data folder; blank uses macOS default",self.c["rpc_datadir"]),
                           ("rpc_cookie","Explicit cookie path; blank means automatic",self.c["rpc_cookie"])]
                fields += [("rpc_tls","HTTPS for Core RPC: on/off (required for remote hosts)","on" if self.c["rpc_tls"] else "off"),
                           ("rpc_user","RPC username; password comes from BTC_RPC_PASSWORD",self.c["rpc_user"])]
            else:
                fields += [("pool","BTC pool endpoint: stratum+ssl://host:port or stratum+tcp://host:port",self.c["pool"]),
                           ("pool_user","Pool username / address.worker",self.c["pool_user"]),
                           ("pool_password","Pool password",self.c["pool_password"]),
                           ("backup","Backup endpoint; blank means none",self.c["backup"])]
            self.setup_fields = fields
        if key=="rpc_port":
            try:
                value = int(value)
            except ValueError:
                self.note("Enter a port number.","error"); self.setup_fields.insert(0,(key,label,default)); self.buf=""; return
        if key == 'rpc_tls':
            if value.lower() not in ('on', 'off'):
                self.note('Choose on or off.', 'error'); self.setup_fields.insert(0,(key,label,default)); self.buf=''; return
            value = value.lower() == 'on'
        try:
            validate(dict(self.setup_draft, **{key:value}))
            if key == "address":
                from .protocol import script_for_address
                script_for_address(value,self.setup_draft["network"])
            elif key == "pool" or (key == "backup" and value):
                from .connections import endpoint
                endpoint(value,self.c["tls"])
        except ValueError as e:
            self.note(e,"error")
            self.setup_fields.insert(0,(key,label,default)); self.buf=""; return
        self.setup_draft[key] = value
        self.buf = ""
        if not self.setup_fields:
            try:
                service.validate_start(self.setup_draft)
                save(self.setup_draft)
                self.c = load(); self.note("Connection saved. s starts mining.","accepted")
            except ValueError as e:
                self.note(e,"error")
            self.setup_draft = None; self.buf=None; self.overlay=None

    def command(self,line):
        try:
            parts = shlex.split(line.lstrip("/"))
        except ValueError as e:
            self.note(e,"error"); return
        if not parts:
            return
        name,*args = parts
        if name.lower() == 'hub':
            self.open_hub(args); return
        if name.lower() in ('loop', 'dashboard'):
            self.loop_mode = name.lower() == 'loop'
            self.loop_editor = None; self.overlay = None; self.show_events = False; return
        if name in ("quit","q"):
            self.alive=False; return
        if name=="setup":
            self.setup_begin(); return
        if name=="network" and not args:
            self.network_begin(); return
        if name=="help":
            self.overlay = ("Commands",[
                "s start · t stop + Desktop summary · q / Ctrl+C close view",
                "+ / − workers (changes gather for 1.5 seconds) · p manual pause",
                "q leaves a running miner running. Nothing starts at login.","",
                "/hub                        Open the local Algorithm Observatory",
                "/lab                        Open the live scale and difficulty lab",
                "/target dif                 Open the recorded network difficulty HTML page",
                "/hub --path PATH            Use another Observatory folder",
                "/files                      Open the HTML project and audit browser",
                "/loop                       Full-screen editable four-step loop",
                "/dashboard                  Return to the standard dashboard",
                "Loop: 1–4 select · Enter/e edit · Ctrl+S save · Esc back",
                "f freezes/resumes display only · e switches loop/events in compact view",
                "/setup                      Guided Core or pool configuration",
                "/usage                      Current session",
                "/config                     Every effective setting",
                "/set KEY=value              Save setting; restart if running",
                "/unset KEY                  Restore a setting's default",
                "/perf eco|auto|max|N|N%      Worker count (eco 1, auto 2)",
                "/workers [up|down|N]        Show or change CPU worker count",
                "/difficulty [up|down|reset|N] Regtest multiplier; restarts if running",
                "/network                    Select network from menu; test connection",
                "/network mainnet|testnet4    Switch network; mining stays stopped",
                "                            testnet = legacy testnet3; regtest also supported",
                "/pause on|off|120            Pause while keyboard/mouse active",
                "/resume                     Clear manual pause",
                "/strategy thesis2|thesis|linear|hybrid",
                "/set thesis2_step=7 thesis2_prime=19",
                "/connection core|pool       Select a configured connection",
                "/set single_nonce_only=on   First THESIS2 nonce / legacy minimal set",
                "/set entropy_min=0.18 entropy_max=0.45",
                "/set partition=quadrant     Legacy modes: quadrant / chunk / ordered",
                "/set cpu_duty=50            Worker duty cycle",
                "/set round_restart_seconds=600",
                "/math --height 900000 --bits 17034219",
                "/math --strategy thesis     Inspect retained legacy formulas",
                "/pruning                    Full-SHA filter settings and counters",
                "/abacus                     Resident math and scoped experiments",
                "/provider refresh           Refresh current API and formula discovery",
                "/provider watch --seconds 10 Observe provider model events",
                "/provider check             Check calculator values and codec interoperability",
                "/provider hash --header-hex HEX  Compare remote and local header hashes",
                "  --hash-mode remote        Compute the supplied header remotely only",
                "/set pruning_enabled=on     Enable lossless candidate filtering",
                "/probe --window 512         SUPT report",
                "/probe --compare            Saved strategy comparison",
                "/probe --z0                 Z0 diagnostic",
                "/backtest --blocks 100      Requires Bitcoin Core",
                "/bench --sweep              Offline; stop miner first",
                "/bench --strategy thesis2   Scheduler + diagnostics benchmark",
                "/doctor --connect           Check Core and candidate block",
                "/logs                       Events; /err for service output",
                "/restart                    Restart without Desktop summary",
                "","Cards: ↑/↓ scroll · PageUp/PageDown · Esc return",
                "Reviewed math updates can restart an active miner."])
            self.scroll=0; return
        mapped = {"usage":"status","stats":"status","threads":"perf","workers":"perf","settings":"config","events":"logs","err":"logs","math":"math","bench":"benchmark"}.get(name,name)
        if name=="err":
            args = ["--service"]+args
        elif name=="set":
            mapped="config"; args=["set"]+args
        elif name=="unset":
            mapped="config"; args=["unset"]+args
        elif name in ("strategy","connection"):
            if len(args)!=1:
                self.note(f"/{name} needs one value.","error"); return
            mapped="config"; args=["set",f"{name}={args[0]}"]
        elif name=="pause" and args:
            raw = {"on":"120","off":"0"}.get(args[0],args[0])
            mapped="config"; args=["set",f"pause_on_active={raw}"]
        if mapped=="status" and not args:
            args=["--json"]
        if mapped=="network" and args:
            self.perf_target = None
        self.execute([mapped,*args],"/"+name)

    def adjust(self,delta):
        base = self.perf_target if self.perf_target is not None else self.c["workers"]
        self.perf_target=max(1,min(os.cpu_count() or 8,base+delta))
        self.perf_deadline=time.monotonic()+1.5

    def input(self,key):
        if key=="\x03":
            self.alive=False; return
        if self.loop_mode:
            from .loop_view import handle
            if handle(self, key):
                return
        if self.network_choice is not None:
            from .settings import CHOICES
            options = CHOICES["network"]
            if key in ("\x1b", "q"):
                self.network_choice = None
            elif key in ("\x1b[A", "\x1b[B"):
                self.network_choice = (self.network_choice + (-1 if key.endswith("A") else 1)) % len(options)
            elif key in ("1", "2", "3", "4"):
                self.network_choice = int(key)-1
            elif key in ("\r", "\n"):
                name = options[self.network_choice]
                self.network_choice = None
                self.execute(["network", name, "--check"], "Select and test " + name)
            elif key=="t":
                self.network_choice = None
                self.execute(["stop"])
            return
        if self.setup_draft is not None:
            if key=="\x1b":
                self.setup_draft=None; self.setup_fields=[]; self.buf=None; self.overlay=None
            elif key in ("\r","\n"):
                self.setup_answer()
            elif key in ("\x7f","\b"):
                self.buf=self.buf[:-1]
            elif len(key)==1 and key.isprintable():
                self.buf+=key
            return
        if self.buf is not None:
            if key=="\x1b":
                self.buf=None
            elif key in ("\x7f","\b"):
                self.buf=self.buf[:-1]
                if not self.buf:
                    self.buf=None
            elif key in ("\x1b[A","\x1b[B"):
                self.palette += -1 if key.endswith("A") else 1
            elif key in ("\r","\n","\t"):
                options=[x for x in COMMANDS if x[0].startswith(self.buf)]
                line=self.buf
                if options and (self.buf=="/" or key=="\t"):
                    line=options[self.palette%len(options)][0]
                self.buf=None; self.command(line)
            elif len(key)==1 and key.isprintable():
                self.buf+=key; self.palette=0
            return
        if key in ("/", "l"):
            self.buf=key; self.palette=0
        elif key=="q":
            self.alive=False
        elif key=="f":
            self.freeze()
        elif key=="e":
            self.show_events = not self.show_events
        elif key=="s":
            if not self.busy and not self.s.get("running"):
                try:
                    service.validate_start(self.c)
                except ValueError as e:
                    self.note(f"Setup needed: {e}","notice")
                    self.setup_begin()
                    return
            self.execute(["start"])
        elif key=="t":
            self.perf_target = None
            self.execute(["stop"])
        elif key=="p":
            self.execute(["resume" if self.s.get("paused_reason")=="manual" else "pause"])
        elif key in ("+","="):
            self.adjust(1)
        elif key in ("-","_"):
            self.adjust(-1)
        elif key=="\x1b":
            self.overlay=None; self.scroll=0
        elif key in ("\x1b[A","\x1b[B","\x1b[5~","\x1b[6~") and self.overlay:
            amount = {"\x1b[A":-1,"\x1b[B":1,"\x1b[5~":-10,"\x1b[6~":10}[key]
            self.scroll=max(0,min(len(self.overlay[1])-1,self.scroll+amount))
        elif key=="?":
            self.command("help")

    def rail(self, height=None):
        s=self.s; c=self.c
        running=s.get("running",False); rates=s.get("rates",{}) if running else {}
        samples=list(self.spark) if running else []
        peak=max(samples,default=0) or 1
        graph="".join("▁▂▃▄▅▆▇█"[max(0,min(7,int(v/peak*7)))] for v in samples)
        thesis2 = c["strategy"] == "thesis2"
        strategy_line = "THESIS2 · 19² − 1 = 360" if thesis2 else c["strategy"]+" · "+c["partition"]
        count_line = "32-bit nonce traversal" if thesis2 else f"{s.get('candidate_count',0):,} candidates"
        controls_line = f"{s.get('math_details',{}).get('order',c.get('thesis2_order','field'))} · step {c['thesis2_step']} · prime {c['thesis2_prime']}" if thesis2 else f"entropy {c['entropy_min']}–{c['entropy_max']}"
        folder=str(ROOT)
        home=os.path.expanduser("~")
        if folder.startswith(home+os.sep):
            folder="~"+folder[len(home):]
        # Larger priorities yield first in shorter windows, preserving order.
        items=[
            (1,BOLD+ACCENT+"SESSION"),
            (0,DIM+"10s rate    "+BOLD+DATA+rate(rates.get("10",0))),
            (6,DATA+(graph or "─"*26)),
            (3,DIM+"60s         "+INK+rate(rates.get("60",0))),
            (3,DIM+"15m         "+INK+rate(rates.get("900",0))),
            (7,""),
            (1,BOLD+ACCENT+("RESULTS" if running else "RESULTS · LAST SESSION")),
            (0,GREEN+f"{s.get('shares_accepted',0):,} accepted shares"),
            (0,DIM+f"{s.get('shares_rejected',0):,} rejected solutions"),
            (0,DIM+f"{s.get('shares_unknown',0):,} unknown outcomes"),
            (0,INK+f"{s.get('blocks_accepted',0):,} accepted Core blocks"),
            (7,""),
            (1,BOLD+ACCENT+"ENGINE / STRATEGY"),
            (4,INK+safe(s.get("hasher","ARM SHA-256"))),
            (1,DIM+f"{c['workers']} workers · duty {c['cpu_duty']}%"),
            (5,DIM+f"{s.get('hashes',0):,} hashes"),
            (1,INK+safe(strategy_line)),
            (4,DIM+count_line),
            (3,DIM+controls_line),
            (7,""),
            (1,BOLD+ACCENT+"CONNECTION"),
            (1,INK+safe(s.get("endpoint") or (c["pool"] if c["connection"]=="pool" else c["rpc_host"]))),
            (2,DIM+f"height {s.get('height') or '—'}"),
            (2,DIM+("elapsed " if running else "last session ")+duration(s.get("elapsed",0))),
            (5,DIM+safe(self.mem)),
            (5,FAINT+safe(folder)),
        ]
        if height is not None and len(items)>height:
            remove=set(sorted(range(len(items)),key=lambda i:(items[i][0],i),reverse=True)[:len(items)-max(0,height)])
            items=[item for i,item in enumerate(items) if i not in remove]
        return [line for _,line in items]

    def panel(self, height):
        """Render the existing active panel; command dispatch stays in App.input."""
        if height <= 0:
            return []
        if self.network_choice is not None:
            from .settings import CHOICES
            labels = ("Mainnet · real Bitcoin", "Testnet4 · test Bitcoin",
                      "Testnet3 · legacy test network", "Regtest · local testing")
            lines = [BOLD+ACCENT+"Select Bitcoin network", DIM+"↑↓ or 1–4 choose · Enter select + test · Esc cancel", ""]
            for i, (name, label) in enumerate(zip(CHOICES["network"], labels)):
                lines.append((BOLD+ACCENT+"› " if i==self.network_choice else DIM+"  ") +
                             str(i+1)+"  "+label+("  [current]" if name==self.c["network"] else ""))
            lines += ["", DIM+"Switching stops mining. Selection tests the connection; it does not start mining."]
        elif self.setup_draft is not None:
            key,label,default=self.setup_fields[0]
            lines=[BOLD+ACCENT+"Connection setup",INK+safe(label),
                   DIM+"Default: "+("••••" if key=="pool_password" else safe(default or "(blank)")),
                   "",DIM+"Enter accepts · Esc cancels · mining remains stopped"]
        elif self.buf is not None and " " not in self.buf:
            options=[x for x in COMMANDS if x[0].startswith(self.buf)]
            lines=[BOLD+ACCENT+"Commands"+RESET+DIM+" · ↑↓ choose · Enter run · Esc close"]
            room=max(0,height-len(lines))
            if options and room:
                selected=self.palette%len(options); start=max(0,selected-room+1)
                for i,(command,desc) in enumerate(options[start:start+room],start):
                    lines.append((BOLD+ACCENT+"› " if i==selected else DIM+"  ")+command.ljust(13)+RESET+DIM+desc)
        elif self.overlay:
            title,body=self.overlay
            lines=[BOLD+ACCENT+safe(title)+RESET+DIM+" · ↑↓ scroll · Esc return"]
            lines += [INK+safe(line) for line in body[self.scroll:self.scroll+max(0,height-1)]]
        else:
            lines=[BOLD+ACCENT+"ACTIVITY"+RESET+DIM+"  latest session events"]
            if height >= 12:
                lines.append("")
            room=max(0,height-len(lines))
            for stamp,kind,text in list(self.messages)[-room:] if room else []:
                color={"accepted":GREEN,"rejected":RED,"error":RED,"connection":YELLOW,
                       "unknown":YELLOW,"start":ACCENT}.get(kind,DIM)
                label=clipped(safe(kind).upper(),10)
                lines.append(DIM+safe(stamp)+"  "+color+label+" "+INK+safe(text))
        return lines[:height]+[""]*max(0,height-len(lines))

    def frame(self,cols,rows):
        self.drain_updates()
        if self.loop_mode:
            from .loop_view import frame
            return frame(self, cols, rows)
        if cols >= 60 and rows >= 18:
            from .copper import frame
            return frame(self, cols, rows)
        return self.small_frame(cols, rows)

    def small_frame(self,cols,rows):
        cols=max(1,cols); rows=max(1,rows); width=max(0,cols-1)
        wide=cols>=100 and rows>=24
        s=self.s; c=self.c
        state=safe(s.get("state","STOPPED")); running=s.get("running",False)
        color=GREEN if state=="MINING" else YELLOW if state in ("PAUSED","CONNECTING","STARTING") else DIM
        title=BOLD+ACCENT+">_ BTC MINER"+RESET+DIM+"   /   LOCAL EDITION"
        if width>=50:
            title=clipped(title,width-cell_width(state)-2)+"  "+BOLD+color+state
        detail=ACCENT+safe(c["network"])+RESET+INK+("  Bitcoin Core" if c["connection"]=="core" else "  Stratum V1 pool")
        detail+=DIM+f" · {c['strategy']} · {c['workers']} workers · "+safe(c["worker"])
        status=color+"● "+state+RESET+DIM+(" · "+duration(s.get("elapsed",0))+" · t to stop" if running else " · s to start")
        reasons=[]
        if self.pending_stop:
            reasons.append(YELLOW+"Stop queued — finishing the current command")
        if s.get("paused_reason"):
            reasons.append(YELLOW+safe(s["paused_reason"]))
        if self.setup_draft is not None:
            secret=self.setup_fields[0][0]=="pool_password"
            prompt=ACCENT+"› "+INK+("•"*len(self.buf or "") if secret else safe(self.buf or ""))
        else:
            prompt=ACCENT+"› "+(INK+safe(self.buf) if self.buf is not None else DIM+("Working…" if self.busy else "Type / for commands"))
        footer=DIM+f"s start  t stop  p pause  + − CPU  /network {c['network']}  q close view"
        if cols<80:
            footer=DIM+"s start  t stop  p pause  + − CPU  / commands  q close"
        if self.perf_target is not None:
            footer=YELLOW+f"workers {c['workers']} → {self.perf_target} · applying in {max(0,self.perf_deadline-time.monotonic()):.1f}s"
        if rows<8:
            lines=[status,detail,reasons[0] if reasons else "",prompt,footer]
            # Keep the prompt even in a one-row terminal; do not wrap/scroll.
            lines=([prompt] if rows==1 else [status,prompt,footer][:rows]) if rows<5 else lines
            lines += [""]*max(0,rows-len(lines))
            return RESET+ESC+"H"+"\r\n".join(clipped(line,width)+RESET for line in lines)
        bottom=4 if rows>=18 else 3
        header=[title]
        if rows>=30:
            header.append("")
        header += [detail,status]
        if c["network"]=="regtest" and c["connection"]=="core":
            multiplier=s.get("regtest_difficulty_multiplier",c.get("regtest_difficulty_multiplier",1)) if running else c.get("regtest_difficulty_multiplier",1)
            header.append(ACCENT+f"Test difficulty ×{multiplier:,}"+DIM+" · /difficulty up | down | reset")
        header += reasons
        if not wide and rows>=18:
            rates=s.get("rates",{}) if running else {}
            results_context=DIM+"Last session: " if not running else ""
            header += [DATA+"10s "+rate(rates.get("10",0))+DIM+"  ·  60s "+rate(rates.get("60",0))+"  ·  15m "+rate(rates.get("900",0)),
                       results_context+GREEN+f"{s.get('shares_accepted',0)} accepted shares"+DIM+f" · {s.get('shares_rejected',0)} rejected solutions",
                       DIM+f"{s.get('shares_unknown',0)} unknown outcomes · {s.get('blocks_accepted',0)} accepted Core blocks"]
        header.append(FAINT+"─"*width)
        if rows>=30:
            header.append("")
        header=header[:max(2,rows-bottom-2)]
        height=rows-bottom-len(header)
        lines=self.panel(height)
        display=[clipped(line,width)+RESET for line in header]
        if wide:
            rail_width=36; left=width-rail_width-3
            rail=self.rail(height)
            for i,line in enumerate(lines):
                display.append(clipped(line,left)+FAINT+" │ "+clipped(rail[i] if i<len(rail) else "",rail_width)+RESET)
        else:
            display += [clipped(line,width)+RESET for line in lines]
        display += [FAINT+"─"*width+RESET,clipped(prompt,width)+RESET,clipped(footer,width)+RESET]
        if bottom==4:
            note="q / Ctrl+C closes this view; a running miner continues."
            if not wide and self.mem and cols>=80:
                note += "  "+safe(self.mem)
            display.append(clipped(FAINT+note,width)+RESET)
        return RESET+ESC+"H"+"\r\n".join(display)

    def paste(self, text):
        # Paste is data only, never an action or a command submission.
        text = ''.join(c for c in text if c.isprintable())
        if self.loop_editor is not None:
            if self.loop_editor['text'] is not None:
                self.loop_editor['text'] = (self.loop_editor['text']+text)[:256]
        elif self.buf is not None:
            self.buf += text

    def loop(self):
        terminal = Terminal()
        previous_handlers={}
        def halt(*_):
            self.alive=False
        for sig in (signal.SIGTERM, signal.SIGINT) + ((signal.SIGHUP,) if hasattr(signal, 'SIGHUP') else ()):
            previous_handlers[sig]=signal.signal(sig,halt)
        thread=threading.Thread(target=self.poll,daemon=True); thread.start()
        threading.Thread(target=self.poll_memory,daemon=True).start()
        keys = Keys(); painter = Painter(); next_render = 0
        try:
            terminal.enter()
            sys.stdout.write(ESC+"?1049h"+RESET+ESC+"2J"+ESC+"H"+ESC+"?25l"+ESC+"?7l"+ESC+"?2004h"+"\033]11;#201e1b\007"); sys.stdout.flush()
            while self.alive:
                if self.perf_target is not None and time.monotonic()>=self.perf_deadline and not self.busy:
                    target=self.perf_target; self.perf_target=None
                    self.execute(["perf",str(target)],"Adjust workers")
                if time.monotonic() >= next_render:
                    cols,rows=shutil.get_terminal_size((110,36))
                    output = painter.render(self.frame(cols,rows), (cols,rows))
                    if output:
                        sys.stdout.write(output); sys.stdout.flush()
                    next_render = time.monotonic()+.1
                raw = terminal.read()
                if raw == b'': break
                for key in keys.feed(raw or b''):
                    next_render = 0
                    if isinstance(key, tuple):
                        self.paste(key[1])
                    else:
                        self.input(key)
        finally:
            self.stop_poll.set()
            terminal.restore()
            sys.stdout.write(RESET+ESC+"?2004l"+ESC+"?7h"+ESC+"?25h"+"\033]111\007"+ESC+"?1049l"); sys.stdout.flush()
            for sig,handler in previous_handlers.items():
                signal.signal(sig,handler)
            print("BTC Miner view closed. A running miner continues; use ./bin/btc-miner stop to stop it.")

def run():
    if not sys.stdin.isatty() or not sys.stdout.isatty():
        print("Open Start BTC Miner.command in Terminal, or use ./bin/btc-miner --help.")
        return 1
    App().loop()
    return 0
