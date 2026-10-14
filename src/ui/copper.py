"""Copper Console character-grid presentation; no I/O or miner control.

The loop shows observed completed work, not fabricated native-stage timing.
See MASTER_PLAN.md LIVE-01 and ui_support.Observations for sample scope.
"""
import time
from .tui import ACCENT, BOLD, DIM, FAINT, GREEN, INK, RED, RESET, YELLOW, ESC
from .tui import clipped, cell_width, duration, rate, safe


def fit(items, height):
    """Keep important lines in their original order as vertical space shrinks."""
    retained = sorted(sorted(range(len(items)), key=lambda i: (items[i][0], i))[:max(0,height)])
    return [items[i][1] for i in retained]


def box(width, height, title, lines):
    if height < 2 or width < 4:
        return [clipped(line, width) for line in lines[:height]] + [' '*width]*max(0,height-len(lines))
    label = ' '+title+' '
    cap = FAINT+'┌─'+ACCENT+clipped(label, min(width-4, cell_width(label)))
    cap += FAINT+'─'*max(0,width-4-cell_width(label))+'─┐'
    if not title:
        cap = FAINT+'┌'+'─'*(width-2)+'┐'
    body = [FAINT+'│'+RESET+clipped(' '+line,width-2)+FAINT+'│' for line in lines[:height-2]]
    body += [FAINT+'│'+' '*(width-2)+'│']*max(0,height-2-len(body))
    return [cap]+body+[FAINT+'└'+'─'*(width-2)+'┘']


def events(app, height):
    messages = app.frozen['messages'] if app.frozen else list(app.messages)
    result = []
    for stamp, kind, text in messages[-max(0,height):] if height else []:
        color = {'error':RED,'rejected':RED,'accepted':GREEN,'unknown':YELLOW,'connection':YELLOW}.get(kind,ACCENT)
        result.append(DIM+safe(stamp)+'  '+color+safe(kind).upper().ljust(10)+' '+INK+safe(text))
    return result


def loop_lines(app, status, sample, height, narrow):
    running = status.get('running',False)
    state = status.get('state','STOPPED')
    observation = app.frozen['observed_at'] if app.frozen else app.observed_at
    now = app.frozen['at'] if app.frozen else time.time()
    age = max(0,now-observation) if observation else None
    fresh = age is not None and age <= 3
    sample_age = max(0,now-sample['timestamp']) if sample else None
    recent = bool(sample and sample_age<=5 and fresh and running and state=='MINING')
    current_height = status.get('height')
    same_height = bool(sample and sample.get('height') == current_height)
    scope = ('FROZEN · f resumes display' if app.frozen else
             'Last session · s starts mining' if not running else
             'Waiting for a status observation' if age is None else
             f"{'STALE' if not fresh else 'Live observations'} · updated {age:.1f}s ago")
    job = sample['job'][:12] if sample and same_height else 'awaiting sample'
    work = f'height {current_height or "—"} · job {job}'
    batch = f"{sample['attempted']:,} attempts · completed batch" if sample else 'awaiting completed batch'
    hashing = ('Stopped' if not running else 'Status stale' if not fresh else
               'Paused · '+safe(status.get('paused_reason','')) if state=='PAUSED' else
               'Waiting for work' if state!='MINING' else
               f"{status.get('workers',app.c['workers'])} workers configured · {rate(status.get('rates',{}).get('10',0))}")
    result = f"{status.get('blocks_accepted',0)} blocks · {status.get('shares_accepted',0)} shares accepted"
    nonce = f"{sample['nonce']:,}" if sample else 'awaiting sample'
    digest = sample['hash'][:16]+'…'+sample['hash'][-12:] if sample else '—'
    samples = app.frozen['spark'] if app.frozen else list(app.spark)
    peak = max(samples,default=0) or 1
    graph = ''.join('▁▂▃▄▅▆▇█'[max(0,min(7,int(v/peak*7)))] for v in samples) if running else ''
    strategy = app.c['strategy']
    math = (f"THESIS2 {status.get('math_details',{}).get('order',app.c.get('thesis2_order','field'))} · step {app.c['thesis2_step']} · prime {app.c['thesis2_prime']} · 32-bit nonce traversal"
            if strategy=='thesis2' else f"{strategy} · {app.c['partition']} · {status.get('candidate_count',0):,} candidates")
    sample_scope = ('No sample for this session' if not sample else
                    f"Sample age {sample_age:.1f}s"+(' · previous height' if not same_height else ''))
    items = [(0, (YELLOW if app.frozen or (running and not fresh) else DIM)+scope),
             (9,''),
             (1,ACCENT+'01  GET WORK       '+INK+work),
             (1,ACCENT+'02  BUILD BATCH    '+INK+batch),
             (1,ACCENT+'03  HASH           '+(GREEN if recent else INK)+hashing),
             (2,ACCENT+'04  CHECK / SUBMIT '+INK+result),
             (9,''),
             (4,DIM+'10s rate history   '+ACCENT+(graph or '—')),
             (1,DIM+'Sampled nonce      '+INK+nonce),
             (1,DIM+'Sampled hash       '+INK+digest),
             (3,FAINT+sample_scope),
             (3,FAINT+'Sampled replay of completed work · not every hash'),
             (9,''),
             (6,ACCENT+'ENGINE / STRATEGY'),
             (5,INK+math),
             (6,DIM+safe(status.get('hasher','Hasher not yet observed'))),
             (7,DIM+safe(app.mem))]
    if strategy!='thesis2':
        items.append((7,DIM+f"entropy {app.c['entropy_min']}–{app.c['entropy_max']}"))
    telemetry = status.get('model_telemetry',{})
    provider = status.get('provider', {})
    resources=status.get('resources',{})
    if resources.get('enabled'):
        sample=resources.get('sample') or {}
        cpu=sample.get('host_cpu_percent');rss=sample.get('owned_rss_mib')
        cpu_text='unavailable' if cpu is None else f'{cpu:.1f}%'
        ram_text='unavailable' if rss is None else f'{rss:.0f}/{resources.get("rss_limit_mib",0):.0f} MiB'
        items.insert(1,(1,ACCENT+f'Mac CPU {cpu_text} · target {resources.get("cpu_target")}% · backoff {resources.get("cpu_backoff")}%'))
        items.insert(2,(1,DIM+f'Workers {resources.get("active_workers",0)}/{resources.get("maximum_workers",0)} · RAM {ram_text}'))
        items.insert(3,(2,DIM+safe(resources.get('last_reason',''))))
    if app.c.get('provider_enabled') or provider.get('enabled'):
        if not running:
            provider_line = 'API enabled · connects when you start mining'
        else:
            provider_line = ('API '+safe(provider.get('state', 'connecting'))+
                             ' · stream '+safe(provider.get('stream', 'connecting'))+
                             ' · job math '+safe(provider.get('math_check', 'pending')))
        items.insert(1, (1, ACCENT+provider_line))
        if running:
            items.append((4, DIM+f"API formulas {provider.get('formula_count', 0)} · checks {provider.get('checks_passed', 0)} · TCMP events {provider.get('binary_events', 0)}"))
            measurements=provider.get('telemetry',{})
            calc=measurements.get('calculations',{}).get('websocket') or measurements.get('calculations',{}).get('rest')
            if calc:
                value=calc.get('cpu_ms');label='unavailable' if value is None else f'{value:g} ms'
                items.append((3,DIM+'API calculation cost '+label+' · '+safe(calc.get('availability','unknown'))))
            server=measurements.get('server',{})
            label=server.get('availability','unavailable')
            if label=='current':
                value=server.get('cpu_percent');label+=' · CPU '+('unavailable' if value is None else f'{value:.1f}%')
            items.append((3,DIM+'Server resources '+safe(label)))
    if telemetry.get('enabled') is False:
        items.insert(1,(0,YELLOW+'Sampling disabled · counters still available'))
    elif telemetry.get('dropped') or telemetry.get('errors'):
        items.insert(1,(0,YELLOW+f"Telemetry: {telemetry.get('dropped',0)} dropped · {telemetry.get('errors',0)} errors"))
    if narrow and height<10:
        items = [(priority,line.replace('       ',' ').replace('      ',' ')) for priority,line in items]
    return fit(items,height)


def rail(app,status,height):
    running = status.get('running',False)
    rates = status.get('rates',{}) if running else {}
    items = [(0,INK+('Core' if app.c['connection']=='core' else 'Pool')+'  '+
              (GREEN+'connected' if status.get('connected') else DIM+'disconnected')),
             (0,DIM+f"Workers   {status.get('workers',app.c['workers'])} · {app.c['cpu_duty']}% duty"),
             (2,DIM+f"Rounds    {status.get('rounds',0):,} completed"),
             (1,GREEN+f"{status.get('shares_accepted',0):,} accepted shares"),
             (1,DIM+f"{status.get('shares_rejected',0):,} rejected solutions"),
             (1,DIM+f"{status.get('shares_unknown',0):,} unknown outcomes"),
             (1,INK+f"{status.get('blocks_accepted',0):,} accepted Core blocks"),
             (4,DIM+f"60s {rate(rates.get('60',0))} · 15m {rate(rates.get('900',0))}"),
             (3,DIM+('elapsed ' if running else 'last session ')+duration(status.get('elapsed',0))),
             (7,FAINT+safe(status.get('endpoint',''))),
             (8,''),(0,BOLD+ACCENT+'HUB'),(0,ACCENT+'/hub'),
             (2,INK+'Open Algorithm Observatory'),(2,DIM+'Local browser · 127.0.0.1'),
             (8,''),(6,DIM+safe(app.c['worker']))]
    return fit(items,height)


def frame(app,cols,rows):
    width = max(0,cols-1)
    status = app.frozen['status'] if app.frozen else app.s
    sample = app.frozen['sample'] if app.frozen else app.sample
    running = status.get('running',False)
    # Lifecycle state and pause/stop notices always stay live even when inspecting.
    state = safe(app.s.get('state','STOPPED'))
    color = GREEN if state=='MINING' else YELLOW if state in ('PAUSED','CONNECTING','STARTING') else DIM
    badge = color+'● '+state
    header = [clipped(BOLD+ACCENT+'>_ BTC MINER'+DIM+' / COPPER',width-cell_width(badge)-1)+' '+badge,
              ACCENT+safe(app.c['network'])+DIM+' / '+INK+('Bitcoin Core' if app.c['connection']=='core' else 'Stratum V1 pool')+
              DIM+f" · {app.c['strategy']} · {app.c['workers']} workers · "+('t to stop' if app.s.get('running') else 's to start')]
    if app.pending_stop:
        header.append(YELLOW+'Stop queued — finishing the current command')
    if app.s.get('paused_reason'):
        header.append(YELLOW+safe(app.s['paused_reason']))
    if app.s.get('error'):
        header.append(RED+safe(app.s['error']))
    if app.c['network']=='regtest' and app.c['connection']=='core':
        multiplier = status.get('regtest_difficulty_multiplier', app.c['regtest_difficulty_multiplier']) if running else app.c['regtest_difficulty_multiplier']
        header.append(ACCENT+f'Test difficulty ×{multiplier:,}'+DIM+' · /difficulty up | down | reset')
    if app.frozen:
        header.append(YELLOW+'DISPLAY FROZEN · f resumes · mining controls remain live')
    header = header[:6]
    rates = status.get('rates',{}) if running else {}
    wide = cols>=100 and rows>=24
    display = list(header)
    if wide:
        widths=[(width-2)//3]*2
        widths.append(width-2-sum(widths))
        cells=[box(widths[0],4,'10s HASHRATE',[BOLD+INK+rate(rates.get('10',0)),DIM+f"60s {rate(rates.get('60',0))} · 15m {rate(rates.get('900',0))}"]),
               box(widths[1],4,'SESSION HASHES' if running else 'LAST SESSION HASHES',[BOLD+INK+f"{status.get('hashes',0):,}",DIM+duration(status.get('elapsed',0))]),
               box(widths[2],4,'ACCEPTED BLOCKS',[BOLD+INK+str(status.get('blocks_accepted',0)),DIM+'Core acceptance confirmed' if status.get('blocks_accepted',0) else DIM+'No accepted blocks'])]
        display += [' '.join(cell[i] for cell in cells) for i in range(4)]
    else:
        display += [ACCENT+'10s '+INK+rate(rates.get('10',0))+DIM+' · 60s '+rate(rates.get('60',0))+' · 15m '+rate(rates.get('900',0)),
                    (DIM+'Last session: ' if not running else '')+GREEN+f"{status.get('shares_accepted',0)} accepted shares"+DIM+f" · {status.get('shares_rejected',0)} rejected solutions",
                    DIM+f"{status.get('shares_unknown',0)} unknown outcomes · {status.get('blocks_accepted',0)} accepted Core blocks"]
    overlay = app.network_choice is not None or app.setup_draft is not None or app.buf is not None or app.overlay is not None
    footer_height = 5 if wide else 4
    activity_height = 5 if wide and rows>=32 else 0
    gap = 1 if rows>=30 else 0
    display += ['']*gap
    main_height = rows-len(display)-footer_height-activity_height-gap
    if wide:
        right = min(39,max(32,width//3)); left = width-right-1
        body = app.panel(max(0,main_height-2)) if overlay else loop_lines(app,status,sample,main_height-2,False)
        a = box(left,main_height,'COMMANDS / REPORT' if overlay else 'MINING LOOP',body)
        b = box(right,main_height,'SESSION' if running else 'RESULTS · LAST SESSION',rail(app,status,main_height-2))
        display += [x+' '+y for x,y in zip(a,b)]
    else:
        body = (app.panel(max(0,main_height-2)) if overlay else events(app,main_height-2)
                if app.show_events else loop_lines(app,status,sample,main_height-2,True))
        title = 'COMMANDS / REPORT' if overlay else 'ACTIVITY · e loop' if app.show_events else 'MINING LOOP · e events'
        display += box(width,main_height,title,body)
    if activity_height:
        display += ['']*gap+box(width,activity_height,'ACTIVITY',events(app,activity_height-2))
    else:
        display += ['']*gap
    secret = app.setup_draft is not None and app.setup_fields[0][0]=='pool_password'
    prompt = (('•'*len(app.buf or '') if secret else safe(app.buf or '')) if app.buf is not None else
              f"Working: {safe(app.active_args[0] if app.active_args else 'command')} · {time.monotonic()-app.command_started:.0f}s" if app.busy else 'Type / for commands')
    if wide:
        display += box(width,3,'', [ACCENT+'› '+INK+prompt])
    else:
        display += [FAINT+'─'*width,ACCENT+'› '+INK+prompt]
    shortcuts = ('s start  t stop  p pause miner  f freeze view  + − CPU  /hub browser  q close' if cols>=100 else
                 's start  t stop  p pause  f freeze  e events  /hub  q close')
    if app.perf_target is not None:
        shortcuts = f"workers {app.c['workers']} → {app.perf_target} · applying in {max(0,app.perf_deadline-time.monotonic()):.1f}s"
    display += [DIM+shortcuts,FAINT+f"q / Ctrl+C closes view; mining continues. /network {app.c['network']}"]
    display=display[:rows]+['']*max(0,rows-len(display))
    return RESET+ESC+'H'+'\r\n'.join(clipped(line,width)+RESET for line in display)
