"""Full-screen mining cycle and staged settings editor.

Observations describe completed work, not native-stage timing. Mining mutations
use the existing command queue only after explicit Save & apply (Ctrl+S).
"""
import json
import time
from .settings import changes, atomic_json
from .tui import ACCENT, BOLD, DIM, FAINT, GREEN, RED, RESET, YELLOW, ESC
from .tui import clipped, safe, rate
from .copper import box

LABELS = ['Get job', 'Prepare candidates', 'Hash nonces', 'Submit result']
FIELDS = [
    ['connection', 'template_refresh', 'rpc_timeout', 'connect_timeout'],
    ['strategy', 'batch_size', 'thesis2_order', 'thesis2_step', 'thesis2_prime', 'single_nonce_only', 'pruning_enabled'],
    ['workers', 'cpu_duty', 'pause_on_active', 'native_hasher'],
    ['worker', 'pool_difficulty', 'stop_after_block', 'retry_seconds'],
]
HINTS = {
    'connection': 'core or pool; use /setup for endpoints and credentials',
    'strategy': 'thesis2, thesis, linear, hybrid',
    'thesis2_order': 'field or flower; both cover the full nonce domain',
    'pool_difficulty': 'Requested share difficulty; the pool chooses the actual value',
    'thesis2_step': 'Must be coprime to 360',
    'thesis2_prime': 'Uses the existing validated scheduler prime set',
    'pause_on_active': 'Idle seconds before resuming; 0 disables activity pause',
    'native_hasher': 'true or false', 'stop_after_block': 'true or false',
    'single_nonce_only': 'true or false', 'pruning_enabled': 'true or false',
    'template_refresh': 'Seconds between Core template refreshes',
    'rpc_timeout': 'Core RPC timeout in seconds', 'connect_timeout': 'Connection timeout in seconds',
    'retry_seconds': 'Seconds between connection retries',
    'workers': 'CPU worker count', 'cpu_duty': 'CPU duty percentage, 1–100',
    'batch_size': 'Nonces per batch, 64–1,000,000',
}


def load_labels(logs):
    try:
        labels = json.loads((logs/'loop-view.json').read_text())['labels']
        if isinstance(labels, list) and len(labels) == 4 and all(isinstance(s, str) and s.strip() and len(s) <= 40 and s.isprintable() for s in labels):
            return labels
    except (OSError, ValueError, KeyError, TypeError):
        pass
    return list(LABELS)


def begin_edit(app):
    if app.busy:
        app.note('Wait for the current command before editing.', 'notice'); return
    app.perf_target = None
    keys = FIELDS[app.loop_selected]
    app.loop_editor = dict(index=0, keys=['label']+keys,
        values={'label': app.loop_labels[app.loop_selected], **{k:str(app.c[k]) for k in keys}},
        original={k:app.c[k] for k in keys}, text=None, error='')


def save_edit(app):
    from .tui import LOGS
    ed = app.loop_editor
    if app.busy:
        ed['error'] = 'Another command is running. Try again when it finishes.'; return
    try:
        label = ed['values']['label'].strip()
        if not label or len(label)>40 or not label.isprintable():
            raise ValueError('Label must be 1–40 printable characters.')
        # Validate only changed fields against current configuration: unrelated
        # changes arriving from the poller must not be silently overwritten.
        assignments = [f'{k}={ed["values"][k]}' for k in ed['keys'][1:]
                       if ed['values'][k] != str(ed['original'][k])]
        updated = changes(app.c, assignments)
        if assignments and app.s.get('running'):
            from . import service
            service.validate_start(updated)
        labels = list(app.loop_labels); labels[app.loop_selected] = label
        atomic_json(LOGS/'loop-view.json', {'schema':'btc-loop-view/v1', 'labels':labels})
    except (ValueError, OSError) as error:
        ed['error'] = safe(error); return
    app.loop_labels = labels
    app.loop_editor = None
    app.note('Loop labels saved.', 'accepted')
    if assignments:
        # Settings success/failure is reported separately by complete_command.
        app.execute(['config', 'set', *assignments], 'Apply loop settings')


def editor_input(app, key):
    ed = app.loop_editor
    if ed['text'] is not None:
        if key == '\x1b':
            ed['text'] = None
        elif key in ('\r', '\n', '\x13'):
            ed['values'][ed['keys'][ed['index']]] = ed['text']
            ed['text'] = None; ed['error'] = ''
            if key == '\x13':
                save_edit(app)
        elif key in ('\x7f', '\b'):
            ed['text'] = ed['text'][:-1]
        elif key == '\x15':
            ed['text'] = ''
        elif len(key)==1 and key.isprintable() and len(ed['text'])<256:
            ed['text'] += key
        return
    if key == '\x1b':
        app.loop_editor = None
    elif key in ('\x1b[A', '\x1b[B', '\t'):
        ed['index'] = (ed['index'] + (-1 if key=='\x1b[A' else 1)) % (len(ed['keys'])+1)
    elif key == '\x13' or (key in ('\r', '\n') and ed['index']==len(ed['keys'])):
        save_edit(app)
    elif key in ('\r', '\n'):
        ed['text'] = ed['values'][ed['keys'][ed['index']]]


def handle(app, key):
    """True means handled. Other keys retain the existing miner controls."""
    if app.loop_editor is not None:
        editor_input(app, key); return True
    if app.overlay or app.buf is not None or app.network_choice is not None or app.setup_draft is not None:
        return False
    if key in ('1', '2', '3', '4'):
        app.loop_selected = int(key)-1
    elif key in ('\t', '\x1b[C', '\x1b[B'):
        app.loop_selected = (app.loop_selected+1)%4
    elif key in ('\x1b[D', '\x1b[A'):
        app.loop_selected = (app.loop_selected-1)%4
    elif key in ('e', '\r', '\n'):
        begin_edit(app)
    elif key == '\x1b':
        app.loop_mode = False
    else:
        return False
    return True


def editor_lines(app, height):
    ed = app.loop_editor
    lines = [BOLD+ACCENT+f'EDIT STEP {app.loop_selected+1} · {LABELS[app.loop_selected]}',
             DIM+'↑/↓ select · Enter edit · Ctrl+U clears field · Esc cancels',
             YELLOW+'Save & apply restarts a running miner when settings change.']
    field_lines = []
    for i, key in enumerate(ed['keys']):
        value = ed['text']+'▏' if i==ed['index'] and ed['text'] is not None else ed['values'][key]
        field_lines.append((ACCENT+'› ' if i==ed['index'] else DIM+'  ')+key+'  '+ink_safe(value))
    field_lines.append((ACCENT+'› ' if ed['index']==len(ed['keys']) else DIM+'  ')+'SAVE & APPLY  [Ctrl+S]')
    space = max(1, height-6)
    start = max(0, min(ed['index']-space+1, len(field_lines)-space))
    lines += field_lines[start:start+space]
    selected = ed['keys'][ed['index']] if ed['index']<len(ed['keys']) else ''
    lines += [DIM+HINTS.get(selected, 'Labels change the display only; step behavior stays the same.' if selected=='label' else 'Enter saves the draft; Esc discards it.'),
              RED+ed['error'] if ed['error'] else DIM+'Changes stay in this draft until Save & apply.']
    return lines[:height]


def ink_safe(value):
    from .tui import INK
    return INK+safe(value)


def observations(app):
    s = app.frozen['status'] if app.frozen else app.s
    sample = app.frozen['sample'] if app.frozen else app.sample
    now = app.frozen['at'] if app.frozen else time.time()
    observed = app.frozen['observed_at'] if app.frozen else app.observed_at
    running = s.get('running', False)
    fresh = bool(observed and now-observed <= 3)
    scope = ('FROZEN observations · f resumes' if app.frozen else 'Last session · miner stopped' if not running
             else 'Live observations' if fresh else 'STALE · waiting for status')
    telemetry = s.get('model_telemetry', {})
    if telemetry.get('enabled') is False:
        sample = None; scope += ' · sampling disabled'
    if telemetry.get('errors') or telemetry.get('dropped'):
        scope += f" · telemetry {telemetry.get('errors',0)} errors / {telemetry.get('dropped',0)} dropped"
    sample_note = (f"Completed sample · {max(0,now-sample['timestamp']):.1f}s old" if sample else 'No completed sample')
    if sample and sample.get('height') != s.get('height'):
        sample_note += ' · previous height'
    current_sample = sample if sample and sample.get('height') == s.get('height') else None
    job = current_sample['job'][:20] if current_sample else 'awaiting sample'
    hashing = ('Stopped' if not running else 'Status stale' if not fresh else
               'Paused: '+safe(s.get('paused_reason','')) if s.get('state')=='PAUSED' else
               rate(s.get('rates',{}).get('10',0)) if s.get('state')=='MINING' else 'Waiting for work')
    cards = [
        [f"{app.c['connection'].upper()} · {app.c['network']}",
         'Connected' if s.get('connected') and running else 'Disconnected',
         f"Height {s.get('height') if s.get('height') is not None else '—'}", 'Job '+job,
         f"Refresh {app.c['template_refresh']}s · timeout {app.c['rpc_timeout']}s", '/setup connection · /network choose'],
        [app.c['strategy'].upper()+f" · batch {app.c['batch_size']:,}",
         f"{s.get('math_details',{}).get('order',app.c.get('thesis2_order','field'))} · step {app.c['thesis2_step']} · prime {app.c['thesis2_prime']}" if app.c['strategy']=='thesis2' else 'Partition '+app.c['partition'],
         f"{sample['attempted']:,} attempts in sampled batch" if sample else 'Awaiting completed batch',
         'Pruning '+('on' if app.c['pruning_enabled'] else 'off'), sample_note],
        [hashing, f"{s.get('workers',app.c['workers'])} workers · {app.c['cpu_duty']}% duty",
         f"{s.get('hashes',0):,} total hashes", f"Sample nonce {sample['nonce']:,}" if sample else 'No sampled nonce',
         'SHA '+sample['hash'][:24]+'…' if sample else 'No sampled hash', sample_note],
        [f"{s.get('shares_accepted',0):,} shares accepted", f"{s.get('shares_rejected',0):,} solutions rejected",
         f"{s.get('shares_unknown',0):,} unknown outcomes", f"{s.get('blocks_accepted',0):,} Core blocks accepted",
         'Only target-valid results are submitted', 'Pool chooses actual share difficulty'],
    ]
    return scope, cards


def frame(app, cols, rows):
    width = max(0,cols-1)
    scope, cards = observations(app)
    state = safe(app.s.get('state','STOPPED'))
    header = [BOLD+ACCENT+'BTC MINER / LOOP'+DIM+'   '+state,
              DIM+scope+' · sampled completed work, not stage timing']
    alert = ('Stop queued' if app.pending_stop else '') or app.s.get('error') or app.s.get('paused_reason')
    if alert:
        header.append(YELLOW+safe(alert))
    footer = [DIM+'1–4 / Tab select · Enter/e edit · Esc dashboard · / commands',
              DIM+'s start · t stop · p pause · f freeze · +/− CPU · q close view']
    if app.perf_target is not None:
        footer[1] = YELLOW+f'Workers → {app.perf_target} · pending apply'
    secret = app.setup_draft is not None and app.setup_fields and app.setup_fields[0][0]=='pool_password'
    prompt = ('•'*len(app.buf or '') if secret else safe(app.buf or '')) if app.buf is not None else (
        'Applying command…' if app.busy else safe(app.messages[-1][2]) if app.messages else '')
    footer.insert(0, ACCENT+'› '+prompt)
    if rows < 12:
        lines = [header[0], DIM+scope]+[f'{i+1}. {app.loop_labels[i]}' for i in range(4)]
        if app.loop_editor:
            ed = app.loop_editor; i = ed['index']
            key = ed['keys'][i] if i<len(ed['keys']) else 'SAVE & APPLY'
            value = ed['text'] if ed['text'] is not None else ed['values'].get(key,'Ctrl+S')
            lines = [header[0], 'Editing '+key, safe(value), RED+ed['error'], 'Enlarge window for all fields']
        lines = lines[:max(0,rows-2)] + footer[-2:]
    else:
        height = rows-len(header)-len(footer)
        if app.loop_editor:
            body = box(width,height,'STEP EDITOR',editor_lines(app,max(0,height-2)))
        elif app.network_choice is not None or app.setup_draft is not None or app.buf is not None or app.overlay:
            body = box(width,height,'COMMANDS / REPORT',app.panel(max(0,height-2)))
        elif cols>=76 and height>=13:
            left = (width-5)//2; right = width-5-left
            top = (height-1)//2; bottom = height-1-top
            def card(i,w,h):
                title = ('▶ ' if app.loop_selected==i else '')+f'{i+1:02} '+app.loop_labels[i]
                return box(w,h,title,[ink_safe(x) for x in cards[i]])
            a,b = card(0,left,top), card(1,right,top)
            c,d = card(3,left,bottom), card(2,right,bottom)
            body = [x+(ACCENT+' ──→ ' if j==top//2 else '     ')+y for j,(x,y) in enumerate(zip(a,b))]
            body += [ACCENT+' '*max(0,left//2)+'↑'+' '*max(0,left+5+right//2-left//2-1)+'↓']
            body += [x+(ACCENT+' ←── ' if j==bottom//2 else '     ')+y for j,(x,y) in enumerate(zip(c,d))]
        else:
            body = []
            for i in range(4):
                h = height//4+(1 if i<height%4 else 0)
                title = ('▶ ' if app.loop_selected==i else '')+f'{i+1:02} '+app.loop_labels[i]+(' ↓' if i<3 else ' ↺ 01')
                body += box(width,h,title,[ink_safe(x) for x in cards[i]])
        lines = header+body+footer
    lines = lines[:rows]+['']*max(0,rows-len(lines))
    return RESET+ESC+'H'+'\r\n'.join(clipped(line,width)+RESET for line in lines)
