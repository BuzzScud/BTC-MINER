# Ember terminal implementation

Design 1 from the terminal study is now the default Python TUI. This is a
presentation update on the existing miner: no new runtime dependencies, settings,
commands or theme selector.

## What changed

- Warm charcoal background, copper accents, soft green results and amber notices.
- Full-width identity, selected network, connection, worker and state information.
- Event ledger with timestamps and event kinds in the main column.
- A grouped session/results/engine/strategy/connection rail; the existing 10s,
  60s and 15m rate windows and all four result counters remain distinct.
- The same main column hosts command selection, setup and scrolling reports.
- Persistent prompt, shortcut hints and reminder that closing the view leaves a
  running miner running.
- Compact layout below 100 columns or 24 rows. Secondary rail details yield first
  at intermediate heights. The prompt remains inside even very small terminals.
- Display-cell clipping for CJK/full-width text and combining accents, and style
  resets between columns. Password input and saved password defaults stay masked.
- Stopped results are labeled as the last session; saved rates are not shown as
  live. All values still come from the existing status/configuration data.

`btcminer/tui.py` contains the changes to colors, clipping, `rail()`, `frame()` and
the extracted `panel()` renderer. The loop's background color is now `#201e1b`.
There are no changes to mining algorithms, socket requests or service lifecycle.

## Preserved behavior

An AST comparison with the pre-change source verified that initialization, event
recording, polling, command execution, setup, command parsing, worker adjustment
and keyboard input methods are unchanged. This includes the original palette Tab
behavior. The existing idle policy, queued stop and 1.5-second worker debounce
still apply. `s` starts/attaches, `t` stops and saves the Desktop summary, and
`q`/Ctrl+C closes the view. Network switching and all existing math reports remain
under their current command handlers.

The miner's independently updated math code is preserved. This interface update
does not claim new math, hash performance, telemetry or real-network validation.

## Verification

- All eight existing terminal-control tests pass.
- Thirteen new presentation tests cover state/panel/resize combinations, sparse
  status, distinct result counters, all four strategies and both connection
  types, setup masking, report scrolling, palette selection, pause/stop/worker
  feedback, and clipping. The size matrix covers 1×1 through 140×45. The audit
  added checks that compact stopped results retain their last-session label and
  that a queued stop does not hide an activity-pause explanation.
- A fixture-backed pseudo-terminal session exercised the actual input/render loop,
  command palette, help, resize to 80×24 and 140×45, then exit through each of `q`,
  Ctrl+C, SIGHUP and SIGTERM. Terminal modes, cursor, wrapping, alternate screen, background
  and signal handlers were restored. The check ignores macOS's kernel-owned
  PENDIN bookkeeping flag when comparing terminal attributes. No lifecycle commands
  were allowed in these sessions. The check is reproducible with the included
  `scripts/check_ember_terminal.py`; its report records the tested source hashes.
- The check writes its pseudo-terminal report under `validation/ember/` when run.
  Earlier fixture frames and reports remain available in Git history.
- The portable build runs native SHA256d self-tests and the complete offline
  regression suite in a clean staging folder. Its manifest records exact packaged
  file hashes. Historical Core regtest evidence is not asserted to cover the new
  renderer; the build checks evidence hashes before making that claim.

The Ember archive is built under `dist/ember/` to keep it separate from other
builds in this shared working folder. Existing configuration and network profiles
are not part of the archive.

```bash
python3 -B -m unittest discover -s tests -p 'test_tui*.py' -v
python3 -B scripts/check_ember_terminal.py
python3 -B scripts/build.py --output dist/ember
```
