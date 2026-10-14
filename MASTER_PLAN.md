# Miner research and release contracts

This project uses a Bitcoin miner, exact coprime-rod arithmetic and a separate
calculator observatory to study mathematical correctness, implementation behavior
and measured cost. The objective is reproducible evidence: neither visual patterns,
provider certification labels nor mathematical analogy establishes a SHA-256
shortcut. Every successor MUST preserve domains, counterexamples and unproved gaps.

## Six work areas and ownership

1. **Miner release and mathematical admission.** This folder owns the source
   manifest, scoped proof capsule, safe theorem publication and clean build gates.
   Start at [README](README.md), then PROOF-01 and RELEASE-01 below.
2. **Live modeling and integration.** The separate observatory owns framebuffer
   display, independent display/network clocks, shared-model lifecycle and read-only
   miner telemetry. Read its [master plan](../bitcoin-algorithm-observatory-2026-10-07/MASTER_PLAN.md)
   and [contracts](../bitcoin-algorithm-observatory-2026-10-07/CONTRACTS.md).
   Recorded/synthetic/live data MUST remain visibly distinguishable. A viewer MAY
   observe the miner; observation SHALL NOT grant it operational control.
3. **Remaining mathematics and Lean proofs.** Each project owns its exact theorem
   sources, input domains, bounded resource settings, axiom audits and failure
   controls. The [miner capsule](research/proof-evidence/manifest.json) and the
   observatory's [coverage ledger](../bitcoin-algorithm-observatory-2026-10-07/catalogue-study/proofs/coverage-ledger.json)
   have separate scopes. An unproved general claim SHALL NOT become proved merely
   because finite instances, returned values or a visualization agree. The
   [separate calculator finite-output supplement](../calculator-fix-kit-2026-10-06/lean-values/remaining-proof-work-20261007/review.json)
   has its own source/object/axiom gate; its receipt is recorded as external
   navigation context in the miner registry, without adding its roots to miner
   acceptance or erasing its remaining unproved cases.
4. **Benchmarks and statistical interpretation.** The observatory owns controlled
   workload definitions, unique-input accounting, request/latency metrics and
   benchmark proof receipts. See its [benchmark workspace](../bitcoin-algorithm-observatory-2026-10-07/benchmarks/)
   and contract index. Rates SHALL include comparable work; repeated deterministic
   inputs are not independent observations, and API latency is not CPU time.
5. **Provider corrections and feedback.** The provider owns deployment of its
   calculator/daemon/API. Local patches and authenticated issue submissions are
   distinct from production changes. Review [current handoff readiness](validation/provider-readiness-20261007/handoff-readiness.json),
   [current frontend rebase](validation/provider-readiness-20261007/frontend-rebase.json)
   and [handoff preparation](validation/provider-readiness-20261007/prepare_handoff.py).
   MUST retain exact upstream baselines, reproduced failures, tests and accepted
   issue receipts; SHALL never label a locally tested patch as deployed without
   deployment and independent post-deployment evidence.
6. **Node and miner operations.** The operational owner coordinates explicitly
   authorized node upgrades, wallet-safe backups, loaded-source verification and
   bounded observation. Read [release verification](validation/core-upgrade-20261007/release-verification.json),
   [activation receipt](validation/core-upgrade-20261007/activation.json) and
   [operational soak](validation/core-upgrade-20261007/operational-soak.json).
   A passing short observation SHALL NOT claim indefinite reliability or replace
   unperformed pool, thermal, crash or sleep/wake qualifications. Wallet files,
   credentials and private backups MUST be excluded from distributable evidence.

Sibling-project and operational links require the full research workspace. The
portable miner ZIP intentionally carries only its explicit public release inputs;
its mathematical report and verifier have no sibling-directory dependency.

## Contract map

### PROOF-01 — admit exact statements with current evidence

[`btcminer/proof_evidence.py`](btcminer/proof_evidence.py) MUST verify current Lean
source hashes, retained compiled objects, all local final-review bindings, matching
raw/Lake theorem inventories and negative controls. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted assumptions. A historic log line,
source comment, proof filename or provider boundary flag SHALL NOT substitute for
this gate. Capsule verification checks recorded artifacts; it does not run Lean.

The [portable report](research/proof-evidence/report.html) and
[manifest](research/proof-evidence/manifest.json) bind the repaired RodCircles,
RodScaling and TowerCollapse closure plus five actual provider integer outputs.
The current capsule contains 299 audited roots, 123 explicitly named statements
and all 45 original target theorem headers. Generated roots are counted separately
from the named research registry. Other proof projects have their own counts and
gates; these numbers MUST NOT be used as universal project constants.

Full-workspace fresh replay is defined by
[`validation/miner-proof-repair-20261007/MASTER_PLAN.md`](validation/miner-proof-repair-20261007/MASTER_PLAN.md)
and its Makefile. It needs the pinned Lean/Lake toolchain and external package
objects. The release ships mathematical sources and recorded objects, not that
complete external toolchain. The old failed runs remain historical evidence.

### PUBLISH-01 — preserve semantics when exposing calculations

[`scripts/publish_archive_calculations.py`](scripts/publish_archive_calculations.py)
MUST admit a current capsule before publication. Supported translations currently
consist of five closed natural-number multiplication equalities, matched against
exact source syntax and checked through the native shared abacus. New translation
forms SHALL retain every variable type and hypothesis and need their own review
and meaningful tests. A proof-only theorem SHALL NOT be exposed using a guessed
expression. No published entry has Bitcoin nonce-exclusion authority.

[`btcminer/theorem_calculations.py`](btcminer/theorem_calculations.py) checks the
catalogue at the public calculation boundary. The
[proof registry](research/proof-registry.json) records all accepted named roots;
118 currently have no supported executable translation. The
[claims registry](research/claims.json) retains its separate unresolved claims.
Finite native checks establish the recorded instances, not a universal C/Python
refinement proof.

### RELEASE-01 — fail closed before packaging

[`scripts/build.py`](scripts/build.py) MUST check proof evidence, translations,
registry and the current explicit source manifest before staging. It SHALL repeat
the gate on staged copies, compile native code there, run self-tests and isolated
offline regression tests, then publish the archive atomically. BUILD-INFO SHALL
state proof scope and whether Lean was freshly run. Optional solver skips and
historical network evidence are separate qualifications, never hidden passes.

```sh
python3 -B scripts/verify_proof_evidence.py
python3 -B scripts/publish_archive_calculations.py
python3 -B scripts/refresh_research_metadata.py
python3 -B scripts/build.py
```

Metadata refresh is explicit review bookkeeping, not evidence generation. It
cannot make a changed mathematical source pass the proof gate. A developer MUST
review source changes before refreshing FILES.sha256.json. The portable verifier
and capsule report work after ZIP extraction without original absolute paths;
original paths inside receipts are provenance keys resolved through capsule
objects. Older README research links require the full research workspace.

### ARCHIVE-01 — preserve history and precise remaining obligations

[`scripts/refresh_research_metadata.py`](scripts/refresh_research_metadata.py)
SHALL preserve replaced metadata under `research/registry-history/`. It updates
current source identities without relabeling old runtime evidence as current.
The capsule exporter in the full workspace similarly preserves previous capsules
and publishes a validated manifest atomically. FILES.sha256.json covers explicit
release inputs and excludes itself; the ZIP receives its own complete file map.

[`btcminer/research_system.py`](btcminer/research_system.py) MAY discover additional
Lean declarations, including observatory sources. Discovery is explicitly
unverified. Accepted repair entries pass PROOF-01. The
[provider coverage snapshot](research/provider-coverage-ledger.json) retains
formula-specific domains and remaining obligations verbatim. Its
[reference](research/provider-coverage-reference.json) binds the external source;
it is context, not imported proof acceptance. Refresh it explicitly with
`--observatory /path/to/bitcoin-algorithm-observatory-2026-10-07` after that project's
gate finishes. The observatory owns its fresh proofs and ledger. Do not replace
an obligation list with the statement that all calculator formulas are proved.

### LIVE-01 — distinguish source changes from the running process

The research, packaging and proof capsule workflows described here MUST NOT stop,
restart, reconfigure or mine
through the user's active miner/node. Tests SHALL use temporary folders, fixtures
and disposable services. A running process can retain older loaded code; a source
hash update is not deployment. Only an explicitly coordinated operational change
may reload live code. The historical `bounded_miner_proof_audit.py` is a separate
manual maintenance command that can stop/restart a miner; importing it for a mocked
regression test does not authorize running it against a live process. Build success does not establish live pool compatibility,
profitability, complete thermal/sleep/crash qualification or a mining advantage.

## Verification and traversal

Start with this file, then read the named module's MUST/SHALL comments and its
linked contract. [Proof and publication tests](tests/test_proof_evidence.py) inject
stale sources, missing/corrupt artifacts, disallowed assumptions and altered
translations. [Release tests](tests/test_release_contracts.py) check copied package
inputs and precise registry admission. [VALIDATION.md](VALIDATION.md) separates
current acceptance from historical measurements. Future AIs MUST keep those
boundaries clear when adding formulas, numerical approximations or new models.


### LIBRARY-01 — use the selected Aristotle reference for new miner math

The user selected [this Aristotle project and completed task](https://aristotle.harmonic.fun/projects/9b854e2d-2ae1-4d55-9b53-bf308b5e3648?view=log&task=f63ca67a-6894-4e23-9452-e560c3c161f9)
as the reference for continuing miner evidence and mathematical validation.
Start at the [math library workflow](validation/miner-math-library-20261010/README.txt)
and its [source-bound catalogue](validation/miner-math-library-20261010/catalogue.json).
These links require the full workspace, not the portable miner release.

The pinned upstream registry has 1,750 classified entries. The separate local
library gate freshly checked 168 named theorems and 667 total roots in ten
modules, with the same three-axiom policy as PROOF-01. Seven files have strictly
import-only adaptations; their original bodies and untouched remote versions
are retained. Sixty upstream headline entries match this fresh subset. Other
entries are reference-only here. The upstream registry permits additional
compiler-trust assumptions, so its completion label SHALL NOT substitute for
the miner's local gate. The 299-root release capsule is a separate scope.

New mathematical work MUST preserve this task's immutable baseline, identify
any later revision explicitly, retain theorem domains and hypotheses, and bind
sources, dependencies, audited proof objects, failure controls and runtime
checks. Use `library.py verify` and its checked arithmetic interface for the
supported calculations. Further runtime translations require their own review;
none of these statements grants Bitcoin nonce-exclusion authority or proves
complete C/Python implementation refinement. Live operational changes still
follow LIVE-01.
