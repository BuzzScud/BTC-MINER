# Public release implementation

The release uses a clean Git checkout and an explicit public-file inventory.
The original operational installation is not part of the Git repository.

## Preserved mathematics

`research/import-baseline.json` records original exported source identities.
`research/math-preservation.json` binds 131 unchanged source files and 64
unchanged arithmetic function ASTs in modules needing platform-specific loading.
Run `scripts/check_math_integrity.py` to check those boundaries. C sources, Lean
statements, targets, THESIS2 field/flower algorithms, rod/CRT arithmetic, and
candidate/exclusion verification are retained. The initial public profile uses
the original active flower order, step 7 and prime 19. Runtime sources have new
identities where OS adapters or configuration changed; old runtime reports do
not automatically validate those new identities.

The portable proof capsule still checks 299 audited roots, 123 named statements
and 152 retained objects. `research/public-evidence-derivation.json` records the
original/public manifest digests and the metadata dependency-hash mapping.
Personal home paths and account labels were anonymized in metadata. Lean source
and compiled object bytes were not altered. This is a public derivative of
historical kernel evidence, not a new Lean compilation. The verifier repeats all
source/object/assumption/negative-control binding checks. Additional recent
contract sources are bundled under validation/ and btcminer/distribution/;
their inclusion alone is not new proof acceptance.

## Operating-system boundaries

- `btcminer/platform_support.py`: exclusive process locks, bounded pipe reads,
  terminal input, private-file permissions, platform library names and Core paths.
- Unix control: mode-0600 AF_UNIX socket. Windows: authenticated loopback socket,
  with an unpredictable credential in an owner-only endpoint file.
- Windows resource sampling: psutil CPU deltas and PID/start-time-bound process
  trees. Available-memory thresholds are labeled as sampled heuristics. Missing
  measurements deny worker admission; thermal readings are explicitly unavailable.
- CMake builds the same C sources as the Mac installation. Windows x64 uses the
  Visual Studio 2022 ClangCL toolset, including C11 atomics. No Windows symlink
  privilege is required. Native Windows ARM is outside this release's targets.
- Copper retains its rendering and key decoder; its terminal input/output adapter
  changes by OS. Linux desktop-idle detection is unavailable and disclosed.
- Optional Observatory integration requires the separate Observatory project.
  Retained historical terminal/regtest helper scripts can have Unix-only tools;
  the public setup, runtime and CI entry points are the cross-platform interfaces.

## Validation and maintenance

Run setup with no wizard for a build-only check:

```text
python scripts/setup_terminal.py --yes --no-wizard
```

`--yes` is explicit approval for dependency installation and is used in CI.
Ordinary interactive setup prompts first. Setup never downloads Core, starts a
node, mines, or changes existing Core settings. The separate CI helper explicitly
downloads a pinned Core executable and verifies its official HTTPS checksum.

After editing canonical source files:

```text
python scripts/sync_layout.py
python scripts/check_math_integrity.py
python scripts/verify_proof_evidence.py
python -B -m unittest discover -s tests
```

Use the installed virtual environment's Python. The regression suite uses local
fixtures; it does not contact a live pool/provider or mine on a public network.
`scripts/core_smoke.py --bitcoind PATH` explicitly starts a disconnected private
node in a disposable directory, creates 101 funding fixtures, and stops after
exactly one miner-accepted block containing a signed transaction. It checks exact
SHA256d, the engine's Core/Merkle/witness readback, and Core verifychain level 4.
It does not use a caller-provided datadir or control an existing node.

Review additions to PUBLIC_FILES.json, then run scripts/public_manifest.py to
refresh current source identities. This does not upgrade historical evidence.
Run scripts/audit_public.py after staging and Gitleaks on both the public export
and all Git history before pushing. Generated native binaries and user data stay
outside Git. CI builds/tests macOS ARM, macOS Intel, Linux x64 and Windows x64.
CI status is the authoritative record of remote platform results.
