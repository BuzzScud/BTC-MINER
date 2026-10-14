# Contributor instructions

Keep arithmetic, theorem domains, constants, nonce coverage, and independent
block/exclusion verification unchanged unless a change is explicitly requested.
Use scripts/sync_layout.py after editing canonical src/ or math-library/ sources;
compatibility copies under btcminer/ and native/ must remain byte-identical.
Run scripts/check_math_integrity.py, scripts/verify_proof_evidence.py and relevant
tests. A preserved proof capsule is not a fresh Lean run or whole-program proof.
Never commit local configuration, credentials, wallets, cookies, databases, logs,
virtual environments or private operational artifacts. Follow SECURITY.md.
Use disposable fixtures for tests. Never control an existing user's miner or node.
A private chain test must stop after its first accepted miner block.
Do not suppress test failures or platform limitations. Update PUBLIC_FILES.json
and FILES.sha256.json using scripts/public_manifest.py after reviewing changes.
