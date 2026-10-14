# Security and publication

Never add machine.local.json, network-profiles.local.json, .env files, wallets,
RPC cookies, private keys, tokens, runtime logs/databases, .venv or .build to Git.
Do not run `git add .` against an operational miner installation. Work in a clean
checkout and export only the reviewed PUBLIC_FILES.json inventory.

Run scripts/audit_public.py against the staged index before committing, and run
Gitleaks against the index export and all Git history. Inspect findings locally
without printing credential values. A scan is a review aid, not a universal
promise that arbitrary future content is safe. The checked-in Gitleaks exceptions
cover only reviewed checksum records and one catalogue function description.

Local settings use mode 0600 on Unix; on Windows the installer-generated settings
and control endpoint receive a current-user ACL before publication. Unix process
control uses a mode-0600 socket. Windows uses loopback TCP with a random local
credential; the listener binds only 127.0.0.1 and rejects unauthenticated commands.
It does not expose a network management API.

Remote mining peers are authenticated cooperating nodes. Positive hashes and
exclusions are independently checked; negative scan claims are not Byzantine
proofs of work. Non-loopback distribution requires TLS. Never publish peer tokens.
Use HTTPS or a trusted tunnel for calculator authentication and keep Core RPC
private. The miner needs a payout address, not your wallet private keys or seed.

Report vulnerabilities privately through the repository's GitHub security contact
if available. Otherwise ask the maintainer for a private channel without posting
credentials or exploit details in a public issue. Do not upload live logs until
reviewed and redacted.
