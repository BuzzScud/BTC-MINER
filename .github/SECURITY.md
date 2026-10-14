# Security and publication

Never add machine.local.json, network-profiles.local.json, .env files, wallets,
RPC cookies, private keys, tokens, runtime logs/databases, .venv or .build to Git.
Do not run `git add .` against an operational miner installation. Work in a clean
checkout and export only the reviewed .github/manifests/PUBLIC_FILES.json inventory.

Run scripts/audit_public.py against the staged index before committing, and run
Gitleaks against the index export and all Git history with
`--config .github/gitleaks.toml`. Inspect findings locally
without printing credential values. A scan is a review aid, not a universal
promise that arbitrary future content is safe. The checked-in Gitleaks exceptions
cover only reviewed checksum records and one catalogue function description.

Local settings use mode 0600 on Unix; on Windows settings, control endpoint and
worker token files receive a current-user-only ACL before secret bytes are
written. Explicit grants to other users and inherited access are removed.
Worker token files are checked for private permissions before being read; shared
Windows files must be recreated with `cluster init` or have their ACL repaired.
Unix process
control uses a mode-0600 socket. Windows uses loopback TCP with a random local
credential; the listener binds only 127.0.0.1 and rejects unauthenticated commands.
It does not expose a network management API.

Remote mining peers are authenticated cooperating nodes. Positive hashes and
exclusions are independently checked; negative scan claims are not Byzantine
proofs of work. Non-loopback distribution requires TLS. Never publish peer tokens.
Remote calculator URLs require HTTPS. Remote Core requires rpc_tls=on and an
explicit username or cookie path behind a trusted HTTPS proxy. HTTP is allowed
only on loopback, including secure tunnel endpoints. Core and provider clients
refuse redirects and ignore environment HTTP proxies. Automatic Core cookie
discovery is local only. Keep Core RPC private.

`provider login` prompts for an existing provider account and hidden password,
checks account identity, then opens the dashboard. It saves no password/token;
the password is held in the process environment for the dashboard and its child
miner processes, allowing dedicated runtime sessions and reauthentication. Other
processes with sufficient OS privileges may inspect process memory/environment.
Closing the dashboard leaves an explicitly started miner running with its
credentials until stopped. Login does not register accounts or start mining.
The miner needs a payout address, not your wallet private keys or seed.

Report vulnerabilities privately through the repository's GitHub security contact
if available. Otherwise ask the maintainer for a private channel without posting
credentials or exploit details in a public issue. Do not upload live logs until
reviewed and redacted.
