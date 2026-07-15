# Issue #4519 — rev19 static remediation package

This new evidence root is static-only and does not authorize setup, review,
worktree creation, Lake/Lean execution, calibration, measurement, freeze,
results, or metric calculation. Rev18 (`20260715T022945Z`) remains retired and
is not read, changed, or reused.

The fixed comparison is before
`6a2470114fe0b5dd5c6cdcbb0e02b8acca351fb4` and after
`94ceb4f83906dc23069b7566ce31242240e22855`. A future separately authorized
executor has exactly one root command:

```text
lake --no-ansi --no-cache build IsingModel
```

`protocol.json` is the static contract. It requires detached A/B worktrees at
those SHA identities, different `(device,inode)` root pairs, and a recursive
lstat inventory at setup, before and after every action, and terminal failure.
Each future action must archive byte-for-byte stdout, stderr, `/usr/bin/time
-l` output (including RSS), and a raw warning report.

Setup, review, run, and anchor are four distinct Ed25519 public-key identities.
The anchor is published through a separate immutable authority and binds the
package, setup, review, and terminal-or-journal head. Thus re-signing records
with setup/review/run keys cannot make an altered full chain admissible.

The harness has no subprocess launcher. Its only purpose is validation of
future supplied evidence; a failed declared action must produce the exact
signed terminal record and cannot be retried. The static source contract has
tests for extra-file, review-reseal, terminal-extra-file, and full-chain-reseal
rejection. No test or command was run while producing this package.
