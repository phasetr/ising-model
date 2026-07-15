# Issue #4519 — revision 20 static-only remediation

This is a new static-only root.  Rev18 and rev19 remain retired and are not
read, modified, resumed, or reused.  No setup, review, Lake/Lean/build,
calibration, measurement, freeze, result, or metric action is authorized by
this package.

The future command is fixed, but is not invoked here:

```text
lake --no-ansi --no-cache build IsingModel
```

`harness.py` has no process or network launcher.  It cryptographically verifies
detached Ed25519 signatures and validates the complete proposed chain:
package → setup → review → exact A/B action state machine → journal or terminal
failure → externally published immutable anchor.  Every future action must
bind recursive before/after inventories, exact argv, raw stdout/stderr/time-RSS
and warnings files, their digests, and the warnings count.  A terminal failure
has exactly two state files and cannot be followed by a retry.

The root anchor receipt is published outside this directory in a public GitHub
gist commit.  The receipt binds this package manifest and the four distinct
role keys.  It is not accepted merely because this root says so: validation
checks the supplied public commit bytes, their digest, and an Ed25519 signature.
A later execution anchor must separately bind package/setup/review and its
terminal-or-journal head and itself have a public immutable receipt.
