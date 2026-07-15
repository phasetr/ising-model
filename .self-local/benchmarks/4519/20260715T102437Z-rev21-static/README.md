# Issue #4519 — revision 21 static-only evidence package

This fresh root does not modify Rev18, Rev19, or Rev20.  It grants no setup,
review, Lake/Lean/build, calibration, measurement, freeze, result, metric, or
documentation action.

The only future command is protocol data and is not invoked by this package:

```text
lake --no-ansi --no-cache build IsingModel
```

`harness.py` is a validator, not an executor.  It requires the externally
published, fixed-commit root-anchor bytes before it evaluates the signed setup,
review, action/terminal, and execution-anchor chain.  It never takes root
anchor bytes from a caller.  Each action is fixed to A or B, carries a unique
action id, reads its four raw evidence files from disk, binds exact argv, and
links recursive inventory digests from setup through before and after state.
Warning counts are derived from `warnings.raw`.  A terminal record contains an
exact terminal-state inventory and is terminal: no continuation action is
accepted.

The manifest intentionally lists protocol, public keys, documentation, and
tests.  The validator contains the published anchor's fixed immutable URL and
digest, preventing a mutable receipt from selecting a root authority.
