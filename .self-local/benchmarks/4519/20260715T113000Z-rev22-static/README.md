# Issue #4519 — revision 22 static-only evidence package

This is a fresh static-only package.  Rev18 through Rev21 remain immutable and
are neither read as reusable authority nor modified.  It authorizes no setup,
review, Lake/Lean/build, calibration, measurement, freeze, publication,
metric, source, import, or documentation action.

`package-manifest.json` is the independent canonical package target: it hashes
every static package file, including `harness.py`, and deliberately does not
hash itself.  This removes the only unavoidable self-reference while keeping
the validator in the signed package boundary.  The public root anchor signs
both that manifest digest and the full `harness.py` byte digest.

The validator fetches the sole fixed raw anchor URL and verifies that exact
bytes against its immutable Gist history commit before accepting its Ed25519
signature.  It validates a signed setup/review/action/terminal/anchor chain;
the tests use real deterministic Ed25519 signatures.  A terminal inventory is
an exact recursive `lstat` object allowlist, so added directories, symlinks,
devices, or files fail even if ordinary file checks would miss them.
