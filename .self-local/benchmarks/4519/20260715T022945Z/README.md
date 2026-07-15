# Issue #4519 benchmark protocol revision 18

Run ID: `20260715T022945Z`.

This directory is the immutable rev18 package.  It is deliberately independent
of rev17: it has its own package, execution root, review root, protocol, and
seals.  The sibling execution and review roots must not exist until their
respective authorities create them.

Lifecycle authority is separated as follows:

1. `calibrate.py setup` creates sealed setup evidence only.
2. `review.py create` (a distinct reviewer) creates the external, sealed setup
   review artifact only.
3. `calibrate.py run` validates both artifacts from disk, re-probes the live
   repository, and is the sole production driver for `Bf Af Ar Br Bw Aw`.

The package seal is `package-manifest.json.sha256`.  It binds every executable
and test file other than the manifest and its detached seal.  Dynamic records
are create-once files with detached SHA-256 seals; replay rejects missing,
extra, reordered, resealed, or live-divergent evidence.

Static acceptance test:

```sh
python3 tests/test_rev18.py
```

No Lake command is invoked by that test.  A production invocation requires the
fixed command from `protocol.json` and all three distinct authorities.
