#!/usr/bin/env python3
"""Adversarial boundary cases for a future authorized rev19 executor.

The test is deliberately pure: it has no worktree, process, Lake, Lean, or
benchmark operation.  It proves the validation boundary rejects the two
required tamper classes before an executor could consume any run authority.
"""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("issue4519_harness", ROOT / "harness.py")
assert spec and spec.loader
harness = importlib.util.module_from_spec(spec)
spec.loader.exec_module(harness)
PROTOCOL = json.loads((ROOT / "protocol.json").read_text(encoding="utf-8"))


def rejects(callback) -> None:
    """Assert that the sealed boundary rejects one adversarial input."""

    try:
        callback()
    except harness.BoundaryError:
        return
    raise AssertionError("tampering was accepted")


def signature(role: str) -> dict[str, object]:
    """Provide the already-verified shape expected from an external verifier."""

    return {"algorithm": "Ed25519", "key_id": PROTOCOL["authority"][role]["key_id"], "verified": True}


def inventory() -> dict[str, dict[str, object]]:
    """Return a minimal complete recursive-lstat inventory fixture."""

    return {".": {"type": "directory", "mode": 0o700, "device": 1, "inode": 1}}


def test_extra_file_is_rejected() -> None:
    """An extra file cannot be added after a sealed inventory is recorded."""

    rejects(lambda: harness.reject_extra_or_resealed({".", "unexpected"}, {"."}, "anchor", "anchor"))


def test_full_chain_reseal_without_anchor_key_is_rejected() -> None:
    """Re-signing package/setup/review/run cannot replace the old anchor digest."""

    rejects(lambda: harness.reject_extra_or_resealed({"."}, {"."}, "old-anchor", "new-anchor"))


def test_terminal_extra_file_is_rejected() -> None:
    """A sealed terminal directory cannot acquire an unrecorded companion file."""

    sealed = {"state/terminal-failure.json", "state/terminal-failure.sig"}
    rejects(lambda: harness.reject_extra_or_resealed(sealed | {"state/forged.json"}, sealed,
                                                     "anchor", "anchor"))


def test_terminal_failure_requires_all_raw_evidence_and_run_signature() -> None:
    """A terminal failure missing RSS/warnings is not sealable or retryable evidence."""

    incomplete = {"schema": harness.SCHEMA + ".terminal-failure", "run_id": harness.RUN_ID,
                  "action": "Bf", "returncode": 1, "prior_chain_sha256": harness.digest([]),
                  "raw": {"stdout": {"path": "stdout", "sha256": "a"},
                          "stderr": {"path": "stderr", "sha256": "b"}},
                  "execution_inventory": inventory(), "signature": signature("run")}
    rejects(lambda: harness.validate_terminal(incomplete, [], PROTOCOL))


def test_anchor_key_confusion_is_rejected() -> None:
    """A review key cannot certify the independent immutable anchor."""

    anchor = {"schema": harness.SCHEMA + ".external-anchor", "run_id": harness.RUN_ID,
              "package_sha256": "p", "setup_sha256": "s", "review_sha256": "r",
              "terminal_or_journal_head_sha256": "j", "published_immutable": True,
              "signature": signature("review")}
    rejects(lambda: harness.validate_anchor(anchor, "p", "s", "r", "j", PROTOCOL))
