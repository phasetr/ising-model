#!/usr/bin/env python3
"""Adversarial tamper checks for the package/review/terminal anchor bindings."""

from __future__ import annotations

import base64
import copy
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("harness", ROOT / "harness.py")
assert spec and spec.loader
harness = importlib.util.module_from_spec(spec)
spec.loader.exec_module(harness)


def rejects(callback) -> None:
    try:
        callback()
    except harness.BoundaryError:
        return
    raise AssertionError("tampered chain was accepted")


def test_rfc8032_signature_is_cryptographically_verified() -> None:
    raw_public = bytes.fromhex("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
    pem = "-----BEGIN PUBLIC KEY-----\n" + base64.b64encode(bytes.fromhex("302a300506032b6570032100") + raw_public).decode() + "\n-----END PUBLIC KEY-----\n"
    # RFC 8032 test vector 1 (empty message).
    signature = "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155" + "5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"
    harness.verify_ed25519(pem, b"", base64.b64encode(bytes.fromhex(signature)).decode())
    rejects(lambda: harness.verify_ed25519(pem, b"x", base64.b64encode(bytes.fromhex(signature)).decode()))


def test_review_reseal_is_rejected_without_anchor_replacement() -> None:
    anchor = {"package_manifest_sha256": "package", "setup_sha256": "setup", "review_sha256": "review", "terminal_or_journal_head_sha256": "terminal"}
    rejects(lambda: harness.reject_reseal_without_anchor(anchor, "package", "setup", "forged-review", "terminal"))


def test_package_tamper_is_rejected_without_anchor_replacement() -> None:
    anchor = {"package_manifest_sha256": "package", "setup_sha256": "setup", "review_sha256": "review", "terminal_or_journal_head_sha256": "terminal"}
    rejects(lambda: harness.reject_reseal_without_anchor(anchor, "forged-package", "setup", "review", "terminal"))


def test_terminal_reseal_is_rejected_without_anchor_replacement() -> None:
    anchor = {"package_manifest_sha256": "package", "setup_sha256": "setup", "review_sha256": "review", "terminal_or_journal_head_sha256": "terminal"}
    rejects(lambda: harness.reject_reseal_without_anchor(anchor, "package", "setup", "review", "forged-terminal"))


def test_full_chain_state_machine_rejects_review_and_terminal_tampering() -> None:
    """Exercise every chain edge; Ed25519 itself is covered by the RFC vector above."""

    protocol = json.loads((ROOT / "protocol.json").read_text(encoding="utf-8"))
    inventory = {".": {"type": "directory", "mode": 0o700, "device": 1, "inode": 1}}
    raw_bytes = {f"raw/Bf/{name}": base64.b64encode(value).decode() for name, value in {
        "stdout.raw": b"out", "stderr.raw": b"err", "time-rss.raw": b"rss", "warnings.raw": b""}.items()}
    raw = {name: {"path": f"raw/Bf/{name}", "sha256": hashlib.sha256(base64.b64decode(raw_bytes[f"raw/Bf/{name}"])).hexdigest()}
           for name in ("stdout.raw", "stderr.raw", "time-rss.raw", "warnings.raw")}
    raw["warnings.raw"]["warning_count"] = 0
    setup = {"schema": harness.SCHEMA + ".setup", "run_id": harness.RUN_ID, "stage": "setup", "command": harness.ARGV,
             "worktrees": {label: {"head": sha, "detached": True, "tracked_clean": True,
                                     "root": {"device": index + 1, "inode": index + 1}, "inventory": inventory}
                           for index, (label, sha) in enumerate((("A", harness.BEFORE), ("B", harness.AFTER)))}}
    package_sha = harness.digest(json.loads((ROOT / "package-manifest.json").read_text(encoding="utf-8")))
    setup_sha = harness.digest(setup)
    review = {"schema": harness.SCHEMA + ".review", "run_id": harness.RUN_ID, "approved": True,
              "package_manifest_sha256": package_sha, "setup_sha256": setup_sha}
    review_sha = harness.digest(review)
    action = {"schema": harness.SCHEMA + ".action", "run_id": harness.RUN_ID, "index": 0, "action": "Bf",
              "argv": harness.ARGV, "prior_sha256": review_sha, "returncode": 0,
              "before_inventory": inventory, "after_inventory": inventory, "raw": raw, "raw_bytes": raw_bytes}
    action_sha = harness.digest(action)
    terminal = {"schema": harness.SCHEMA + ".terminal-failure", "run_id": harness.RUN_ID, "index": 1, "action": "Af",
                "argv": harness.ARGV, "prior_sha256": action_sha, "returncode": 1,
                "state_files": sorted(harness.TERMINAL_ALLOWLIST), "execution_inventory": inventory,
                "raw": raw, "raw_bytes": raw_bytes}
    terminal_sha = harness.digest(terminal)
    anchor = {"schema": harness.SCHEMA + ".execution-anchor", "run_id": harness.RUN_ID,
              "package_manifest_sha256": package_sha, "setup_sha256": setup_sha, "review_sha256": review_sha,
              "terminal_or_journal_head_sha256": terminal_sha,
              "publication": {"kind": "github-gist-git-commit", "commit_sha": "0" * 40}}
    published = harness.canonical({key: value for key, value in anchor.items() if key != "publication"})
    anchor["publication"]["published_object_sha256"] = hashlib.sha256(published).hexdigest()
    original = harness.verify_signed
    harness.verify_signed = lambda root, protocol, role, record, signature: harness.digest(record)
    try:
        harness.validate_full_chain(ROOT, protocol, package_sha, (setup, {}), (review, {}), [(action, {})], (terminal, {}), (anchor, {}, published))
        bad_review = copy.deepcopy(review); bad_review["approved"] = False
        rejects(lambda: harness.validate_full_chain(ROOT, protocol, package_sha, (setup, {}), (bad_review, {}), [(action, {})], (terminal, {}), (anchor, {}, published)))
        bad_terminal = copy.deepcopy(terminal); bad_terminal["state_files"].append("state/forged.json")
        rejects(lambda: harness.validate_full_chain(ROOT, protocol, package_sha, (setup, {}), (review, {}), [(action, {})], (bad_terminal, {}), (anchor, {}, published)))
    finally:
        harness.verify_signed = original
