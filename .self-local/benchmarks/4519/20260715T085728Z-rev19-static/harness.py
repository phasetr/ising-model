#!/usr/bin/env python3
"""Static contract and future sealed-boundary validator for Issue #4519 rev19.

This module intentionally has no process launcher: the static-remediation
package must not run Lake, Lean, calibration, or a benchmark.  A separately
authorized future executor must supply the records validated here.
"""

from __future__ import annotations

import hashlib
import json
from typing import Any


SCHEMA = "ising-model.issue-4519.rev19.static-remediation"
RUN_ID = "20260715T085728Z"
BEFORE = "6a2470114fe0b5dd5c6cdcbb0e02b8acca351fb4"
AFTER = "94ceb4f83906dc23069b7566ce31242240e22855"
ARGV = ["lake", "--no-ansi", "--no-cache", "build", "IsingModel"]
TIME_RSS_COMMAND = ["/usr/bin/time", "-l"]
PLAN = ["Bf", "Af", "Ar", "Br", "Bw", "Aw"]
ROLES = ("setup", "review", "run", "anchor")


class BoundaryError(ValueError):
    """Raised when an evidence record cannot cross the sealed boundary."""


def canonical(value: Any) -> bytes:
    """Return the single permitted JSON encoding for a signed record."""

    return (json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode()


def digest(value: Any) -> str:
    """Hash canonical evidence rather than an implementation-dependent repr."""

    return hashlib.sha256(canonical(value)).hexdigest()


def require(condition: bool, message: str) -> None:
    """Stop at the first invariant violation."""

    if not condition:
        raise BoundaryError(message)


def validate_protocol(protocol: dict[str, Any]) -> None:
    """Check all five remediation commitments before any future execution exists."""

    require(protocol.get("schema") == SCHEMA and protocol.get("revision") == 19,
            "wrong revision identity")
    require(protocol.get("run_id") == RUN_ID and protocol.get("static_only") is True,
            "dynamic authority is absent from this revision")
    require(protocol.get("before") == BEFORE and protocol.get("after") == AFTER,
            "fixed A/B SHA binding changed")
    require(protocol.get("command") == ARGV and protocol.get("plan") == PLAN,
            "required root command or alternating plan changed")
    authority = protocol.get("authority")
    require(type(authority) is dict and set(authority) == set(ROLES), "four distinct authorities required")
    key_ids = [authority[role].get("key_id") for role in ROLES]
    fingerprints = [authority[role].get("spki_sha256") for role in ROLES]
    require(all(type(value) is str and len(value) == 64 for value in fingerprints),
            "authority needs immutable public-key fingerprints")
    require(len(set(key_ids)) == len(ROLES) and len(set(fingerprints)) == len(ROLES),
            "role names are not authority: keys must be distinct")
    contract = protocol.get("evidence_contract")
    require(type(contract) is dict, "missing evidence contract")
    require(contract["ab_worktrees"]["detached"] is True and
            contract["ab_worktrees"]["root_inode_relation"] == "A.device_inode != B.device_inode",
            "A/B detached inode-disjoint worktrees are mandatory")
    require(contract["raw_capture"]["per_action"] == ["stdout.raw", "stderr.raw", "time-rss.raw", "warnings.raw"],
            "raw stdout/stderr/time-RSS/warning retention changed")
    require(contract["raw_capture"]["time_command"] == TIME_RSS_COMMAND,
            "required raw time/RSS command changed")
    require(contract["inventory"]["algorithm"] == "recursive-lstat-v1", "recursive inventory missing")
    require(contract["authority"]["anchor_is_externally_published"] is True,
            "external immutable authority missing")
    require(set(contract["tamper_tests"]) == {"extra-file-rejected", "review-reseal-rejected-by-anchor",
                                                "terminal-extra-file-rejected",
                                                "full-chain-reseal-rejected-without-anchor-key"},
            "sealed tamper matrix incomplete")


def validate_inventory(inventory: dict[str, dict[str, Any]]) -> None:
    """Require an exact recursive lstat inventory, including its root object."""

    require(type(inventory) is dict and "." in inventory, "recursive inventory has no root")
    for relative, facts in inventory.items():
        require(type(relative) is str and type(facts) is dict, "invalid inventory item")
        require(facts.get("type") in {"directory", "file", "symlink"}, "unsupported object type")
        require(all(type(facts.get(key)) is int for key in ("mode", "device", "inode")),
                "lstat facts are incomplete")
        if facts["type"] == "file":
            require(type(facts.get("size")) is int and type(facts.get("sha256")) is str,
                    "file digest is absent")
        if facts["type"] == "symlink":
            require(type(facts.get("link")) is str, "symlink text is absent")


def validate_setup(record: dict[str, Any], protocol: dict[str, Any]) -> None:
    """Validate two exact detached, clean, inode-disjoint worktrees and inventories."""

    require(record.get("schema") == SCHEMA + ".setup" and record.get("run_id") == RUN_ID,
            "wrong setup record")
    worktrees = record.get("worktrees")
    require(type(worktrees) is dict and set(worktrees) == {"A", "B"}, "setup lacks A/B roots")
    expected = {"A": protocol["before"], "B": protocol["after"]}
    for label, head in expected.items():
        item = worktrees[label]
        require(item.get("detached") is True and item.get("head") == head and item.get("tracked_clean") is True,
                "worktree is not fixed, detached, and clean: " + label)
        require(type(item.get("root")) is dict, "root lstat missing: " + label)
        require(all(type(item["root"].get(key)) is int for key in ("device", "inode")),
                "root inode facts missing: " + label)
        validate_inventory(item.get("inventory"))
    left, right = worktrees["A"]["root"], worktrees["B"]["root"]
    require((left["device"], left["inode"]) != (right["device"], right["inode"]),
            "A/B root inode alias")


def signed_by(record: dict[str, Any], role: str, protocol: dict[str, Any]) -> None:
    """Require a future verifier to bind the record to the specified distinct key."""

    signature = record.get("signature")
    require(type(signature) is dict and signature.get("algorithm") == "Ed25519", "missing Ed25519 signature")
    require(signature.get("key_id") == protocol["authority"][role]["key_id"], "authority-key confusion")
    require(signature.get("verified") is True, "signature has not been externally verified")


def validate_terminal(record: dict[str, Any], prior_chain: list[dict[str, Any]], protocol: dict[str, Any]) -> None:
    """Seal a failed run as terminal and bind its raw evidence to the full prior chain."""

    require(record.get("schema") == SCHEMA + ".terminal-failure" and record.get("run_id") == RUN_ID,
            "wrong terminal record")
    require(record.get("action") in PLAN and type(record.get("returncode")) is int and record["returncode"] != 0,
            "terminal record does not describe a failed declared action")
    require(record.get("prior_chain_sha256") == digest(prior_chain), "terminal record breaks journal chain")
    raw = record.get("raw")
    require(type(raw) is dict and set(raw) == {"stdout", "stderr", "time_rss", "warnings"},
            "terminal record lacks raw stdout/stderr/time-RSS/warnings")
    for item in raw.values():
        require(type(item) is dict and type(item.get("path")) is str and type(item.get("sha256")) is str,
                "raw evidence is not content-addressed")
    validate_inventory(record.get("execution_inventory"))
    signed_by(record, "run", protocol)


def validate_anchor(anchor: dict[str, Any], package_sha256: str, setup_sha256: str, review_sha256: str,
                    terminal_or_head_sha256: str, protocol: dict[str, Any]) -> None:
    """Require the distinct external authority to prevent full-chain resealing."""

    expected = {"schema": SCHEMA + ".external-anchor", "run_id": RUN_ID,
                "package_sha256": package_sha256, "setup_sha256": setup_sha256,
                "review_sha256": review_sha256, "terminal_or_journal_head_sha256": terminal_or_head_sha256}
    require({key: anchor.get(key) for key in expected} == expected, "external anchor binding changed")
    require(anchor.get("published_immutable") is True, "anchor was not externally made immutable")
    signed_by(anchor, "anchor", protocol)


def reject_extra_or_resealed(actual_paths: set[str], sealed_paths: set[str], old_anchor_sha256: str,
                             presented_anchor_sha256: str) -> None:
    """Reject additions and any complete reseal that lacks the old external anchor."""

    require(actual_paths == sealed_paths, "extra or missing evidence object")
    require(presented_anchor_sha256 == old_anchor_sha256,
            "full-chain reseal cannot replace immutable external anchor")
