#!/usr/bin/env python3
"""Pure validators for the static-only Issue #4519 revision 20 package.

This module deliberately has no launcher, filesystem mutation, network client,
Lake, Lean, or build action.  It validates evidence supplied by a separately
authorized executor; this revision itself grants no such authority.
"""

from __future__ import annotations

import base64
import hashlib
import json
from pathlib import Path
from typing import Any

SCHEMA = "ising-model.issue-4519.rev20.static-remediation"
RUN_ID = "20260715T092437Z"
BEFORE = "6a2470114fe0b5dd5c6cdcbb0e02b8acca351fb4"
AFTER = "94ceb4f83906dc23069b7566ce31242240e22855"
ARGV = ["lake", "--no-ansi", "--no-cache", "build", "IsingModel"]
PLAN = ["Bf", "Af", "Ar", "Br", "Bw", "Aw"]
ROLES = ("setup", "review", "run", "anchor")
RAW_NAMES = ("stdout.raw", "stderr.raw", "time-rss.raw", "warnings.raw")
TERMINAL_ALLOWLIST = {"state/terminal-failure.json", "state/terminal-failure.sig"}

# RFC 8032 parameters.  The verifier is intentionally dependency-free so an
# assertion of ``verified: true`` can never substitute for cryptographic proof.
P = 2**255 - 19
L = 2**252 + 27742317777372353535851937790883648493
D = -121665 * pow(121666, P - 2, P) % P
BX = 15112221349535400772501151409588531511454012693041857206046113283949847762202
BY = 46316835694926478169428394003475163141307993866256225615783033603165251855960


class BoundaryError(ValueError):
    """Raised if supplied evidence crosses no sealed protocol boundary."""


def canonical(value: Any) -> bytes:
    """Return the one JSON representation that is hashed and signed."""

    return (json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode()


def digest(value: Any) -> str:
    """Return the SHA-256 digest of canonical evidence."""

    return hashlib.sha256(canonical(value)).hexdigest()


def require(condition: bool, message: str) -> None:
    """Reject invalid evidence at its first broken invariant."""

    if not condition:
        raise BoundaryError(message)


def _point_add(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    x1, y1, x2, y2 = *left, *right
    product = D * x1 * x2 * y1 * y2 % P
    return ((x1 * y2 + y1 * x2) * pow(1 + product, P - 2, P) % P,
            (y1 * y2 + x1 * x2) * pow(1 - product, P - 2, P) % P)


def _scalar_mult(point: tuple[int, int], scalar: int) -> tuple[int, int]:
    result = (0, 1)
    while scalar:
        if scalar & 1:
            result = _point_add(result, point)
        point = _point_add(point, point)
        scalar >>= 1
    return result


def _decode_point(encoded: bytes) -> tuple[int, int]:
    require(len(encoded) == 32, "Ed25519 point length")
    value = int.from_bytes(encoded, "little")
    sign, y = value >> 255, value & ((1 << 255) - 1)
    require(y < P, "Ed25519 non-canonical y")
    x2 = (y * y - 1) * pow(D * y * y + 1, P - 2, P) % P
    x = pow(x2, (P + 3) // 8, P)
    if x * x % P != x2:
        x = x * pow(2, (P - 1) // 4, P) % P
    require(x * x % P == x2 and x != 0, "Ed25519 invalid point")
    if (x & 1) != sign:
        x = P - x
    return x, y


def _spki_raw_public(pem: str) -> bytes:
    lines = [line for line in pem.splitlines() if not line.startswith("---")]
    der = base64.b64decode("".join(lines), validate=True)
    prefix = bytes.fromhex("302a300506032b6570032100")
    require(len(der) == len(prefix) + 32 and der.startswith(prefix), "not an Ed25519 SPKI key")
    return der[len(prefix):]


def verify_ed25519(public_pem: str, message: bytes, signature_b64: str) -> None:
    """Cryptographically verify an RFC 8032 Ed25519 detached signature."""

    try:
        signature = base64.b64decode(signature_b64, validate=True)
    except Exception as exc:
        raise BoundaryError("invalid Ed25519 base64 signature") from exc
    require(len(signature) == 64, "Ed25519 signature length")
    encoded_r, encoded_a = signature[:32], _spki_raw_public(public_pem)
    scalar_s = int.from_bytes(signature[32:], "little")
    require(scalar_s < L, "non-canonical Ed25519 scalar")
    r, a = _decode_point(encoded_r), _decode_point(encoded_a)
    require(_scalar_mult(r, 8) != (0, 1) and _scalar_mult(a, 8) != (0, 1), "small-order Ed25519 point")
    h = int.from_bytes(hashlib.sha512(encoded_r + encoded_a + message).digest(), "little") % L
    require(_scalar_mult((BX, BY), scalar_s) == _point_add(r, _scalar_mult(a, h)), "Ed25519 verification failed")


def _role_key(root: Path, protocol: dict[str, Any], role: str) -> str:
    authority = protocol["authority"][role]
    pem = (root / authority["public_key"]).read_text(encoding="utf-8")
    der_hash = hashlib.sha256(base64.b64decode("".join(line for line in pem.splitlines() if not line.startswith("---")))).hexdigest()
    require(der_hash == authority["spki_sha256"], "public-key fingerprint mismatch: " + role)
    return pem


def verify_signed(root: Path, protocol: dict[str, Any], role: str, record: dict[str, Any], signature: dict[str, Any]) -> str:
    """Verify a detached, role-bound Ed25519 record signature and return its digest."""

    require(signature.get("algorithm") == "Ed25519", "signature algorithm")
    require(signature.get("key_id") == protocol["authority"][role]["key_id"], "signature role/key mismatch")
    require(signature.get("record_sha256") == digest(record), "signature record digest mismatch")
    verify_ed25519(_role_key(root, protocol, role), canonical(record), signature.get("signature_b64", ""))
    return digest(record)


def validate_protocol(root: Path, protocol: dict[str, Any]) -> None:
    """Validate the fixed revision, command, A/B identities, and authority bindings."""

    require(protocol.get("schema") == SCHEMA and protocol.get("revision") == 20 and protocol.get("run_id") == RUN_ID,
            "wrong revision identity")
    require(protocol.get("static_only") is True and protocol.get("before") == BEFORE and protocol.get("after") == AFTER,
            "static A/B identity changed")
    require(protocol.get("command") == ARGV and protocol.get("plan") == PLAN, "exact command or plan changed")
    require(tuple(protocol.get("roles", ())) == ROLES and set(protocol.get("authority", ())) == set(ROLES), "roles changed")
    fingerprints = [protocol["authority"][role].get("spki_sha256") for role in ROLES]
    identifiers = [protocol["authority"][role].get("key_id") for role in ROLES]
    require(len(set(fingerprints)) == len(ROLES) and len(set(identifiers)) == len(ROLES), "roles are not distinct keys")
    for role in ROLES:
        _role_key(root, protocol, role)
    contract = protocol.get("evidence_contract", {})
    require(contract.get("inventory", {}).get("algorithm") == "recursive-lstat-v1", "inventory contract")
    require(contract.get("raw_capture", {}).get("per_action") == list(RAW_NAMES), "raw contract")
    require(contract.get("raw_capture", {}).get("time_command") == ["/usr/bin/time", "-l"], "time/RSS contract")
    require(contract.get("terminal_failure", {}).get("exact_allowlist") == sorted(TERMINAL_ALLOWLIST), "terminal allowlist")


def validate_inventory(inventory: dict[str, dict[str, Any]]) -> None:
    """Validate a complete recursive lstat inventory supplied by an executor."""

    require(type(inventory) is dict and "." in inventory, "inventory root missing")
    for path, facts in inventory.items():
        require(type(path) is str and type(facts) is dict and facts.get("type") in {"file", "directory", "symlink"}, "inventory object")
        require(all(type(facts.get(name)) is int for name in ("mode", "device", "inode")), "inventory lstat facts")
        if facts["type"] == "file":
            require(type(facts.get("size")) is int and len(facts.get("sha256", "")) == 64, "inventory file digest")
        if facts["type"] == "symlink":
            require(type(facts.get("link")) is str, "inventory link text")


def validate_setup(record: dict[str, Any], protocol: dict[str, Any]) -> None:
    """Require fixed detached A/B worktrees and their setup inventories."""

    require(record.get("schema") == SCHEMA + ".setup" and record.get("run_id") == RUN_ID, "setup identity")
    require(record.get("command") == ARGV and record.get("stage") == "setup", "setup command binding")
    worktrees = record.get("worktrees")
    require(type(worktrees) is dict and set(worktrees) == {"A", "B"}, "setup worktrees")
    for label, sha in (("A", BEFORE), ("B", AFTER)):
        item = worktrees[label]
        require(item.get("head") == sha and item.get("detached") is True and item.get("tracked_clean") is True, "fixed dirty worktree")
        require(type(item.get("root")) is dict and all(type(item["root"].get(x)) is int for x in ("device", "inode")), "root inode")
        validate_inventory(item.get("inventory"))
    require(tuple(worktrees["A"]["root"][x] for x in ("device", "inode")) != tuple(worktrees["B"]["root"][x] for x in ("device", "inode")), "A/B inode alias")


def _validate_raw(raw: dict[str, Any], raw_bytes: dict[str, str]) -> None:
    require(type(raw) is dict and set(raw) == set(RAW_NAMES), "raw allowlist")
    for name in RAW_NAMES:
        item = raw[name]
        require(type(item) is dict and type(item.get("path")) is str and item["path"].endswith("/" + name), "raw path")
        encoded = raw_bytes.get(item["path"])
        try:
            payload = base64.b64decode(encoded, validate=True) if type(encoded) is str else None
        except Exception as exc:
            raise BoundaryError("raw content encoding") from exc
        require(type(payload) is bytes and hashlib.sha256(payload).hexdigest() == item.get("sha256"), "raw digest")
    require(type(raw["warnings.raw"].get("warning_count")) is int and raw["warnings.raw"]["warning_count"] >= 0, "warning count")


def validate_review(record: dict[str, Any], package_sha: str, setup_sha: str) -> None:
    """Require review approval to bind exactly the sealed package and setup record."""

    require(record.get("schema") == SCHEMA + ".review" and record.get("run_id") == RUN_ID and record.get("approved") is True, "review state")
    require(record.get("package_manifest_sha256") == package_sha and record.get("setup_sha256") == setup_sha, "review bindings")


def validate_execution_anchor(root: Path, protocol: dict[str, Any], anchor: dict[str, Any], signature: dict[str, Any], package_sha: str, setup_sha: str, review_sha: str, terminal_or_head_sha: str, published_bytes: bytes) -> None:
    """Require an externally published anchor binding every mutable chain head."""

    expected = {"schema": SCHEMA + ".execution-anchor", "run_id": RUN_ID, "package_manifest_sha256": package_sha,
                "setup_sha256": setup_sha, "review_sha256": review_sha, "terminal_or_journal_head_sha256": terminal_or_head_sha}
    require({key: anchor.get(key) for key in expected} == expected, "execution anchor bindings")
    publication = anchor.get("publication", {})
    require(publication.get("kind") == "github-gist-git-commit" and len(publication.get("commit_sha", "")) == 40, "immutable publication receipt")
    payload = {key: value for key, value in anchor.items() if key != "publication"}
    require(hashlib.sha256(published_bytes).hexdigest() == publication.get("published_object_sha256"), "published anchor mismatch")
    require(json.loads(published_bytes.decode()) == payload, "public receipt content mismatch")
    verify_signed(root, protocol, "anchor", anchor, signature)


def validate_root_anchor(root: Path, protocol: dict[str, Any], manifest_sha: str, receipt: dict[str, Any], published_bytes: bytes) -> None:
    """Verify the already-public immutable root receipt, never a local assertion."""

    payload = receipt.get("payload")
    require(type(payload) is dict and payload.get("schema") == SCHEMA + ".root-anchor" and payload.get("run_id") == RUN_ID,
            "root anchor identity")
    require(payload.get("package_manifest_sha256") == manifest_sha, "root anchor package binding")
    require(payload.get("authority_spki_sha256") == {role: protocol["authority"][role]["spki_sha256"] for role in ROLES},
            "root anchor key binding")
    publication = receipt.get("publication", {})
    require(publication.get("kind") == "github-gist-git-commit" and len(publication.get("commit_sha", "")) == 40,
            "root anchor is not externally immutable")
    require(hashlib.sha256(published_bytes).hexdigest() == publication.get("published_object_sha256"), "root public receipt digest")
    require(json.loads(published_bytes.decode()) == payload, "root public receipt content")
    verify_signed(root, protocol, "anchor", payload, receipt.get("signature", {}))


def validate_full_chain(root: Path, protocol: dict[str, Any], package_sha: str, setup: tuple[dict[str, Any], dict[str, Any]], review: tuple[dict[str, Any], dict[str, Any]], journal: list[tuple[dict[str, Any], dict[str, Any]]], terminal: tuple[dict[str, Any], dict[str, Any]] | None, anchor: tuple[dict[str, Any], dict[str, Any], bytes]) -> None:
    """Validate setup → review → exact action state-machine → terminal/head → anchor."""

    validate_protocol(root, protocol)
    setup_record, setup_signature = setup
    validate_setup(setup_record, protocol)
    setup_sha = verify_signed(root, protocol, "setup", setup_record, setup_signature)
    review_record, review_signature = review
    validate_review(review_record, package_sha, setup_sha)
    review_sha = verify_signed(root, protocol, "review", review_record, review_signature)
    require(len(journal) <= len(PLAN), "journal retry")
    previous = review_sha
    for index, (action, signature) in enumerate(journal):
        require(action.get("schema") == SCHEMA + ".action" and action.get("run_id") == RUN_ID, "action identity")
        require(action.get("index") == index and action.get("action") == PLAN[index] and action.get("argv") == ARGV, "action state-machine")
        require(action.get("prior_sha256") == previous and action.get("returncode") == 0, "action chain or nonterminal failure")
        validate_inventory(action.get("before_inventory")); validate_inventory(action.get("after_inventory"))
        _validate_raw(action.get("raw"), action.get("raw_bytes", {}))
        previous = verify_signed(root, protocol, "run", action, signature)
    if terminal is not None:
        failure, signature = terminal
        require(failure.get("schema") == SCHEMA + ".terminal-failure" and failure.get("run_id") == RUN_ID, "terminal identity")
        require(failure.get("index") == len(journal) and failure.get("action") == PLAN[len(journal)] and failure.get("argv") == ARGV, "terminal state-machine")
        require(failure.get("prior_sha256") == previous and type(failure.get("returncode")) is int and failure["returncode"] != 0, "terminal failure")
        require(set(failure.get("state_files", ())) == TERMINAL_ALLOWLIST, "terminal exact allowlist")
        validate_inventory(failure.get("execution_inventory")); _validate_raw(failure.get("raw"), failure.get("raw_bytes", {}))
        previous = verify_signed(root, protocol, "run", failure, signature)
    else:
        require(len(journal) == len(PLAN), "incomplete run without terminal")
    anchor_record, anchor_signature, published_bytes = anchor
    validate_execution_anchor(root, protocol, anchor_record, anchor_signature, package_sha, setup_sha, review_sha, previous, published_bytes)


def reject_reseal_without_anchor(old_anchor: dict[str, Any], package_sha: str, setup_sha: str, review_sha: str, terminal_or_head_sha: str) -> None:
    """Reject package, review, terminal, or journal substitution without replacing the external anchor."""

    require(old_anchor.get("package_manifest_sha256") == package_sha and old_anchor.get("setup_sha256") == setup_sha and old_anchor.get("review_sha256") == review_sha and old_anchor.get("terminal_or_journal_head_sha256") == terminal_or_head_sha, "reseal disagrees with immutable anchor")
