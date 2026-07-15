#!/usr/bin/env python3
"""Static validators for the Issue #4519 revision 21 evidence package.

No function in this module launches Lean, Lake, a build, a measurement, or an
executor.  ``validate_full_chain`` only verifies evidence created under a
separately authorized future run.
"""

from __future__ import annotations

import base64
import hashlib
import json
from pathlib import Path
from typing import Any
from urllib.request import urlopen

SCHEMA = "ising-model.issue-4519.rev21.static-remediation"
RUN_ID = "20260715T102437Z"
BEFORE = "6a2470114fe0b5dd5c6cdcbb0e02b8acca351fb4"
AFTER = "94ceb4f83906dc23069b7566ce31242240e22855"
ARGV = ["lake", "--no-ansi", "--no-cache", "build", "IsingModel"]
PLAN = ["Bf", "Af", "Ar", "Br", "Bw", "Aw"]
ROLES = ("setup", "review", "run", "anchor")
RAW_NAMES = ("stdout.raw", "stderr.raw", "time-rss.raw", "warnings.raw")
TERMINAL_ALLOWLIST = ("state/terminal-failure.json", "state/terminal-failure.sig")

# These three values are patched only after the public gist has its immutable
# commit.  They are deliberately module constants rather than caller inputs.
ROOT_ANCHOR_RAW_URL = "https://gist.githubusercontent.com/phasetr/250f21c2afd75c33350e45aedf18f6d1/raw/58a3a70a4b0efcdcded287fa97f577b731520828/issue4519-rev21-root-anchor.json"
ROOT_ANCHOR_COMMIT_SHA = "58a3a70a4b0efcdcded287fa97f577b731520828"
ROOT_ANCHOR_BYTES_SHA256 = "4a7fdead9184bdd5dc56e7dd0b160f4f0eca076e7efe94793dda1413029a40f6"

P = 2**255 - 19
L = 2**252 + 27742317777372353535851937790883648493
D = -121665 * pow(121666, P - 2, P) % P
BX = 15112221349535400772501151409588531511454012693041857206046113283949847762202
BY = 46316835694926478169428394003475163141307993866256225615783033603165251855960


class BoundaryError(ValueError):
    """Raised when a claimed sealed evidence boundary is invalid."""


def canonical(value: Any) -> bytes:
    """Return the canonical JSON bytes used by all digests and signatures."""

    return (json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode()


def digest(value: Any) -> str:
    """Return a SHA-256 digest of canonical JSON evidence."""

    return hashlib.sha256(canonical(value)).hexdigest()


def require(condition: bool, message: str) -> None:
    """Stop at the first broken protocol boundary."""

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
    """Cryptographically verify one RFC 8032 Ed25519 detached signature."""

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
    der = base64.b64decode("".join(line for line in pem.splitlines() if not line.startswith("---")))
    require(hashlib.sha256(der).hexdigest() == authority["spki_sha256"], "public-key fingerprint mismatch: " + role)
    return pem


def verify_signed(root: Path, protocol: dict[str, Any], role: str, record: dict[str, Any], signature: dict[str, Any]) -> str:
    """Verify a role-bound signature and return the signed record digest."""

    require(signature.get("algorithm") == "Ed25519", "signature algorithm")
    require(signature.get("key_id") == protocol["authority"][role]["key_id"], "signature role/key mismatch")
    require(signature.get("record_sha256") == digest(record), "signature record digest mismatch")
    verify_ed25519(_role_key(root, protocol, role), canonical(record), signature.get("signature_b64", ""))
    return digest(record)


def validate_protocol(root: Path, protocol: dict[str, Any]) -> None:
    """Validate fixed identity, A/B assignments, authority, and evidence schema."""

    require(protocol.get("schema") == SCHEMA and protocol.get("revision") == 21 and protocol.get("run_id") == RUN_ID,
            "wrong revision identity")
    require(protocol.get("static_only") is True and protocol.get("before") == BEFORE and protocol.get("after") == AFTER,
            "fixed before/after identity changed")
    require(protocol.get("command") == ARGV and protocol.get("plan") == PLAN, "exact command or plan changed")
    require(protocol.get("worktrees") == {"A": AFTER, "B": BEFORE}, "fixed A/B identity changed")
    require(tuple(protocol.get("roles", ())) == ROLES and set(protocol.get("authority", ())) == set(ROLES), "roles changed")
    fingerprints = [protocol["authority"][role].get("spki_sha256") for role in ROLES]
    identifiers = [protocol["authority"][role].get("key_id") for role in ROLES]
    require(len(set(fingerprints)) == len(ROLES) and len(set(identifiers)) == len(ROLES), "roles are not distinct keys")
    for role in ROLES:
        _role_key(root, protocol, role)
    contract = protocol.get("evidence_contract", {})
    require(contract.get("inventory", {}).get("algorithm") == "recursive-lstat-v1", "inventory contract")
    require(contract.get("raw_capture", {}).get("per_action") == list(RAW_NAMES), "raw capture contract")
    require(contract.get("terminal_failure", {}).get("exact_allowlist") == list(TERMINAL_ALLOWLIST), "terminal allowlist")
    require(ROOT_ANCHOR_RAW_URL.startswith("https://gist.githubusercontent.com/") and len(ROOT_ANCHOR_COMMIT_SHA) == 40,
            "root anchor not fixed")


def validate_package_manifest(root: Path) -> str:
    """Verify the immutable package manifest against every in-scope package file."""

    manifest = json.loads((root / "package-manifest.json").read_text(encoding="utf-8"))
    require(manifest.get("schema") == SCHEMA + ".package-manifest" and manifest.get("run_id") == RUN_ID, "manifest identity")
    files = manifest.get("files")
    excludes = set(manifest.get("manifest_excludes", ()))
    require(type(files) is dict and excludes == {"harness.py", "package-manifest.json", "raw/**", "state/**"}, "manifest scope")
    actual = {path.relative_to(root).as_posix() for path in root.rglob("*") if path.is_file()}
    static_actual = {path for path in actual if not path.startswith(("raw/", "state/"))}
    require(set(files) == static_actual - {"harness.py", "package-manifest.json"}, "manifest file set")
    for relative, expected in files.items():
        require(type(relative) is str and len(expected) == 64, "manifest entry")
        require(hashlib.sha256((root / relative).read_bytes()).hexdigest() == expected, "manifest file digest: " + relative)
    return digest(manifest)


def validate_inventory(inventory: dict[str, dict[str, Any]]) -> None:
    """Validate a recursive lstat inventory, including files, directories, and links."""

    require(type(inventory) is dict and "." in inventory, "inventory root missing")
    for path, facts in inventory.items():
        require(type(path) is str and type(facts) is dict and facts.get("type") in {"file", "directory", "symlink"}, "inventory object")
        require(all(type(facts.get(name)) is int for name in ("mode", "device", "inode")), "inventory lstat facts")
        if facts["type"] == "file":
            require(type(facts.get("size")) is int and len(facts.get("sha256", "")) == 64, "inventory file digest")
        if facts["type"] == "symlink":
            require(type(facts.get("link")) is str, "inventory link text")


def _read_raw(root: Path, action_id: str, raw: dict[str, Any]) -> None:
    require(type(raw) is dict and set(raw) == set(RAW_NAMES), "raw allowlist")
    for name in RAW_NAMES:
        item = raw[name]
        expected = f"raw/{action_id}/{name}"
        require(type(item) is dict and item.get("path") == expected and item.get("action_id") == action_id, "action-specific raw path")
        path = root / expected
        require(path.is_file(), "raw evidence missing: " + expected)
        payload = path.read_bytes()
        require(hashlib.sha256(payload).hexdigest() == item.get("sha256"), "raw digest: " + expected)
        if name == "warnings.raw":
            derived = sum("warning:" in line.lower() for line in payload.decode("utf-8", "strict").splitlines())
            require(item.get("warning_count") == derived, "warning count is not derived from warnings.raw")


def validate_setup(record: dict[str, Any], protocol: dict[str, Any]) -> None:
    """Require detached, clean, inode-disjoint exact A/B setup inventories."""

    require(record.get("schema") == SCHEMA + ".setup" and record.get("run_id") == RUN_ID and record.get("stage") == "setup", "setup identity")
    require(record.get("command") == ARGV and set(record.get("worktrees", ())) == {"A", "B"}, "setup binding")
    for label, expected_sha in protocol["worktrees"].items():
        item = record["worktrees"][label]
        require(item.get("head") == expected_sha and item.get("detached") is True and item.get("tracked_clean") is True, "fixed worktree")
        require(type(item.get("root")) is dict and all(type(item["root"].get(x)) is int for x in ("device", "inode")), "worktree inode")
        validate_inventory(item.get("inventory"))
    left, right = record["worktrees"]["A"]["root"], record["worktrees"]["B"]["root"]
    require((left["device"], left["inode"]) != (right["device"], right["inode"]), "A/B inode alias")
    validate_inventory(record.get("execution_inventory"))


def validate_external_root_anchor(root: Path, protocol: dict[str, Any], manifest_sha: str) -> str:
    """Fetch and verify fixed external root-anchor bytes; caller bytes are impossible."""

    try:
        with urlopen(ROOT_ANCHOR_RAW_URL, timeout=15) as response:
            published = response.read()
    except Exception as exc:
        raise BoundaryError("fixed external root anchor unavailable") from exc
    require(hashlib.sha256(published).hexdigest() == ROOT_ANCHOR_BYTES_SHA256, "external root anchor bytes changed")
    try:
        receipt = json.loads(published.decode("utf-8"))
    except Exception as exc:
        raise BoundaryError("external root anchor JSON") from exc
    payload = receipt.get("payload")
    require(type(payload) is dict and payload == {
        "schema": SCHEMA + ".root-anchor", "run_id": RUN_ID,
        "package_manifest_sha256": manifest_sha,
        "authority_spki_sha256": {role: protocol["authority"][role]["spki_sha256"] for role in ROLES},
    }, "external root anchor bindings")
    verify_signed(root, protocol, "anchor", payload, receipt.get("signature", {}))
    return digest(payload)


def validate_review(record: dict[str, Any], manifest_sha: str, root_anchor_sha: str, setup_sha: str) -> None:
    """Require review to bind package, externally rooted authority, and setup."""

    require(record.get("schema") == SCHEMA + ".review" and record.get("run_id") == RUN_ID and record.get("approved") is True, "review state")
    require(record.get("package_manifest_sha256") == manifest_sha and record.get("root_anchor_sha256") == root_anchor_sha and record.get("setup_sha256") == setup_sha,
            "review bindings")


def validate_execution_anchor(root: Path, protocol: dict[str, Any], anchor: dict[str, Any], signature: dict[str, Any], manifest_sha: str, root_anchor_sha: str, setup_sha: str, review_sha: str, terminal_or_head_sha: str, published_bytes: bytes) -> None:
    """Require a signed execution anchor that binds every completed chain head."""

    expected = {"schema": SCHEMA + ".execution-anchor", "run_id": RUN_ID, "package_manifest_sha256": manifest_sha,
                "root_anchor_sha256": root_anchor_sha, "setup_sha256": setup_sha, "review_sha256": review_sha,
                "terminal_or_journal_head_sha256": terminal_or_head_sha}
    require({key: anchor.get(key) for key in expected} == expected, "execution anchor bindings")
    publication = anchor.get("publication", {})
    require(publication.get("kind") == "github-gist-git-commit" and len(publication.get("commit_sha", "")) == 40, "execution anchor publication")
    content = {key: value for key, value in anchor.items() if key != "publication"}
    require(hashlib.sha256(published_bytes).hexdigest() == publication.get("published_object_sha256") and json.loads(published_bytes.decode()) == content,
            "execution anchor public bytes")
    verify_signed(root, protocol, "anchor", anchor, signature)


def validate_terminal_state_files(root: Path, inventory: dict[str, dict[str, Any]]) -> None:
    """Require the terminal record's allowlist to describe real, exact state files."""

    state_root = root / "state"
    require(state_root.is_dir() and not state_root.is_symlink(), "terminal state directory missing")
    actual = {path.relative_to(root).as_posix() for path in state_root.rglob("*") if path.is_file() and not path.is_symlink()}
    require(tuple(sorted(actual)) == TERMINAL_ALLOWLIST, "terminal actual state files")
    for relative in TERMINAL_ALLOWLIST:
        facts = inventory[relative]
        payload = (root / relative).read_bytes()
        require(facts.get("type") == "file" and facts.get("size") == len(payload) and facts.get("sha256") == hashlib.sha256(payload).hexdigest(),
                "terminal state inventory does not describe disk")


def validate_full_chain(root: Path, protocol: dict[str, Any], setup: tuple[dict[str, Any], dict[str, Any]], review: tuple[dict[str, Any], dict[str, Any]], journal: list[tuple[dict[str, Any], dict[str, Any]]], terminal: tuple[dict[str, Any], dict[str, Any]] | None, execution_anchor: tuple[dict[str, Any], dict[str, Any], bytes]) -> None:
    """Validate root-anchor → setup → review → actions/terminal → execution-anchor."""

    validate_protocol(root, protocol)
    manifest_sha = validate_package_manifest(root)
    root_anchor_sha = validate_external_root_anchor(root, protocol, manifest_sha)
    setup_record, setup_signature = setup
    validate_setup(setup_record, protocol)
    setup_sha = verify_signed(root, protocol, "setup", setup_record, setup_signature)
    review_record, review_signature = review
    validate_review(review_record, manifest_sha, root_anchor_sha, setup_sha)
    review_sha = verify_signed(root, protocol, "review", review_record, review_signature)
    require(len(journal) <= len(PLAN), "journal retry")
    previous_record_sha, previous_inventory_sha = review_sha, digest(setup_record["execution_inventory"])
    for index, (action, signature) in enumerate(journal):
        action_id = f"{PLAN[index]}-{index:03d}"
        require(action.get("schema") == SCHEMA + ".action" and action.get("run_id") == RUN_ID and action.get("index") == index, "action identity")
        require(action.get("action") == PLAN[index] and action.get("action_id") == action_id and action.get("worktree") == PLAN[index][0], "action identity/worktree")
        require(action.get("worktree_head") == protocol["worktrees"][PLAN[index][0]] and action.get("argv") == ARGV, "action A/B or argv binding")
        require(action.get("prior_sha256") == previous_record_sha and action.get("returncode") == 0, "action chain")
        validate_inventory(action.get("before_inventory")); validate_inventory(action.get("after_inventory"))
        require(action.get("before_inventory_sha256") == previous_inventory_sha and digest(action["before_inventory"]) == previous_inventory_sha,
                "inventory continuity")
        _read_raw(root, action_id, action.get("raw"))
        previous_record_sha, previous_inventory_sha = verify_signed(root, protocol, "run", action, signature), digest(action["after_inventory"])
    if terminal is not None:
        failure, signature = terminal
        require(len(journal) < len(PLAN), "terminal after completed run")
        index, action_name = len(journal), PLAN[len(journal)]
        action_id = f"{action_name}-{index:03d}"
        require(failure.get("schema") == SCHEMA + ".terminal-failure" and failure.get("run_id") == RUN_ID and failure.get("index") == index,
                "terminal identity")
        require(failure.get("action") == action_name and failure.get("action_id") == action_id and failure.get("worktree") == action_name[0], "terminal action identity")
        require(failure.get("worktree_head") == protocol["worktrees"][action_name[0]] and failure.get("argv") == ARGV, "terminal A/B or argv")
        require(failure.get("prior_sha256") == previous_record_sha and type(failure.get("returncode")) is int and failure["returncode"] != 0, "terminal chain")
        validate_inventory(failure.get("before_inventory")); validate_inventory(failure.get("after_inventory")); validate_inventory(failure.get("terminal_state_inventory"))
        require(failure.get("before_inventory_sha256") == previous_inventory_sha and digest(failure["before_inventory"]) == previous_inventory_sha,
                "terminal inventory continuity")
        require(tuple(sorted(set(failure["terminal_state_inventory"]) - {"."})) == TERMINAL_ALLOWLIST and tuple(failure.get("state_files", ())) == TERMINAL_ALLOWLIST,
                "terminal actual state allowlist")
        validate_terminal_state_files(root, failure["terminal_state_inventory"])
        _read_raw(root, action_id, failure.get("raw"))
        previous_record_sha = verify_signed(root, protocol, "run", failure, signature)
    else:
        require(len(journal) == len(PLAN), "incomplete run without terminal")
    anchor_record, anchor_signature, published_bytes = execution_anchor
    validate_execution_anchor(root, protocol, anchor_record, anchor_signature, manifest_sha, root_anchor_sha, setup_sha, review_sha, previous_record_sha, published_bytes)
