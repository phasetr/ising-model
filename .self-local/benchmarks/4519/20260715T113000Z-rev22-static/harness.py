#!/usr/bin/env python3
"""Static-only validators for Issue #4519 revision 22 evidence."""

from __future__ import annotations

import base64
import hashlib
import json
import os
import stat
from pathlib import Path
from typing import Any
from urllib.request import urlopen

SCHEMA = "ising-model.issue-4519.rev22.static-remediation"
RUN_ID = "20260715T113000Z"
BEFORE = "6a2470114fe0b5dd5c6cdcbb0e02b8acca351fb4"
AFTER = "94ceb4f83906dc23069b7566ce31242240e22855"
ARGV = ["lake", "--no-ansi", "--no-cache", "build", "IsingModel"]
PLAN = ("Bf", "Af", "Ar", "Br", "Bw", "Aw")
ROLES = ("setup", "review", "run", "anchor")
RAW_NAMES = ("stdout.raw", "stderr.raw", "time-rss.raw", "warnings.raw")
TERMINAL_OBJECTS = ("state", "state/terminal-failure.json", "state/terminal-failure.sig")
ROOT_ANCHOR_GIST = "250f21c2afd75c33350e45aedf18f6d1"
ROOT_ANCHOR_FILE = "issue4519-rev22-root-anchor.json"
ROOT_ANCHOR_RAW_URL = f"https://gist.githubusercontent.com/phasetr/{ROOT_ANCHOR_GIST}/raw/{ROOT_ANCHOR_FILE}"
ROOT_ANCHOR_API_URL = f"https://api.github.com/gists/{ROOT_ANCHOR_GIST}"

P = 2**255 - 19
L = 2**252 + 27742317777372353535851937790883648493
D = -121665 * pow(121666, P - 2, P) % P
BX = 15112221349535400772501151409588531511454012693041857206046113283949847762202
BY = 46316835694926478169428394003475163141307993866256225615783033603165251855960


class BoundaryError(ValueError):
    """Raised when an evidence boundary is invalid."""


def canonical(value: Any) -> bytes:
    """Encode the one JSON representation used for records and signatures."""

    return (json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode()


def digest(value: Any) -> str:
    """Return the SHA-256 of canonical JSON."""

    return hashlib.sha256(canonical(value)).hexdigest()


def require(condition: bool, message: str) -> None:
    """Reject the first invalid protocol condition."""

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


def _public_raw(pem: str) -> bytes:
    der = base64.b64decode("".join(line for line in pem.splitlines() if not line.startswith("---")), validate=True)
    prefix = bytes.fromhex("302a300506032b6570032100")
    require(len(der) == len(prefix) + 32 and der.startswith(prefix), "not an Ed25519 SPKI key")
    return der[len(prefix):]


def verify_ed25519(public_pem: str, message: bytes, signature_b64: str) -> None:
    """Verify one detached RFC 8032 Ed25519 signature without a verifier mock."""

    try:
        signature = base64.b64decode(signature_b64, validate=True)
    except Exception as exc:
        raise BoundaryError("invalid Ed25519 base64") from exc
    require(len(signature) == 64, "Ed25519 signature length")
    encoded_r, encoded_a = signature[:32], _public_raw(public_pem)
    scalar_s = int.from_bytes(signature[32:], "little")
    require(scalar_s < L, "non-canonical Ed25519 scalar")
    r, a = _decode_point(encoded_r), _decode_point(encoded_a)
    require(_scalar_mult(r, 8) != (0, 1) and _scalar_mult(a, 8) != (0, 1), "small-order Ed25519 point")
    challenge = int.from_bytes(hashlib.sha512(encoded_r + encoded_a + message).digest(), "little") % L
    require(_scalar_mult((BX, BY), scalar_s) == _point_add(r, _scalar_mult(a, challenge)), "Ed25519 verification failed")


def _role_key(root: Path, protocol: dict[str, Any], role: str) -> str:
    authority = protocol["authority"][role]
    pem = (root / authority["public_key"]).read_text(encoding="utf-8")
    der = base64.b64decode("".join(line for line in pem.splitlines() if not line.startswith("---")), validate=True)
    require(hashlib.sha256(der).hexdigest() == authority["spki_sha256"], "public key fingerprint: " + role)
    return pem


def verify_signed(root: Path, protocol: dict[str, Any], role: str, record: dict[str, Any], signature: dict[str, Any]) -> str:
    """Verify a distinct role key and return its signed record digest."""

    require(signature.get("algorithm") == "Ed25519", "signature algorithm")
    require(signature.get("key_id") == protocol["authority"][role]["key_id"], "signature role/key")
    require(signature.get("record_sha256") == digest(record), "signature digest")
    verify_ed25519(_role_key(root, protocol, role), canonical(record), signature.get("signature_b64", ""))
    return digest(record)


def validate_protocol(root: Path, protocol: dict[str, Any]) -> None:
    """Validate immutable revision identity, exact command, and distinct authority."""

    require(protocol.get("schema") == SCHEMA and protocol.get("revision") == 22 and protocol.get("run_id") == RUN_ID, "protocol identity")
    require(protocol.get("static_only") is True and protocol.get("before") == BEFORE and protocol.get("after") == AFTER, "fixed commits")
    require(protocol.get("command") == ARGV and tuple(protocol.get("plan", ())) == PLAN, "command or plan")
    require(protocol.get("worktrees") == {"A": AFTER, "B": BEFORE}, "A/B binding")
    require(tuple(protocol.get("roles", ())) == ROLES and set(protocol.get("authority", ())) == set(ROLES), "authority roles")
    fingerprints = [protocol["authority"][role].get("spki_sha256") for role in ROLES]
    require(len(set(fingerprints)) == len(ROLES), "authority keys are not distinct")
    for role in ROLES:
        _role_key(root, protocol, role)
    contract = protocol.get("evidence_contract", {})
    require(contract.get("inventory", {}).get("algorithm") == "recursive-lstat-v2", "inventory contract")
    require(contract.get("raw_capture", {}).get("per_action") == list(RAW_NAMES), "raw contract")
    require(contract.get("terminal_failure", {}).get("filesystem_object_allowlist") == list(TERMINAL_OBJECTS), "terminal contract")


def validate_package_manifest(root: Path) -> str:
    """Validate the independent canonical manifest, including the validator itself."""

    manifest = json.loads((root / "package-manifest.json").read_text(encoding="utf-8"))
    require(manifest.get("schema") == SCHEMA + ".package-manifest" and manifest.get("run_id") == RUN_ID, "manifest identity")
    files, excludes = manifest.get("files"), set(manifest.get("manifest_excludes", ()))
    require(type(files) is dict and excludes == {"package-manifest.json", "raw/**", "state/**"}, "manifest exclusions")
    actual = {path.relative_to(root).as_posix() for path in root.rglob("*") if path.is_file()}
    static_actual = {name for name in actual if not name.startswith(("raw/", "state/"))}
    require(set(files) == static_actual - {"package-manifest.json"}, "manifest exact static file set")
    require("harness.py" in files, "harness is not manifest-bound")
    for relative, expected in files.items():
        require(type(relative) is str and type(expected) is str and len(expected) == 64, "manifest entry")
        require(hashlib.sha256((root / relative).read_bytes()).hexdigest() == expected, "manifest digest: " + relative)
    return digest(manifest)


def _facts(path: Path) -> dict[str, Any]:
    status = path.lstat()
    if stat.S_ISREG(status.st_mode):
        kind, extra = "file", {"size": status.st_size, "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
    elif stat.S_ISDIR(status.st_mode):
        kind, extra = "directory", {}
    elif stat.S_ISLNK(status.st_mode):
        kind, extra = "symlink", {"link": os.readlink(path)}
    else:
        kind, extra = "other", {}
    return {"type": kind, "mode": stat.S_IMODE(status.st_mode), "device": status.st_dev, "inode": status.st_ino, **extra}


def _terminal_disk_objects(root: Path) -> dict[str, dict[str, Any]]:
    state = root / "state"
    require(state.exists() and not state.is_symlink() and state.is_dir(), "terminal state directory")
    result = {"state": _facts(state)}
    for path in state.rglob("*"):
        result[path.relative_to(root).as_posix()] = _facts(path)
    return result


def validate_terminal_state_files(root: Path, inventory: dict[str, dict[str, Any]]) -> None:
    """Require exact recursive terminal objects, including directories and symlinks."""

    require(type(inventory) is dict and tuple(sorted(inventory)) == TERMINAL_OBJECTS, "terminal inventory allowlist")
    actual = _terminal_disk_objects(root)
    require(tuple(sorted(actual)) == TERMINAL_OBJECTS, "terminal disk object allowlist")
    for relative in TERMINAL_OBJECTS:
        require(inventory[relative] == actual[relative], "terminal lstat object mismatch: " + relative)


def validate_inventory(inventory: dict[str, dict[str, Any]]) -> None:
    """Validate a recursively represented lstat inventory record."""

    require(type(inventory) is dict and "." in inventory, "inventory root")
    for relative, facts in inventory.items():
        require(type(relative) is str and type(facts) is dict and facts.get("type") in {"file", "directory", "symlink"}, "inventory object")
        require(all(type(facts.get(key)) is int for key in ("mode", "device", "inode")), "inventory lstat facts")
        if facts["type"] == "file":
            require(type(facts.get("size")) is int and len(facts.get("sha256", "")) == 64, "inventory file")
        if facts["type"] == "symlink":
            require(type(facts.get("link")) is str, "inventory symlink")


def _read_raw(root: Path, action_id: str, raw: dict[str, Any]) -> None:
    require(type(raw) is dict and set(raw) == set(RAW_NAMES), "raw allowlist")
    for name in RAW_NAMES:
        item, expected = raw[name], f"raw/{action_id}/{name}"
        require(type(item) is dict and item.get("action_id") == action_id and item.get("path") == expected, "raw action binding")
        path = root / expected
        require(path.is_file() and not path.is_symlink(), "raw disk object")
        payload = path.read_bytes()
        require(item.get("sha256") == hashlib.sha256(payload).hexdigest(), "raw digest")
        if name == "warnings.raw":
            derived = sum("warning:" in line.lower() for line in payload.decode("utf-8", "strict").splitlines())
            require(item.get("warning_count") == derived, "derived warning count")


def validate_setup(record: dict[str, Any], protocol: dict[str, Any]) -> None:
    """Require exact detached, clean, inode-disjoint A/B setup facts."""

    require(record.get("schema") == SCHEMA + ".setup" and record.get("run_id") == RUN_ID and record.get("stage") == "setup", "setup identity")
    require(record.get("command") == ARGV and set(record.get("worktrees", ())) == {"A", "B"}, "setup command/A-B")
    for label, expected in protocol["worktrees"].items():
        item = record["worktrees"][label]
        require(item.get("head") == expected and item.get("detached") is True and item.get("tracked_clean") is True, "worktree identity")
        require(type(item.get("root")) is dict and all(type(item["root"].get(k)) is int for k in ("device", "inode")), "worktree root")
        validate_inventory(item.get("inventory"))
    left, right = record["worktrees"]["A"]["root"], record["worktrees"]["B"]["root"]
    require((left["device"], left["inode"]) != (right["device"], right["inode"]), "A/B inode alias")
    validate_inventory(record.get("execution_inventory"))


def _fetch(url: str) -> bytes:
    try:
        with urlopen(url, timeout=20) as response:
            return response.read()
    except Exception as exc:
        raise BoundaryError("external anchor unavailable") from exc


def validate_external_root_anchor(root: Path, protocol: dict[str, Any], manifest_sha: str) -> str:
    """Fetch a fixed raw URL and prove its bytes belong to one immutable Gist commit."""

    raw = _fetch(ROOT_ANCHOR_RAW_URL)
    try:
        receipt = json.loads(raw.decode("utf-8"))
        overview = json.loads(_fetch(ROOT_ANCHOR_API_URL).decode("utf-8"))
    except Exception as exc:
        raise BoundaryError("external root anchor JSON") from exc
    matching_commit = None
    for history in overview.get("history", []):
        version = history.get("version")
        if type(version) is not str or len(version) != 40:
            continue
        try:
            revision = json.loads(_fetch(f"{ROOT_ANCHOR_API_URL}/{version}").decode("utf-8"))
            content = revision["files"][ROOT_ANCHOR_FILE]["content"].encode("utf-8")
        except Exception:
            continue
        if content == raw:
            matching_commit = version
            break
    require(matching_commit is not None, "raw anchor not pinned to immutable gist commit")
    payload = receipt.get("payload")
    expected = {"schema": SCHEMA + ".root-anchor", "run_id": RUN_ID, "package_manifest_sha256": manifest_sha,
                "harness_sha256": hashlib.sha256((root / "harness.py").read_bytes()).hexdigest(),
                "authority_spki_sha256": {role: protocol["authority"][role]["spki_sha256"] for role in ROLES}}
    require(payload == expected, "root anchor package/harness bindings")
    verify_signed(root, protocol, "anchor", payload, receipt.get("signature", {}))
    return digest({"payload": payload, "gist_commit_sha": matching_commit})


def validate_review(record: dict[str, Any], manifest_sha: str, root_anchor_sha: str, setup_sha: str) -> None:
    """Require review to bind the rooted package and setup values."""

    require(record == {"schema": SCHEMA + ".review", "run_id": RUN_ID, "approved": True,
                       "package_manifest_sha256": manifest_sha, "root_anchor_sha256": root_anchor_sha,
                       "setup_sha256": setup_sha}, "review bindings")


def validate_execution_anchor(root: Path, protocol: dict[str, Any], anchor: dict[str, Any], signature: dict[str, Any], manifest_sha: str, root_anchor_sha: str, setup_sha: str, review_sha: str, head_sha: str, published: bytes) -> None:
    """Require an anchor over the full completed chain head and exact public bytes."""

    expected = {"schema": SCHEMA + ".execution-anchor", "run_id": RUN_ID, "package_manifest_sha256": manifest_sha,
                "root_anchor_sha256": root_anchor_sha, "setup_sha256": setup_sha, "review_sha256": review_sha,
                "terminal_or_journal_head_sha256": head_sha}
    require({key: anchor.get(key) for key in expected} == expected, "execution anchor bindings")
    publication = anchor.get("publication", {})
    require(publication.get("kind") == "github-gist-git-commit" and len(publication.get("commit_sha", "")) == 40, "execution publication")
    contents = {key: value for key, value in anchor.items() if key != "publication"}
    require(json.loads(published.decode("utf-8")) == contents and hashlib.sha256(published).hexdigest() == publication.get("published_object_sha256"), "execution public bytes")
    verify_signed(root, protocol, "anchor", anchor, signature)


def validate_full_chain(root: Path, protocol: dict[str, Any], setup: tuple[dict[str, Any], dict[str, Any]], review: tuple[dict[str, Any], dict[str, Any]], journal: list[tuple[dict[str, Any], dict[str, Any]]], terminal: tuple[dict[str, Any], dict[str, Any]] | None, execution_anchor: tuple[dict[str, Any], dict[str, Any], bytes]) -> None:
    """Validate root-anchor → setup → review → actions/terminal → execution anchor."""

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
    previous_record, previous_inventory = review_sha, digest(setup_record["execution_inventory"])
    for index, (action, signature) in enumerate(journal):
        name, action_id = PLAN[index], f"{PLAN[index]}-{index:03d}"
        require(action.get("schema") == SCHEMA + ".action" and action.get("run_id") == RUN_ID and action.get("index") == index, "action identity")
        require(action.get("action") == name and action.get("action_id") == action_id and action.get("worktree") == name[0], "action A/B")
        require(action.get("worktree_head") == protocol["worktrees"][name[0]] and action.get("argv") == ARGV and action.get("returncode") == 0, "action command")
        validate_inventory(action.get("before_inventory")); validate_inventory(action.get("after_inventory"))
        require(action.get("prior_sha256") == previous_record and action.get("before_inventory_sha256") == previous_inventory and digest(action["before_inventory"]) == previous_inventory, "action continuity")
        _read_raw(root, action_id, action.get("raw"))
        previous_record, previous_inventory = verify_signed(root, protocol, "run", action, signature), digest(action["after_inventory"])
    if terminal is None:
        require(len(journal) == len(PLAN), "incomplete chain")
    else:
        failure, signature = terminal
        require(len(journal) < len(PLAN), "terminal after completion")
        index, name, action_id = len(journal), PLAN[len(journal)], f"{PLAN[len(journal)]}-{len(journal):03d}"
        require(failure.get("schema") == SCHEMA + ".terminal-failure" and failure.get("run_id") == RUN_ID and failure.get("index") == index, "terminal identity")
        require(failure.get("action") == name and failure.get("action_id") == action_id and failure.get("worktree") == name[0] and failure.get("worktree_head") == protocol["worktrees"][name[0]], "terminal A/B")
        require(failure.get("argv") == ARGV and type(failure.get("returncode")) is int and failure["returncode"] != 0 and failure.get("prior_sha256") == previous_record, "terminal command/chain")
        validate_inventory(failure.get("before_inventory")); validate_inventory(failure.get("after_inventory"))
        require(failure.get("before_inventory_sha256") == previous_inventory and digest(failure["before_inventory"]) == previous_inventory, "terminal continuity")
        validate_terminal_state_files(root, failure.get("terminal_state_inventory"))
        _read_raw(root, action_id, failure.get("raw"))
        previous_record = verify_signed(root, protocol, "run", failure, signature)
    anchor, signature, published = execution_anchor
    validate_execution_anchor(root, protocol, anchor, signature, manifest_sha, root_anchor_sha, setup_sha, review_sha, previous_record, published)
