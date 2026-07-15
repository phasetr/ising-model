#!/usr/bin/env python3
"""Disk-first primitives for the isolated Issue #4519 revision-18 protocol."""

from __future__ import annotations

import hashlib
import json
import os
import stat
import subprocess
from pathlib import Path
from typing import Any


class Stop(RuntimeError):
    """Raised when sealed evidence or authority is not admissible."""


def canonical(value: Any) -> bytes:
    """Return the one JSON representation accepted for protocol evidence."""

    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True) + "\n").encode("utf-8")


def sha_bytes(data: bytes) -> str:
    """Hash immutable bytes using the protocol's single digest algorithm."""

    return hashlib.sha256(data).hexdigest()


def sha(path: Path) -> str:
    """Hash a regular file without following a protocol-controlled symlink."""

    if not path.is_file() or path.is_symlink():
        raise Stop("expected regular file: %s" % path)
    return sha_bytes(path.read_bytes())


def load(path: Path) -> dict[str, Any]:
    """Load canonical JSON and reject alternate byte encodings."""

    raw = path.read_bytes()
    try:
        value = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise Stop("invalid JSON: %s" % path) from error
    if type(value) is not dict or canonical(value) != raw:
        raise Stop("non-canonical object: %s" % path)
    return value


def create_once(path: Path, data: bytes) -> None:
    """Atomically publish immutable evidence, refusing a second publication."""

    path.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
    if os.path.lexists(path):
        raise Stop("create-once collision: %s" % path)
    try:
        descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    except FileExistsError as error:
        raise Stop("create-once collision: %s" % path) from error
    try:
        with os.fdopen(descriptor, "wb", closefd=False) as output:
            output.write(data)
            output.flush()
            os.fsync(output.fileno())
        os.fchmod(descriptor, 0o444)
    finally:
        os.close(descriptor)
    directory = os.open(path.parent, os.O_RDONLY)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)


def create_json_once(path: Path, value: dict[str, Any]) -> None:
    """Publish one canonical JSON evidence object."""

    create_once(path, canonical(value))


def seal_path(path: Path) -> Path:
    """Return the detached-seal path for one evidence record."""

    return path.with_name(path.name + ".sha256")


def create_seal_once(path: Path) -> None:
    """Publish a detached exact SHA-256 seal after the record is durable."""

    create_once(seal_path(path), (sha(path) + "\n").encode("ascii"))


def verify_seal(path: Path) -> str:
    """Verify a read-only record and its single-line detached seal."""

    mode = stat.S_IMODE(path.stat().st_mode)
    if mode & 0o222:
        raise Stop("mutable evidence: %s" % path)
    expected = sha(path)
    seal = seal_path(path)
    if not seal.is_file() or seal.is_symlink() or seal.read_bytes() != (expected + "\n").encode("ascii"):
        raise Stop("detached seal mismatch: %s" % path)
    if stat.S_IMODE(seal.stat().st_mode) & 0o222:
        raise Stop("mutable detached seal: %s" % seal)
    return expected


def protocol_ok(protocol: dict[str, Any]) -> None:
    """Validate the compact immutable contract before any dynamic operation."""

    required = {"schema", "revision", "run_id", "package_root", "execution_root",
                "review_root", "roles", "plan", "command", "environment"}
    if set(protocol) != required or protocol["schema"] != "ising-model.issue-4519.rev18":
        raise Stop("wrong rev18 protocol shape")
    if protocol["revision"] != 18 or protocol["run_id"] != "20260715T022945Z":
        raise Stop("wrong rev18 identity")
    if protocol["plan"] != ["Bf", "Af", "Ar", "Br", "Bw", "Aw"]:
        raise Stop("the six-action driver plan was altered")
    roles = protocol["roles"]
    if type(roles) is not dict or set(roles) != {"setup", "review", "run"} or len(set(roles.values())) != 3:
        raise Stop("authority roles are not separated")
    if type(protocol["command"]) is not list or not all(type(x) is str for x in protocol["command"]):
        raise Stop("fixed command is malformed")
    if type(protocol["environment"]) is not dict or not all(type(k) is str and type(v) is str
                                                               for k, v in protocol["environment"].items()):
        raise Stop("fixed environment is malformed")


def verify_package(package: Path) -> dict[str, Any]:
    """Verify the static package manifest without creating any dynamic root."""

    manifest_path = package / "package-manifest.json"
    manifest = load(manifest_path)
    if set(manifest) != {"schema", "run_id", "files"} or manifest["schema"] != "ising-model.issue-4519.rev18.package":
        raise Stop("wrong package manifest")
    if manifest["run_id"] != "20260715T022945Z" or type(manifest["files"]) is not dict:
        raise Stop("wrong package manifest identity")
    expected = set(manifest["files"]) | {"package-manifest.json", "package-manifest.json.sha256"}
    actual = {item.relative_to(package).as_posix() for item in package.rglob("*") if item.is_file()}
    if actual != expected:
        raise Stop("package file set changed")
    for relative, digest in manifest["files"].items():
        if type(relative) is not str or type(digest) is not str or sha(package / relative) != digest:
            raise Stop("package content changed: %s" % relative)
        if stat.S_IMODE((package / relative).stat().st_mode) & 0o222:
            raise Stop("immutable package contains writable file: %s" % relative)
    verify_seal(manifest_path)
    protocol = load(package / "protocol.json")
    protocol_ok(protocol)
    if Path(protocol["package_root"]) != package.resolve():
        raise Stop("package root authority mismatch")
    return protocol


def live_state(repo: Path) -> dict[str, str]:
    """Capture the live repository identity used by setup and run gates."""

    if not repo.is_dir():
        raise Stop("live repository missing")
    def git(*args: str) -> str:
        result = subprocess.run(["git", "-C", str(repo), *args], check=False,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        if result.returncode != 0:
            raise Stop("live git probe failed")
        return result.stdout
    lakefile = repo / "lakefile.lean"
    if not lakefile.is_file():
        raise Stop("live lakefile missing")
    return {"repo": str(repo.resolve()), "head": git("rev-parse", "HEAD").strip(),
            "clean": git("status", "--porcelain", "--untracked-files=no"),
            "lakefile_sha256": sha(lakefile)}


def sealed_object(path: Path, expected_schema: str) -> tuple[dict[str, Any], str]:
    """Load an exact, detached-sealed dynamic object of one schema."""

    digest = verify_seal(path)
    value = load(path)
    if value.get("schema") != expected_schema:
        raise Stop("wrong evidence schema: %s" % path)
    return value, digest


def require_authority(protocol: dict[str, Any], role: str, authority: str) -> None:
    """Require the one sealed authority name for an operation role."""

    if authority != protocol["roles"][role]:
        raise Stop("wrong %s authority" % role)


def setup(protocol: dict[str, Any], execution: Path, repo: Path, authority: str) -> Path:
    """Create only sealed setup evidence; this function never reviews or runs."""

    protocol_ok(protocol)
    require_authority(protocol, "setup", authority)
    if execution != Path(protocol["execution_root"]) or os.path.lexists(execution):
        raise Stop("execution root must be the absent sealed root")
    record = {"schema": "ising-model.issue-4519.rev18.setup", "revision": 18,
              "run_id": protocol["run_id"], "authority": authority,
              "protocol_sha256": sha(Path(protocol["package_root"]) / "protocol.json"),
              "live": live_state(repo)}
    execution.mkdir(mode=0o700, parents=True)
    path = execution / "setup.json"
    create_json_once(path, record)
    create_seal_once(path)
    return path


def create_review(protocol: dict[str, Any], execution: Path, review_root: Path,
                  authority: str) -> Path:
    """Create the external setup-review artifact, exactly once and detached-sealed."""

    protocol_ok(protocol)
    require_authority(protocol, "review", authority)
    if authority in {protocol["roles"]["setup"], protocol["roles"]["run"]}:
        raise Stop("reviewer is not independent")
    if review_root != Path(protocol["review_root"]) or os.path.lexists(review_root):
        raise Stop("review root must be the absent sealed root")
    setup_record, setup_sha = sealed_object(execution / "setup.json", "ising-model.issue-4519.rev18.setup")
    if setup_record["authority"] != protocol["roles"]["setup"]:
        raise Stop("setup authority mismatch")
    review_root.mkdir(mode=0o700, parents=True)
    review = {"schema": "ising-model.issue-4519.rev18.setup-review", "revision": 18,
              "run_id": protocol["run_id"], "authority": authority, "approved": True,
              "setup_sha256": setup_sha,
              "setup_live_sha256": sha_bytes(canonical(setup_record["live"])),
              "protocol_sha256": setup_record["protocol_sha256"]}
    path = review_root / "setup-review.json"
    create_json_once(path, review)
    create_seal_once(path)
    return path


def run_gate(protocol: dict[str, Any], execution: Path, review_root: Path,
             repo: Path, authority: str) -> tuple[dict[str, Any], str]:
    """Revalidate sealed disk evidence and the current repository before a run."""

    protocol_ok(protocol)
    require_authority(protocol, "run", authority)
    setup_record, setup_sha = sealed_object(execution / "setup.json", "ising-model.issue-4519.rev18.setup")
    review, _ = sealed_object(review_root / "setup-review.json", "ising-model.issue-4519.rev18.setup-review")
    expected_protocol = sha(Path(protocol["package_root"]) / "protocol.json")
    if review != {"schema": "ising-model.issue-4519.rev18.setup-review", "revision": 18,
                  "run_id": protocol["run_id"], "authority": protocol["roles"]["review"],
                  "approved": True, "setup_sha256": setup_sha,
                  "setup_live_sha256": sha_bytes(canonical(setup_record["live"])),
                  "protocol_sha256": expected_protocol}:
        raise Stop("external review artifact does not exactly approve current setup")
    if setup_record["protocol_sha256"] != expected_protocol or setup_record["live"] != live_state(repo):
        raise Stop("live state diverged from sealed setup")
    return setup_record, setup_sha


def replay(protocol: dict[str, Any], execution: Path) -> list[dict[str, Any]]:
    """Replay the complete six-action journal solely from sealed disk evidence."""

    journal = execution / "journal"
    names = sorted(item.name for item in journal.glob("*.json")) if journal.exists() else []
    expected_names = ["%02d-%s.json" % (n, action) for n, action in enumerate(protocol["plan"], 1)]
    if names != expected_names:
        raise Stop("journal does not contain exactly the six canonical actions")
    previous = ""
    records = []
    for n, action in enumerate(protocol["plan"], 1):
        path = journal / ("%02d-%s.json" % (n, action))
        record, digest = sealed_object(path, "ising-model.issue-4519.rev18.action")
        expected = {"schema": "ising-model.issue-4519.rev18.action", "revision": 18,
                    "run_id": protocol["run_id"], "number": n, "action": action,
                    "previous_sha256": previous, "command": protocol["command"],
                    "environment": protocol["environment"], "returncode": 0,
                    "stdout_sha256": record.get("stdout_sha256"), "stderr_sha256": record.get("stderr_sha256")}
        if record != expected or not all(type(record[key]) is str and len(record[key]) == 64
                                     for key in ["stdout_sha256", "stderr_sha256"]):
            raise Stop("invalid action record: %s" % path)
        previous = digest
        records.append(record)
    return records
