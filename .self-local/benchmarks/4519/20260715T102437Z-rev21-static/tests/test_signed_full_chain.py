"""Actual Ed25519 signed full-chain adversarial tests for revision 21."""

from __future__ import annotations

import base64
import copy
import hashlib
import importlib.util
import json
import shutil
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("harness", ROOT / "harness.py")
assert spec and spec.loader
harness = importlib.util.module_from_spec(spec)
spec.loader.exec_module(harness)

SEEDS = {
    "setup": "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
    "review": "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
    "run": "c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7",
    "anchor": "f5e5767cf153319517630f226876b86c8160cc583bc013744c6bf255f5cc0ee5",
}


def encode(point: tuple[int, int]) -> bytes:
    """Encode an Edwards point in the RFC 8032 compressed form."""

    x, y = point
    return (y | ((x & 1) << 255)).to_bytes(32, "little")


def sign(seed_hex: str, message: bytes) -> str:
    """Make a deterministic Ed25519 test signature from an RFC 8032 seed."""

    expanded = hashlib.sha512(bytes.fromhex(seed_hex)).digest()
    scalar = int.from_bytes(expanded[:32], "little")
    scalar &= (1 << 254) - 8
    scalar |= 1 << 254
    public = encode(harness._scalar_mult((harness.BX, harness.BY), scalar))
    nonce = int.from_bytes(hashlib.sha512(expanded[32:] + message).digest(), "little") % harness.L
    encoded_r = encode(harness._scalar_mult((harness.BX, harness.BY), nonce))
    challenge = int.from_bytes(hashlib.sha512(encoded_r + public + message).digest(), "little") % harness.L
    signature = encoded_r + ((nonce + challenge * scalar) % harness.L).to_bytes(32, "little")
    return base64.b64encode(signature).decode()


def signature(role: str, record: dict) -> dict:
    """Build a complete detached signature, never a verifier mock."""

    return {"algorithm": "Ed25519", "key_id": f"issue4519-rev21-{role}", "record_sha256": harness.digest(record),
            "signature_b64": sign(SEEDS[role], harness.canonical(record))}


def inventory(tag: str) -> dict:
    """Return a compact but recursively shaped lstat inventory fixture."""

    return {".": {"type": "directory", "mode": 0o700, "device": 7, "inode": 100},
            "artifact": {"type": "file", "mode": 0o600, "device": 7, "inode": 101, "size": len(tag),
                         "sha256": hashlib.sha256(tag.encode()).hexdigest()}}


def terminal_inventory() -> dict:
    """Return the actual terminal state directory inventory and nothing extra."""

    return {".": {"type": "directory", "mode": 0o700, "device": 7, "inode": 200},
            "state/terminal-failure.json": {"type": "file", "mode": 0o600, "device": 7, "inode": 201, "size": 2,
                                            "sha256": hashlib.sha256(b"{}").hexdigest()},
            "state/terminal-failure.sig": {"type": "file", "mode": 0o600, "device": 7, "inode": 202, "size": 3,
                                           "sha256": hashlib.sha256(b"sig").hexdigest()}}


class Response:
    """Minimal context manager used to supply the independently signed root bytes."""

    def __init__(self, payload: bytes):
        self.payload = payload

    def __enter__(self):
        return self

    def __exit__(self, *_args):
        return False

    def read(self) -> bytes:
        return self.payload


class SignedFullChainTests(unittest.TestCase):
    """Build a real signed baseline then prove required substitutions are rejected."""

    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name) / "package"
        shutil.copytree(ROOT, self.root, ignore=shutil.ignore_patterns("__pycache__"))
        self.protocol = json.loads((self.root / "protocol.json").read_text())
        self.manifest_sha = harness.validate_package_manifest(self.root)
        self.root_payload = {"schema": harness.SCHEMA + ".root-anchor", "run_id": harness.RUN_ID,
                             "package_manifest_sha256": self.manifest_sha,
                             "authority_spki_sha256": {role: self.protocol["authority"][role]["spki_sha256"] for role in harness.ROLES}}
        # The baseline uses the immutable public root itself; no caller bytes
        # or verifier mock can make the root-anchor gate pass.

    def tearDown(self) -> None:
        self.temp.cleanup()

    def raw(self, action_id: str, warning: bytes = b"warning: fixture\n") -> dict:
        """Create the four real action-id-specific raw files and their signed facts."""

        payloads = {"stdout.raw": b"stdout\n", "stderr.raw": b"stderr\n", "time-rss.raw": b"maximum resident set size = 1\n", "warnings.raw": warning}
        result = {}
        for name, payload in payloads.items():
            path = self.root / "raw" / action_id / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(payload)
            result[name] = {"action_id": action_id, "path": f"raw/{action_id}/{name}", "sha256": hashlib.sha256(payload).hexdigest()}
        result["warnings.raw"]["warning_count"] = sum("warning:" in line.lower() for line in warning.decode().splitlines())
        return result

    def chain(self):
        """Create the smallest valid signed chain: Bf succeeded, Af terminally failed."""

        initial, after_bf = inventory("initial"), inventory("after-bf")
        setup = {"schema": harness.SCHEMA + ".setup", "run_id": harness.RUN_ID, "stage": "setup", "command": harness.ARGV,
                 "worktrees": {"A": {"head": harness.AFTER, "detached": True, "tracked_clean": True,
                                      "root": {"device": 1, "inode": 1}, "inventory": inventory("A")},
                               "B": {"head": harness.BEFORE, "detached": True, "tracked_clean": True,
                                      "root": {"device": 2, "inode": 2}, "inventory": inventory("B")}},
                 "execution_inventory": initial}
        setup_sha = harness.digest(setup)
        root_sha = harness.digest(self.root_payload)
        review = {"schema": harness.SCHEMA + ".review", "run_id": harness.RUN_ID, "approved": True,
                  "package_manifest_sha256": self.manifest_sha, "root_anchor_sha256": root_sha, "setup_sha256": setup_sha}
        review_sha = harness.digest(review)
        action_id = "Bf-000"
        action = {"schema": harness.SCHEMA + ".action", "run_id": harness.RUN_ID, "index": 0, "action": "Bf", "action_id": action_id,
                  "worktree": "B", "worktree_head": harness.BEFORE, "argv": harness.ARGV, "prior_sha256": review_sha, "returncode": 0,
                  "before_inventory": initial, "before_inventory_sha256": harness.digest(initial), "after_inventory": after_bf, "raw": self.raw(action_id)}
        action_sha = harness.digest(action)
        terminal_id = "Af-001"
        terminal = {"schema": harness.SCHEMA + ".terminal-failure", "run_id": harness.RUN_ID, "index": 1, "action": "Af", "action_id": terminal_id,
                    "worktree": "A", "worktree_head": harness.AFTER, "argv": harness.ARGV, "prior_sha256": action_sha, "returncode": 1,
                    "before_inventory": after_bf, "before_inventory_sha256": harness.digest(after_bf), "after_inventory": after_bf,
                    "terminal_state_inventory": terminal_inventory(), "state_files": list(harness.TERMINAL_ALLOWLIST), "raw": self.raw(terminal_id)}
        (self.root / "state").mkdir(parents=True, exist_ok=True)
        (self.root / "state" / "terminal-failure.json").write_bytes(b"{}")
        (self.root / "state" / "terminal-failure.sig").write_bytes(b"sig")
        terminal_sha = harness.digest(terminal)
        anchor = {"schema": harness.SCHEMA + ".execution-anchor", "run_id": harness.RUN_ID,
                  "package_manifest_sha256": self.manifest_sha, "root_anchor_sha256": root_sha, "setup_sha256": setup_sha,
                  "review_sha256": review_sha, "terminal_or_journal_head_sha256": terminal_sha,
                  "publication": {"kind": "github-gist-git-commit", "commit_sha": "a" * 40}}
        published = harness.canonical({key: value for key, value in anchor.items() if key != "publication"})
        anchor["publication"]["published_object_sha256"] = hashlib.sha256(published).hexdigest()
        return (setup, signature("setup", setup)), (review, signature("review", review)), [(action, signature("run", action))], (terminal, signature("run", terminal)), (anchor, signature("anchor", anchor), published)

    def validates(self, chain) -> None:
        harness.validate_full_chain(self.root, self.protocol, *chain)

    def rejects(self, chain) -> None:
        with self.assertRaises(harness.BoundaryError):
            self.validates(chain)

    def test_signed_full_chain_baseline(self) -> None:
        self.validates(self.chain())

    def test_forged_warning_count_is_rejected(self) -> None:
        setup, review, journal, terminal, anchor = self.chain()
        terminal = copy.deepcopy(terminal)
        terminal[0]["raw"]["warnings.raw"]["warning_count"] = 0
        terminal = (terminal[0], signature("run", terminal[0]))
        self.rejects((setup, review, journal, terminal, anchor))

    def test_cross_action_raw_reuse_is_rejected(self) -> None:
        setup, review, journal, terminal, anchor = self.chain()
        terminal = copy.deepcopy(terminal)
        terminal[0]["raw"]["stdout.raw"]["action_id"] = "Bf-000"
        terminal[0]["raw"]["stdout.raw"]["path"] = "raw/Bf-000/stdout.raw"
        terminal = (terminal[0], signature("run", terminal[0]))
        self.rejects((setup, review, journal, terminal, anchor))

    def test_missing_terminal_state_file_is_rejected(self) -> None:
        setup, review, journal, terminal, anchor = self.chain()
        (self.root / "state" / "terminal-failure.sig").unlink()
        self.rejects((setup, review, journal, terminal, anchor))

    def test_inventory_discontinuity_is_rejected(self) -> None:
        setup, review, journal, terminal, anchor = self.chain()
        journal = copy.deepcopy(journal)
        journal[0][0]["before_inventory_sha256"] = "0" * 64
        journal[0] = (journal[0][0], signature("run", journal[0][0]))
        self.rejects((setup, review, journal, terminal, anchor))

    def test_anchor_reseal_replacement_is_rejected(self) -> None:
        setup, review, journal, terminal, anchor = self.chain()
        review = copy.deepcopy(review)
        review[0]["approved"] = False
        review = (review[0], signature("review", review[0]))
        self.rejects((setup, review, journal, terminal, anchor))


if __name__ == "__main__":
    unittest.main()
