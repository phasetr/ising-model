"""Adversarial signed-chain tests for the revision 22 static validator."""

from __future__ import annotations

import base64
import copy
import hashlib
import importlib.util
import json
import os
import shutil
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("rev22_harness", ROOT / "harness.py")
assert spec and spec.loader
h = importlib.util.module_from_spec(spec)
spec.loader.exec_module(h)

SEEDS = {"setup": "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
         "review": "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
         "run": "c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7",
         "anchor": "f5e5767cf153319517630f226876b86c8160cc583bc013744c6bf255f5cc0ee5"}


def encode(point: tuple[int, int]) -> bytes:
    """Encode one Edwards point in RFC 8032 compressed form."""

    x, y = point
    return (y | ((x & 1) << 255)).to_bytes(32, "little")


def sign(seed: str, message: bytes) -> str:
    """Create a deterministic real Ed25519 fixture signature."""

    expanded = hashlib.sha512(bytes.fromhex(seed)).digest()
    scalar = int.from_bytes(expanded[:32], "little")
    scalar &= (1 << 254) - 8
    scalar |= 1 << 254
    public = encode(h._scalar_mult((h.BX, h.BY), scalar))
    nonce = int.from_bytes(hashlib.sha512(expanded[32:] + message).digest(), "little") % h.L
    encoded_r = encode(h._scalar_mult((h.BX, h.BY), nonce))
    challenge = int.from_bytes(hashlib.sha512(encoded_r + public + message).digest(), "little") % h.L
    return base64.b64encode(encoded_r + ((nonce + challenge * scalar) % h.L).to_bytes(32, "little")).decode()


def signature(role: str, record: dict) -> dict:
    """Attach a complete non-mocked signed record."""

    return {"algorithm": "Ed25519", "key_id": f"issue4519-rev22-{role}", "record_sha256": h.digest(record),
            "signature_b64": sign(SEEDS[role], h.canonical(record))}


def inventory(tag: str, inode: int = 100) -> dict:
    """Construct a minimal recursive lstat-shaped inventory fixture."""

    return {".": {"type": "directory", "mode": 0o700, "device": 7, "inode": inode},
            "artifact": {"type": "file", "mode": 0o600, "device": 7, "inode": inode + 1, "size": len(tag),
                         "sha256": hashlib.sha256(tag.encode()).hexdigest()}}


class SignedFullChainTests(unittest.TestCase):
    """Exercise actual signatures and all structural boundaries."""

    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name) / "package"
        shutil.copytree(ROOT, self.root, ignore=shutil.ignore_patterns("__pycache__"))
        self.protocol = json.loads((self.root / "protocol.json").read_text())
        self.manifest_sha = h.validate_package_manifest(self.root)

    def tearDown(self) -> None:
        self.temp.cleanup()

    def raw(self, action_id: str) -> dict:
        """Create the four real per-action raw files and their facts."""

        payloads = {"stdout.raw": b"stdout\n", "stderr.raw": b"stderr\n",
                    "time-rss.raw": b"maximum resident set size = 1\n", "warnings.raw": b"warning: fixture\n"}
        result = {}
        for name, payload in payloads.items():
            path = self.root / "raw" / action_id / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(payload)
            result[name] = {"action_id": action_id, "path": f"raw/{action_id}/{name}", "sha256": hashlib.sha256(payload).hexdigest()}
        result["warnings.raw"]["warning_count"] = 1
        return result

    def terminal_inventory(self) -> dict:
        """Create the exact terminal state and return its complete lstat inventory."""

        state = self.root / "state"
        state.mkdir()
        (state / "terminal-failure.json").write_bytes(b"{}")
        (state / "terminal-failure.sig").write_bytes(b"sig")
        return h._terminal_disk_objects(self.root)

    def chain(self):
        """Create Bf success followed by a terminal Af failure."""

        initial, after_bf = inventory("initial", 100), inventory("after-bf", 110)
        setup = {"schema": h.SCHEMA + ".setup", "run_id": h.RUN_ID, "stage": "setup", "command": h.ARGV,
                 "worktrees": {"A": {"head": h.AFTER, "detached": True, "tracked_clean": True,
                                      "root": {"device": 1, "inode": 1}, "inventory": inventory("A", 1)},
                               "B": {"head": h.BEFORE, "detached": True, "tracked_clean": True,
                                      "root": {"device": 2, "inode": 2}, "inventory": inventory("B", 3)}},
                 "execution_inventory": initial}
        setup_sha = h.digest(setup)
        root_sha = h.validate_external_root_anchor(self.root, self.protocol, self.manifest_sha)
        review = {"schema": h.SCHEMA + ".review", "run_id": h.RUN_ID, "approved": True,
                  "package_manifest_sha256": self.manifest_sha, "root_anchor_sha256": root_sha, "setup_sha256": setup_sha}
        review_sha = h.digest(review)
        action = {"schema": h.SCHEMA + ".action", "run_id": h.RUN_ID, "index": 0, "action": "Bf", "action_id": "Bf-000",
                  "worktree": "B", "worktree_head": h.BEFORE, "argv": h.ARGV, "prior_sha256": review_sha, "returncode": 0,
                  "before_inventory": initial, "before_inventory_sha256": h.digest(initial), "after_inventory": after_bf, "raw": self.raw("Bf-000")}
        action_sha = h.digest(action)
        terminal = {"schema": h.SCHEMA + ".terminal-failure", "run_id": h.RUN_ID, "index": 1, "action": "Af", "action_id": "Af-001",
                    "worktree": "A", "worktree_head": h.AFTER, "argv": h.ARGV, "prior_sha256": action_sha, "returncode": 1,
                    "before_inventory": after_bf, "before_inventory_sha256": h.digest(after_bf), "after_inventory": after_bf,
                    "terminal_state_inventory": self.terminal_inventory(), "raw": self.raw("Af-001")}
        terminal_sha = h.digest(terminal)
        anchor = {"schema": h.SCHEMA + ".execution-anchor", "run_id": h.RUN_ID, "package_manifest_sha256": self.manifest_sha,
                  "root_anchor_sha256": root_sha, "setup_sha256": setup_sha, "review_sha256": review_sha,
                  "terminal_or_journal_head_sha256": terminal_sha,
                  "publication": {"kind": "github-gist-git-commit", "commit_sha": "a" * 40}}
        published = h.canonical({key: value for key, value in anchor.items() if key != "publication"})
        anchor["publication"]["published_object_sha256"] = hashlib.sha256(published).hexdigest()
        return (setup, signature("setup", setup)), (review, signature("review", review)), [(action, signature("run", action))], (terminal, signature("run", terminal)), (anchor, signature("anchor", anchor), published)

    def test_manifest_includes_validator(self) -> None:
        self.assertIn("harness.py", json.loads((self.root / "package-manifest.json").read_text())["files"])
        (self.root / "harness.py").write_text("tampered\n")
        with self.assertRaises(h.BoundaryError):
            h.validate_package_manifest(self.root)

    def test_terminal_rejects_extra_directory_and_symlink(self) -> None:
        inventory_record = self.terminal_inventory()
        (self.root / "state" / "extra").mkdir()
        with self.assertRaises(h.BoundaryError):
            h.validate_terminal_state_files(self.root, inventory_record)
        shutil.rmtree(self.root / "state" / "extra")
        os.symlink("terminal-failure.json", self.root / "state" / "extra-link")
        with self.assertRaises(h.BoundaryError):
            h.validate_terminal_state_files(self.root, inventory_record)

    @unittest.skipUnless(os.environ.get("REV22_ANCHOR_READY") == "1", "anchor is published only after pre-anchor validation")
    def test_signed_full_chain_and_resealed_substitutions(self) -> None:
        chain = self.chain()
        h.validate_full_chain(self.root, self.protocol, *chain)
        setup, review, journal, terminal, anchor = copy.deepcopy(chain)
        review[0]["approved"] = False
        review = (review[0], signature("review", review[0]))
        with self.assertRaises(h.BoundaryError):
            h.validate_full_chain(self.root, self.protocol, setup, review, journal, terminal, anchor)
        setup, review, journal, terminal, anchor = self.chain()
        (self.root / "state" / "surplus").mkdir()
        with self.assertRaises(h.BoundaryError):
            h.validate_full_chain(self.root, self.protocol, setup, review, journal, terminal, anchor)


if __name__ == "__main__":
    unittest.main()
