#!/usr/bin/env python3
"""Replay, security, and single-driver acceptance tests for revision 18."""

from __future__ import annotations

import copy
import json
import os
import shutil
import stat
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import calibrate  # noqa: E402
import manager  # noqa: E402


class Revision18Tests(unittest.TestCase):
    """Exercise only disposable execution/review roots and a disposable Git repo."""

    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.base = Path(self.temp.name)
        self.repo = self.base / "repo"
        self.repo.mkdir()
        (self.repo / "lakefile.lean").write_text("lean_lib Temp\n", encoding="utf-8")
        subprocess.run(["git", "-C", str(self.repo), "init", "-q"], check=True)
        subprocess.run(["git", "-C", str(self.repo), "add", "lakefile.lean"], check=True)
        subprocess.run(["git", "-C", str(self.repo), "-c", "user.name=t", "-c", "user.email=t@e", "commit", "-qm", "init"], check=True)
        self.protocol = copy.deepcopy(manager.load(ROOT / "protocol.json"))
        self.protocol["package_root"] = str(ROOT)
        self.execution = self.base / "execution"
        self.review = self.base / "review"
        self.protocol["execution_root"] = str(self.execution)
        self.protocol["review_root"] = str(self.review)

    def tearDown(self) -> None:
        self.temp.cleanup()

    def setup_review(self) -> None:
        manager.setup(self.protocol, self.execution, self.repo, "setup-operator")
        manager.create_review(self.protocol, self.execution, self.review, "independent-reviewer")

    def test_package_and_external_review_are_sealed(self) -> None:
        protocol = manager.verify_package(ROOT)
        self.assertEqual(protocol["run_id"], "20260715T022945Z")
        self.setup_review()
        review = self.review / "setup-review.json"
        self.assertTrue(review.exists())
        self.assertFalse(stat.S_IMODE(review.stat().st_mode) & 0o222)
        with self.assertRaises(manager.Stop):
            manager.create_review(self.protocol, self.execution, self.review, "independent-reviewer")

    def test_live_gate_rejects_repository_divergence(self) -> None:
        self.setup_review()
        (self.repo / "lakefile.lean").write_text("changed\n", encoding="utf-8")
        with self.assertRaisesRegex(manager.Stop, "live state diverged"):
            manager.run_gate(self.protocol, self.execution, self.review, self.repo, "calibration-executor")

    def test_setup_rejects_a_dangling_execution_root_symlink(self) -> None:
        self.execution.symlink_to(self.base / "missing-target")
        with self.assertRaisesRegex(manager.Stop, "execution root"):
            manager.setup(self.protocol, self.execution, self.repo, "setup-operator")

    def test_driver_executes_exact_six_actions_and_replays(self) -> None:
        self.setup_review()
        seen: list[tuple[str, ...]] = []
        def runner(command: list[str], cwd: Path, environment: dict[str, str]) -> tuple[int, bytes, bytes]:
            self.assertEqual(cwd, self.repo)
            self.assertEqual(command, self.protocol["command"])
            self.assertEqual(environment, self.protocol["environment"])
            seen.append(tuple(command))
            return 0, b"ok", b""
        calibrate.run_calibration(self.protocol, self.execution, self.review, self.repo,
                                  "calibration-executor", runner)
        self.assertEqual(len(seen), 6)
        self.assertEqual([item["action"] for item in manager.replay(self.protocol, self.execution)],
                         ["Bf", "Af", "Ar", "Br", "Bw", "Aw"])
        with self.assertRaises(manager.Stop):
            calibrate.run_calibration(self.protocol, self.execution, self.review, self.repo,
                                      "calibration-executor", runner)

    def test_replay_rejects_resealed_tampering_and_role_confusion(self) -> None:
        self.setup_review()
        with self.assertRaises(manager.Stop):
            manager.run_gate(self.protocol, self.execution, self.review, self.repo, "independent-reviewer")
        calibrate.run_calibration(self.protocol, self.execution, self.review, self.repo,
                                  "calibration-executor", lambda *_: (0, b"", b""))
        path = self.execution / "journal/03-Ar.json"
        os.chmod(path, 0o644)
        corrupt = manager.load(path)
        corrupt["action"] = "Bw"
        path.write_bytes(manager.canonical(corrupt))
        os.chmod(path, 0o444)
        os.chmod(manager.seal_path(path), 0o644)
        manager.seal_path(path).write_text(manager.sha(path) + "\n", encoding="ascii")
        os.chmod(manager.seal_path(path), 0o444)
        with self.assertRaisesRegex(manager.Stop, "invalid action record"):
            manager.replay(self.protocol, self.execution)

    def test_only_calibrate_owns_production_driver(self) -> None:
        self.assertIn("def run_calibration", (ROOT / "calibrate.py").read_text(encoding="utf-8"))
        self.assertNotIn("run_calibration", (ROOT / "review.py").read_text(encoding="utf-8"))


if __name__ == "__main__":
    unittest.main(verbosity=2)
