#!/usr/bin/env python3
"""Source-level checks for the static-only Issue #4519 rev19 remediation package.

This test intentionally neither imports the harness nor invokes a process.  It
checks the sealed protocol and the source contract only; it cannot authorize a
Lake/Lean/build/calibration action.
"""

from __future__ import annotations

import ast
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
protocol = json.loads((ROOT / "protocol.json").read_text(encoding="utf-8"))
source = (ROOT / "harness.py").read_text(encoding="utf-8")

assert protocol["static_only"] is True
assert protocol["before"] == "6a2470114fe0b5dd5c6cdcbb0e02b8acca351fb4"
assert protocol["after"] == "94ceb4f83906dc23069b7566ce31242240e22855"
assert protocol["command"] == ["lake", "--no-ansi", "--no-cache", "build", "IsingModel"]
assert protocol["plan"] == ["Bf", "Af", "Ar", "Br", "Bw", "Aw"]
assert set(protocol["authority"]) == {"setup", "review", "run", "anchor"}
assert len({value["key_id"] for value in protocol["authority"].values()}) == 4
assert len({value["spki_sha256"] for value in protocol["authority"].values()}) == 4
assert protocol["evidence_contract"]["inventory"]["algorithm"] == "recursive-lstat-v1"
assert protocol["evidence_contract"]["raw_capture"]["per_action"] == [
    "stdout.raw", "stderr.raw", "time-rss.raw", "warnings.raw"]
assert "full-chain-reseal-rejected-without-anchor-key" in protocol["evidence_contract"]["tamper_tests"]
assert "/usr/bin/time" in source and "Ed25519" in source and "validate_terminal" in source
assert "validate_inventory" in source and "execution_inventory" in source
assert "published_immutable" in source and "full-chain reseal" in source
tree = ast.parse(source)
for node in ast.walk(tree):
    assert not isinstance(node, (ast.Import, ast.ImportFrom)) or all(
        alias.name not in {"subprocess", "os", "shutil"} for alias in node.names)
