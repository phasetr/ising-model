#!/usr/bin/env python3
"""Static source checks; no test in this root runs a build or a process."""

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
assert protocol["evidence_contract"]["raw_capture"]["per_action"] == ["stdout.raw", "stderr.raw", "time-rss.raw", "warnings.raw"]
assert protocol["evidence_contract"]["terminal_failure"]["exact_allowlist"] == ["state/terminal-failure.json", "state/terminal-failure.sig"]
assert "verify_ed25519" in source and "validate_full_chain" in source and "validate_root_anchor" in source
for node in ast.walk(ast.parse(source)):
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        assert all(alias.name not in {"subprocess", "os", "shutil", "socket", "urllib", "http", "requests"} for alias in node.names)
