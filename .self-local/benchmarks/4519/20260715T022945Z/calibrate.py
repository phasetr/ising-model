#!/usr/bin/env python3
"""The sole revision-18 production calibration driver."""

from __future__ import annotations

import argparse
import os
import subprocess
from pathlib import Path
from typing import Callable

import manager


def run_calibration(protocol: dict, execution: Path, review_root: Path, repo: Path,
                    authority: str, runner: Callable[[list[str], Path, dict[str, str]], tuple[int, bytes, bytes]]) -> None:
    """Gate and execute exactly Bf, Af, Ar, Br, Bw, Aw once in that order."""

    manager.run_gate(protocol, execution, review_root, repo, authority)
    journal = execution / "journal"
    if journal.exists():
        raise manager.Stop("calibration journal is create-once")
    previous = ""
    for number, action in enumerate(protocol["plan"], 1):
        code, stdout, stderr = runner(protocol["command"], repo, protocol["environment"])
        if type(code) is not int or code != 0 or type(stdout) is not bytes or type(stderr) is not bytes:
            raise manager.Stop("fixed calibration command failed at %s" % action)
        record = {"schema": "ising-model.issue-4519.rev18.action", "revision": 18,
                  "run_id": protocol["run_id"], "number": number, "action": action,
                  "previous_sha256": previous, "command": protocol["command"],
                  "environment": protocol["environment"], "returncode": code,
                  "stdout_sha256": manager.sha_bytes(stdout), "stderr_sha256": manager.sha_bytes(stderr)}
        path = journal / ("%02d-%s.json" % (number, action))
        manager.create_json_once(path, record)
        manager.create_seal_once(path)
        previous = manager.sha(path)
    manager.replay(protocol, execution)


def subprocess_runner(command: list[str], cwd: Path, environment: dict[str, str]) -> tuple[int, bytes, bytes]:
    """Run only the immutable protocol command under its immutable environment."""

    env = {**os.environ, **environment}
    completed = subprocess.run(command, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               check=False)
    return completed.returncode, completed.stdout, completed.stderr


def main() -> None:
    """Expose setup and the single gated calibration command."""

    parser = argparse.ArgumentParser()
    parser.add_argument("operation", choices=["setup", "run"])
    parser.add_argument("--repo-root", required=True, type=Path)
    parser.add_argument("--authority", required=True)
    args = parser.parse_args()
    package = Path(__file__).resolve().parent
    protocol = manager.verify_package(package)
    execution = Path(protocol["execution_root"])
    if args.operation == "setup":
        manager.setup(protocol, execution, args.repo_root, args.authority)
    else:
        run_calibration(protocol, execution, Path(protocol["review_root"]), args.repo_root,
                        args.authority, subprocess_runner)


if __name__ == "__main__":
    main()
