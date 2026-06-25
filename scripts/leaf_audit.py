#!/usr/bin/env python3
"""Import-graph leaf audit for the IsingModel Lean library.

The ``lakefile.toml`` globs ``["IsingModel", "IsingModel.+"]``, so *every*
``.lean`` file under ``IsingModel/`` is a build target regardless of whether
any genuine terminal capstone needs it.  Orphan / dead modules therefore stay
on the build critical path even though nothing depends on them.  This script
analyses the static ``import`` graph to surface candidates for removal.

Definitions
-----------
* **orphan**: a module that is reachable from *nothing* — not even the
  catch-all root umbrella ``IsingModel.lean``.  NOTE: genuine terminal
  capstones are themselves leaves that nothing imports, so the orphan set
  ALWAYS contains real results (e.g. ``ContinuousSpin.TwoComponentLebowitz``,
  ``LatticeSystemBridge.*``, the ``GKSTest`` entry ``TestGenerators``).
  **Orphan does NOT mean deletable.**
* **dead (relative to a capstone set)**: a module not contained in the
  transitive import-closure of any genuine terminal capstone.  This is only
  trustworthy when the capstone set is *complete*; an incomplete set
  over-reports dead modules (it will flag everything reachable only via the
  still-missing capstones).

Usage
-----
    python3 scripts/leaf_audit.py                 # list orphans
    python3 scripts/leaf_audit.py CAPSTONES_FILE  # dead set vs a capstone list

``CAPSTONES_FILE`` is a newline-separated list of module names (e.g.
``IsingModel.Peierls.CubicBoxShellConnected``); ``#`` comments and blank lines
are ignored.  Because the curated capstone list is the hard part, the dead-set
output must be cross-checked against ``lake build`` before any deletion.
"""
from __future__ import annotations

import os
import re
import sys
from collections import defaultdict

ROOT_DIR = "IsingModel"
ROOT_MODULE = "IsingModel"
ROOT_FILE = "IsingModel.lean"
_IMPORT_RE = re.compile(r"^import\s+(IsingModel\S*)")


def _module_of_path(path: str) -> str:
    """Convert ``IsingModel/Foo/Bar.lean`` to the module ``IsingModel.Foo.Bar``."""
    assert path.endswith(".lean")
    return path[:-5].replace(os.sep, ".")


def _path_of_module(module: str) -> str:
    """Convert a module name back to its source path."""
    return module.replace(".", os.sep) + ".lean"


def build_import_graph() -> tuple[dict[str, set[str]], set[str]]:
    """Scan the source tree and return ``(imports, all_modules)``.

    ``imports[m]`` is the set of ``IsingModel.*`` modules that module ``m``
    imports directly.  ``all_modules`` is every module found, including the
    root umbrella when present.
    """
    imports: dict[str, set[str]] = defaultdict(set)
    all_modules: set[str] = set()
    for dirpath, _dirs, files in os.walk(ROOT_DIR):
        for filename in files:
            if not filename.endswith(".lean"):
                continue
            path = os.path.join(dirpath, filename)
            module = _module_of_path(path)
            all_modules.add(module)
            with open(path, encoding="utf-8", errors="replace") as handle:
                for line in handle:
                    match = _IMPORT_RE.match(line)
                    if match:
                        imports[module].add(match.group(1))
    if os.path.exists(ROOT_FILE):
        all_modules.add(ROOT_MODULE)
        with open(ROOT_FILE, encoding="utf-8", errors="replace") as handle:
            for line in handle:
                match = _IMPORT_RE.match(line)
                if match:
                    imports[ROOT_MODULE].add(match.group(1))
    return imports, all_modules


def closure(imports: dict[str, set[str]], seeds) -> set[str]:
    """Return the transitive import-closure of ``seeds`` under ``imports``."""
    seen: set[str] = set()
    stack = list(seeds)
    while stack:
        node = stack.pop()
        if node in seen:
            continue
        seen.add(node)
        stack.extend(child for child in imports.get(node, ()) if child not in seen)
    return seen


def line_count(module: str) -> int:
    """Return the line count of a module's source file (0 if missing)."""
    try:
        with open(_path_of_module(module), encoding="utf-8", errors="replace") as handle:
            return sum(1 for _ in handle)
    except FileNotFoundError:
        return 0


def read_capstones(path: str) -> list[str]:
    """Read a newline-separated capstone module list (``#`` comments ignored)."""
    capstones: list[str] = []
    with open(path, encoding="utf-8", errors="replace") as handle:
        for line in handle:
            stripped = line.split("#", 1)[0].strip()
            if stripped:
                capstones.append(stripped)
    return capstones


def main(argv: list[str]) -> int:
    """Entry point: print orphans, or the dead set relative to a capstone list."""
    imports, all_modules = build_import_graph()
    root_reachable = closure(imports, [ROOT_MODULE])
    orphans = sorted(all_modules - root_reachable - {ROOT_MODULE})

    print(f"total modules: {len(all_modules)}")
    print(f"root-reachable: {len(root_reachable)}")
    print(f"orphans (reachable from nothing — INCLUDES genuine capstones): {len(orphans)}")
    for module in orphans:
        print(f"  {line_count(module):6d}  {module}")

    if len(argv) > 1:
        capstones = read_capstones(argv[1])
        present = [c for c in capstones if c in all_modules]
        missing = [c for c in capstones if c not in all_modules]
        if missing:
            print(f"\nWARNING: {len(missing)} capstone(s) not found as modules:")
            for module in missing:
                print(f"  {module}")
        live = closure(imports, present)
        dead = sorted(all_modules - live - {ROOT_MODULE}, key=line_count, reverse=True)
        dead_lines = sum(line_count(m) for m in dead)
        print(
            f"\nlive (closure of {len(present)} capstones): {len(live)}; "
            f"dead vs this list: {len(dead)} files / {dead_lines} lines"
        )
        print("(trustworthy ONLY if the capstone list is complete; verify with lake build)")
        for module in dead:
            print(f"  {line_count(module):6d}  {module}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
