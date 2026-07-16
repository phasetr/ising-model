#!/usr/bin/env python3
"""Audit gate for the IsingModel Lean library (V1-V3).

Deterministic, dependency-free checks intended to run in CI (and, if wired,
from a git pre-push hook). Uses only the Python 3 standard library.

Checks
------
V1  No ``axiom`` declarations anywhere under ``IsingModel/``. The project has
    no axiomatized targets, so the expected count is zero.
V2  No ``sorry`` / ``admit`` / ``native_decide`` in library code, after
    blanking comments and string literals. ``native_decide`` is exempt only in
    the files listed in ``V2_NATIVE_DECIDE_FILE_ALLOWLIST`` (executable
    sanity-check ``example``s embedded in the library directory).
V3  Capstone axiom audit. For every fully-qualified name in
    ``scripts/audit/capstones.txt`` the ``#print axioms`` output must be a
    subset of ``{propext, Classical.choice, Quot.sound}``. An unknown
    identifier is a hard failure (keeps the capstone list honest).

Usage
-----
    python3 scripts/audit_gate.py            # V1 + V2 always; V3 if lake env present
    python3 scripts/audit_gate.py --full     # V1 + V2 + V3 (V3 required; CI mode)

Exit code 0 iff every executed check passes; 1 otherwise.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from pathlib import Path

# Repository root = parent of the ``scripts`` directory holding this file.
REPO_ROOT = Path(__file__).resolve().parent.parent
LIB_DIR = REPO_ROOT / "IsingModel"
CAPSTONES_FILE = REPO_ROOT / "scripts" / "audit" / "capstones.txt"
# Scratch dir for the V3 temp .lean (gitignored; avoids leaking into the tree).
TEMP_DIR = REPO_ROOT / ".self-local" / "tmp"

# Only these files may contain ``native_decide`` (executable sanity-check
# ``example``s living in the library directory). This exemption covers
# ``native_decide`` only, never ``sorry`` or ``admit``.
V2_NATIVE_DECIDE_FILE_ALLOWLIST = {"IsingModel/TestGenerators.lean"}

# The axioms every capstone is permitted to depend on (subset accepted).
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})


def strip_noncode(source: str) -> str:
    """Return ``source`` with comments and string-literal contents blanked out.

    A single left-to-right character scanner tracks four mutually exclusive
    states simultaneously, so a delimiter that appears *inside* another
    construct never triggers a spurious transition:

    * code
    * double-quoted string (backslash escapes consumed as a unit)
    * line comment (``--`` to end of line)
    * nested block comment (``/- ... -/``)

    This closes the fail-open hole of running string- and comment-stripping as
    two independent passes (e.g. ``def m := "/-"`` would otherwise open a block
    comment and swallow subsequent real code). Blanked characters become spaces
    (newlines preserved) so line/column numbers stay accurate for diagnostics.
    """
    out: list[str] = []
    i = 0
    n = len(source)
    state = "code"  # code | string | line | block
    block_depth = 0
    while i < n:
        ch = source[i]
        nxt = source[i + 1] if i + 1 < n else ""
        if state == "code":
            if ch == '"':
                state = "string"
                out.append('"')
                i += 1
            elif ch == "-" and nxt == "-":
                state = "line"
                out.append("  ")
                i += 2
            elif ch == "/" and nxt == "-":
                state = "block"
                block_depth = 1
                out.append("  ")
                i += 2
            else:
                out.append(ch)
                i += 1
        elif state == "string":
            if ch == "\\" and i + 1 < n:
                # Consume the escaped char as a unit, preserving a trailing
                # newline (Lean string line-continuation) for line accounting.
                out.append(" \n" if source[i + 1] == "\n" else "  ")
                i += 2
            elif ch == '"':
                state = "code"
                out.append('"')
                i += 1
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
        elif state == "line":
            if ch == "\n":
                state = "code"
                out.append("\n")
                i += 1
            else:
                out.append(" ")
                i += 1
        else:  # block comment
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.append("  ")
                i += 2
            elif ch == "-" and nxt == "/":
                block_depth -= 1
                out.append("  ")
                i += 2
                if block_depth == 0:
                    state = "code"
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
    return "".join(out)


def iter_lib_files() -> list[Path]:
    """Return every ``*.lean`` file under ``IsingModel/`` (sorted)."""
    return sorted(LIB_DIR.rglob("*.lean"))


def rel(path: Path) -> str:
    """Return ``path`` relative to the repository root, POSIX style."""
    return path.relative_to(REPO_ROOT).as_posix()


# ``axiom`` command with any leading attribute block and any combination of
# declaration modifiers (private / protected / noncomputable / unsafe /
# scoped[...] / local). Applied to comment/string-stripped text.
_AXIOM_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:(?:private|protected|noncomputable|unsafe)\s+"
    r"|(?:scoped|local)(?:\s*\[[^\]]*\])?\s+)*"
    r"axiom\b"
)


def check_v1() -> list[str]:
    """V1: report any top-level ``axiom`` declaration under ``IsingModel/``."""
    failures: list[str] = []
    for path in iter_lib_files():
        text = strip_noncode(path.read_text(encoding="utf-8"))
        for lineno, line in enumerate(text.splitlines(), start=1):
            if _AXIOM_RE.match(line):
                failures.append(f"{rel(path)}:{lineno}: axiom declaration")
    return failures


def check_v2() -> list[str]:
    """V2: report ``sorry`` / ``admit`` / ``native_decide`` in library code."""
    failures: list[str] = []
    tokens = ("sorry", "admit", "native_decide")
    word_res = {tok: re.compile(rf"\b{re.escape(tok)}\b") for tok in tokens}
    for path in iter_lib_files():
        relpath = rel(path)
        cleaned = strip_noncode(path.read_text(encoding="utf-8"))
        for lineno, line in enumerate(cleaned.splitlines(), start=1):
            for tok in tokens:
                if not word_res[tok].search(line):
                    continue
                if tok == "native_decide" and relpath in V2_NATIVE_DECIDE_FILE_ALLOWLIST:
                    continue
                failures.append(f"{relpath}:{lineno}: `{tok}`")
    return failures


def read_capstones() -> list[str]:
    """Read fully-qualified capstone names, dropping comments and blanks."""
    names: list[str] = []
    for raw in CAPSTONES_FILE.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        names.append(line)
    return names


def parse_axioms_output(output: str) -> dict[str, set[str]]:
    """Parse ``#print axioms`` output into ``name -> axiom set``.

    Names Lean could not resolve simply do not appear in the result.
    """
    result: dict[str, set[str]] = {}
    dep_re = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
    none_re = re.compile(r"'([^']+)' does not depend on any axioms")
    for match in dep_re.finditer(output):
        body = match.group(2).strip()
        result[match.group(1)] = {a.strip() for a in body.split(",") if a.strip()}
    for match in none_re.finditer(output):
        result[match.group(1)] = set()
    return result


def check_v3() -> tuple[list[str], set[str]]:
    """V3: audit capstone axiom dependencies. Return (failures, observed union)."""
    failures: list[str] = []
    observed: set[str] = set()
    names = read_capstones()
    if not names:
        return (["capstones.txt lists no theorems (V3 has nothing to audit)"], observed)

    lines = ["import IsingModel", ""]
    lines += [f"#print axioms {name}" for name in names]
    source = "\n".join(lines) + "\n"

    TEMP_DIR.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", dir=str(TEMP_DIR), delete=False, encoding="utf-8"
    ) as handle:
        temp_path = Path(handle.name)
        handle.write(source)
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(temp_path)],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
        )
    finally:
        try:
            temp_path.unlink()
        except OSError:
            pass

    combined = proc.stdout + "\n" + proc.stderr

    # Hard-fail on unresolved identifiers (stale / misspelled capstone names).
    if re.search(r"unknown (identifier|constant)", combined):
        for match in re.finditer(r"unknown (?:identifier|constant) '([^']+)'", combined):
            failures.append(f"V3: unknown identifier `{match.group(1)}` in capstones.txt")
        if not failures:
            failures.append("V3: lean reported an unknown identifier (see output)")

    parsed = parse_axioms_output(combined)
    for name in names:
        if name not in parsed:
            failures.append(f"V3: no `#print axioms` result for `{name}`")
            continue
        axioms = parsed[name]
        observed |= axioms
        extra = axioms - ALLOWED_AXIOMS
        if extra:
            failures.append(
                f"V3: `{name}` depends on disallowed axioms {sorted(extra)}"
            )

    if proc.returncode != 0 and not failures:
        failures.append(
            "V3: `lake env lean` exited nonzero but produced no parsed failure; "
            f"raw output:\n{combined.strip()}"
        )
    return (failures, observed)


def lake_available() -> bool:
    """Return whether a ``lake`` executable is usable for the V3 check."""
    try:
        subprocess.run(
            ["lake", "--version"],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            check=False,
        )
        return True
    except (OSError, FileNotFoundError):
        return False


def main() -> int:
    """Run the audit gate and return the process exit code."""
    parser = argparse.ArgumentParser(description="IsingModel audit gate (V1-V3).")
    parser.add_argument(
        "--full",
        action="store_true",
        help="Require V3 (capstone axiom audit) via `lake env lean`.",
    )
    args = parser.parse_args()

    ok = True

    print("== V1: no `axiom` declarations under IsingModel/ ==")
    v1 = check_v1()
    if v1:
        ok = False
        print(f"FAIL: {len(v1)} axiom declaration(s) found:")
        for item in v1:
            print(f"  {item}")
    else:
        print("PASS")

    print("== V2: no sorry/admit/native_decide in library code ==")
    v2 = check_v2()
    if v2:
        ok = False
        print(f"FAIL: {len(v2)} occurrence(s) found:")
        for item in v2:
            print(f"  {item}")
    else:
        print("PASS")

    print("== V3: capstone axiom audit (#print axioms) ==")
    if args.full or lake_available():
        v3, observed = check_v3()
        if v3:
            ok = False
            print(f"FAIL: {len(v3)} problem(s):")
            for item in v3:
                print(f"  {item}")
        else:
            names = read_capstones()
            observed_str = "{" + ", ".join(sorted(observed)) + "}" if observed else "{}"
            print(
                f"PASS ({len(names)} capstones; every axiom set is a subset of "
                f"{{propext, Classical.choice, Quot.sound}}; observed union = {observed_str})"
            )
    else:
        print("SKIP: no `lake` env available (pass --full to require V3)")

    print()
    if ok:
        print("audit gate: PASS")
        return 0
    print("audit gate: FAIL")
    return 1


if __name__ == "__main__":
    sys.exit(main())
