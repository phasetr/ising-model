#!/usr/bin/env python3
"""Audit gate for the IsingModel Lean library (V1-V4).

Deterministic, dependency-free checks intended to run in CI (and, if wired,
from a git pre-push hook). Uses only the Python 3 standard library.

Checks
------
V1  No ``axiom`` declarations in any checked Lean file. The project has no
    axiomatized targets, so the expected count is zero.
V2  No ``sorry`` / ``admit`` / ``native_decide`` in checked Lean code, after
    blanking comments and string literals. ``native_decide`` is exempt in the
    files listed in ``V2_NATIVE_DECIDE_FILE_ALLOWLIST`` and under the
    directories listed in ``V2_NATIVE_DECIDE_DIR_ALLOWLIST`` (executable
    sanity-check ``example``s); the exemption never covers ``sorry``/``admit``.

    "Checked" means every tracked Lean file the project owns
    (``iter_checked_files``): ``IsingModel/**/*.lean`` plus the umbrella
    ``IsingModel.lean`` and ``test/**/*.lean``. Restricting V1/V2 to the
    ``IsingModel/`` subdirectory used to leave the umbrella and the test suite
    entirely unchecked -- a ``sorry`` there would have been invisible.
V3  Capstone axiom audit. For every fully-qualified name in
    ``scripts/audit/capstones.txt`` the ``#print axioms`` output must be a
    subset of ``{propext, Classical.choice, Quot.sound}``. An unknown
    identifier is a hard failure (keeps the capstone list honest), and the list
    must hold at least :data:`CAPSTONE_MIN_COUNT` names -- a non-empty guard
    alone leaves "delete twelve of the thirteen lines" as a one-edit way to
    make V3 vacuous.
V4  No Japanese text (kana, CJK ideographs and radicals, CJK punctuation,
    enclosed and compatibility forms, vertical forms, fullwidth and halfwidth
    forms, ideographic variation selectors) in git-tracked files under the
    paths listed in ``V4_PATHS``. Committed sources, docs and TeX are
    English-only.
    The scope is delimited *by the ``V4_PATHS`` enumeration*, not by
    ``.gitignore``: internal working material such as ``.self-local/issues/``
    and ``.self-local/reports/`` **is** tracked and **does** contain Japanese
    on purpose, and is excluded only because ``V4_PATHS`` does not list it.
    Consequently ``V4_PATHS`` must never be widened to ``"."`` -- that would
    pull in ``.self-local/`` and fail immediately.

Usage
-----
    python3 scripts/audit_gate.py            # V1 + V2 + V4 always; V3 if lake env present
    python3 scripts/audit_gate.py --full     # V1 + V2 + V3 + V4 (V3 required; CI mode)
    python3 scripts/audit_gate.py --self-test  # test the gate itself (no lake needed)

Exit code 0 iff every executed check passes; 1 otherwise.

Scanned-set honesty
-------------------
V1, V2 and V4 each return the list of files they *actually opened*, not the list
their file enumeration produced, and :func:`main` requires the two to agree
(:func:`unvisited_failures`). Without that, a single ``continue`` in a check's
loop body -- ``if "RandomCurrent" in path.parts: continue`` -- removes a whole
subtree from the scan while the enumeration, every fixture test and the printed
"2063 files scanned" stay exactly as before. The count reported on a PASS line
is therefore the number of files read, so it can never overstate the coverage
the gate achieved.

The gate is only worth as much as its own tests: ``scripts/test_audit_gate.py``
pins each check against fixtures *and* mutates this file's detection logic to
prove that a weakened gate fails its tests instead of silently passing.
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

# Directories under which ``native_decide`` is exempt for the same reason, with
# no per-file upkeep: ``test/`` is nothing but executable sanity checks, and
# ``native_decide`` is how they evaluate. The exemption is again per-token --
# a ``sorry`` or ``admit`` in a test is still a V2 failure, which is the whole
# reason ``test/`` is scanned at all rather than left outside V1/V2.
V2_NATIVE_DECIDE_DIR_ALLOWLIST = ("test/",)

# The axioms every capstone is permitted to depend on (subset accepted).
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

# Ratchet on the size of ``capstones.txt``: V3 audits exactly the names listed
# there, so thinning the list is the cheapest way to disarm the check without
# touching a line of gate logic. The "list is non-empty" guard does not help --
# one surviving line passes it while twelve headline theorems stop being
# audited, and every fixture-driven V3 test stays green because each builds its
# own throwaway list. Set to the number of names currently tracked; removing a
# capstone therefore means lowering this constant on purpose, in the same
# commit, with a reason.
CAPSTONE_MIN_COUNT = 13

# Pathspecs scanned by V4 (English-only committed sources and public docs).
# ``IsingModel.lean`` (library umbrella), ``test``, ``.github`` and
# ``lakefile.toml`` are listed explicitly: they are tracked, English-only, and
# would otherwise be unscanned. Do NOT replace this list by ``"."`` -- see the
# module docstring (``.self-local/`` is tracked and intentionally Japanese).
#
# The last four entries are machine-managed (``.gitignore``, editor settings,
# the Lake manifest, the toolchain pin). They were added once measurement showed
# they cost nothing: zero hits for the whole Japanese class over all four. Being
# generated is not a reason to leave a tracked file unscanned -- a generated file
# is committed like any other, and an unscanned tracked file is exactly the
# fail-open hole V4 exists to close. With them the scope is stated positively:
# **every tracked file except ``.self-local/`` is scanned**, an invariant the
# test suite pins (``ScopeCoverageTest``), so a new top-level tracked path forces
# an explicit include/exclude decision instead of silently escaping the gate.
V4_PATHS = (
    "docs",
    "README.md",
    "tex",
    "IsingModel",
    "IsingModel.lean",
    "test",
    "scripts",
    ".github",
    "lakefile.toml",
    ".gitignore",
    ".vscode",
    "lake-manifest.json",
    "lean-toolchain",
)

# Tracked paths deliberately outside the V4 scope: internal working material
# that is Japanese on purpose. Used by the scope-coverage test, which requires
# every tracked file to be either scanned by V4 or listed here.
V4_UNSCANNED_PREFIXES = (".self-local/",)

# Full CJK/Japanese class. The narrow "kana + U+4E00-U+9FAF" class used by the
# manual ``rg`` spot check misses exactly the residue a Japanese-to-English
# rewrite tends to leave behind -- prolonged sound mark (U+30FC), ideographic
# comma/full stop (U+3001/U+3002), corner and fullwidth brackets, ideographic
# space (U+3000), fullwidth alphanumerics -- so V4 uses the wider ranges below:
#   U+2E80-U+303F  CJK radicals supplement, Kangxi radicals, ideographic
#                  description characters, CJK symbols and punctuation
#                  (includes the ideographic space U+3000)
#   U+3041-U+309F  hiragana (incl. U+3094 and the kana marks)
#   U+30A0-U+30FF  katakana (incl. U+30F4-U+30F6 and the prolonged sound mark)
#   U+3190-U+33FF  kanbun marks, katakana phonetic extensions, enclosed CJK
#                  letters and months, CJK compatibility (squared abbreviations
#                  and era names such as the ones a pasted Japanese table emits)
#   U+3400-U+4DBF  CJK unified ideographs extension A
#   U+4E00-U+9FFF  CJK unified ideographs (whole block, not just U+9FAF)
#   U+F900-U+FAFF  CJK compatibility ideographs
#   U+FE10-U+FE1F  vertical forms (vertical comma, full stop, brackets)
#   U+FE30-U+FE6F  CJK compatibility forms and small form variants
#   U+FF00-U+FFEF  halfwidth and fullwidth forms (halfwidth kana, fullwidth ASCII)
#   U+20000-U+2FFFF CJK unified ideographs extensions B and beyond
#   U+E0100-U+E01EF ideographic variation selectors (VS17-VS256)
# Measured on the current tree, per candidate range, over all tracked files under
# ``V4_PATHS``: every range above scores zero hits, so the wider class costs no
# false positive.
#
# Deliberately excluded: **U+FE00-U+FE0F (variation selectors VS1-VS16)**, also
# zero hits today. It is the one CJK-adjacent block with a non-CJK job:
# U+FE0F is the emoji presentation selector, and the tree already contains 35
# dingbats it could legitimately follow (checkmark U+2713, star U+2605), so the
# block trades a future false positive for no detection power -- a variation
# selector in Japanese text follows a base ideograph, which the ideograph ranges
# above already catch. U+E0100-U+E01EF has no such double duty (it only ever
# follows a CJK ideograph) and is kept so that an *orphaned* selector left behind
# by a Japanese-to-English rewrite -- invisible residue, exactly like U+3000 --
# still trips the gate. Bopomofo and Hangul (U+3100-U+318F) are out of scope:
# they are not Japanese and V4 is not a general non-Latin gate.
#
# The class is built from codepoints rather than spelled out with literal
# characters, so that this file passes its own check.
_JAPANESE_RANGES = (
    (0x2E80, 0x303F),
    (0x3041, 0x309F),
    (0x30A0, 0x30FF),
    (0x3190, 0x33FF),
    (0x3400, 0x4DBF),
    (0x4E00, 0x9FFF),
    (0xF900, 0xFAFF),
    (0xFE10, 0xFE1F),
    (0xFE30, 0xFE6F),
    (0xFF00, 0xFFEF),
    (0x20000, 0x2FFFF),
    (0xE0100, 0xE01EF),
)
_JAPANESE_RE = re.compile(
    "[" + "".join(f"{chr(lo)}-{chr(hi)}" for lo, hi in _JAPANESE_RANGES) + "]"
)


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
    """Return every ``*.lean`` file under ``IsingModel/`` (sorted).

    This is the *library* proper -- the set the capstone honesty check and
    ``dead_candidate_scan.py`` reason about. V1/V2 scan the wider
    ``iter_checked_files``.
    """
    return sorted(LIB_DIR.rglob("*.lean"))


# Lean sources owned by the project but outside ``IsingModel/``: the umbrella
# module, the test suite and the Lean helper the dead-candidate scanner runs.
# Kept as a named constant so that narrowing the V1/V2 scan is an edit to a
# pinned list rather than an invisible filter. Together with ``IsingModel/``
# these cover every tracked ``*.lean`` file, an invariant the test suite pins
# (``CheckedFilesTest``): a new Lean root forces an explicit decision instead of
# silently escaping V1 and V2.
EXTRA_CHECKED_ROOTS = ("IsingModel.lean", "test", "scripts/audit")


def iter_checked_files() -> list[Path]:
    """Return every ``*.lean`` file V1 and V2 scan (sorted, deduplicated).

    ``IsingModel/`` plus :data:`EXTRA_CHECKED_ROOTS`. A file is included by
    existence, never filtered by name or by parent directory: a filter is
    exactly how a directory silently drops out of the gate's field of view.
    """
    found = set(iter_lib_files())
    for name in EXTRA_CHECKED_ROOTS:
        root = REPO_ROOT / name
        if root.is_dir():
            found |= set(root.rglob("*.lean"))
        elif root.is_file() and root.suffix == ".lean":
            found.add(root)
    return sorted(found)


def rel(path: Path) -> str:
    """Return ``path`` relative to the repository root, POSIX style."""
    return path.relative_to(REPO_ROOT).as_posix()


# ``axiom`` command with any leading ``... in`` command wrappers, any leading
# attribute block and any combination of declaration modifiers (private /
# protected / noncomputable / unsafe / scoped[...] / local). Applied to
# comment/string-stripped text.
#
# Lean's ``in`` combinator is a *generic* ``trailing_parser`` -- in the compiler
# it is ``Command.«in» := trailing_parser withOpen (" in" >> commandParser)``
# (``Lean/Parser/Command.lean``), attaching ``in <command>`` after *any*
# preceding command. So a single line can prefix an ``axiom`` with a scoping
# command and its ``in`` continuation: ``open Nat in axiom bad : True``,
# ``set_option pp.all true in axiom bad : True``, ``omit [Inst] in axiom bad``
# (the ``omit`` form is idiomatic here -- dozens of files use it), and chains
# such as ``open Nat in set_option x true in axiom bad`` -- each still declares
# an axiom. Without the leading wrapper group these same-line forms slip past
# V1 entirely.
#
# Because ``in`` is generic, no finite keyword list is *exhaustive*; the wrapper
# alternation enumerates the seven scoping commands that idiomatically carry an
# ``in`` continuation onto a declaration (``open`` / ``set_option`` /
# ``variable`` / ``universe`` / ``include`` / ``omit`` / ``attribute``).
# Anchoring on those keywords keeps the group from firing on an ordinary
# declaration whose body merely contains the word ``in`` (``theorem in_axiom``
# starts with ``theorem``, not a wrapper keyword, and ``axiom`` inside an
# identifier such as ``myaxiom``/``axiomatic`` is excluded by the trailing
# ``\b``). A same-line ``in axiom`` behind some *other*, non-enumerated command
# is the residual heuristic gap tracked in issue #4653; measured on the current
# tree the wrapper group adds no false positive.
#
# The guard is ``(?!\bin\s)``, not ``(?!\bin\b)``: the delimiter is ``\bin\s+``
# (``in`` then whitespace), so the guard must key on that exact shape. A ``\bin\b``
# guard also fired when ``in`` appears *inside* the wrapper target followed by a
# non-word char -- an escaped identifier ``«in»`` or a dotted component
# ``Foo.in.Bar`` / option name ``foo.in.bar`` -- desynchronising the segment from
# the delimiter and dropping the whole wrapper (so ``open «in» in axiom`` slipped
# past). ``\bin\s`` skips those inner ``in`` tokens and stops only at the real
# delimiter. The one shape no *linear* guard can catch is a bare keyword ``in`` as
# the final namespace component (``open A.in in axiom``): its ``in`` *is* followed
# by whitespace, so ``A.in `` is identical to ``A.`` plus the ``in `` delimiter --
# but a bare keyword ``in`` is not a legal Lean identifier (it must be ``«in»``, and
# that form *is* caught), so ``open A.in in axiom`` is not valid Lean; it stays in
# the issue #4653 residual gap rather than justify a backtracking (ReDoS) rewrite.
#
# ReDoS note: each wrapper segment consumes ``(?!\bin\s)[^\n]`` -- any char that
# does *not* start the ``in`` delimiter -- so a segment stops at the first
# ``in`` and the partition into segments is unique. That removes the ambiguity
# an inner ``[^\n]*?`` had inside the outer ``(...)*``, which backtracked
# catastrophically on a wrapper-prefixed line that never reaches ``axiom``
# (``open Foo in`` repeated: ~0.4 s at 20 copies, unbounded beyond). Python 3.9
# has no atomic groups / possessive quantifiers, so the guarded char class is
# the linear form; ``test_audit_gate`` pins a bounded match time on such input.
_AXIOM_RE = re.compile(
    r"^\s*"
    r"(?:(?:open|set_option|variable|universe|include|omit|attribute)\b"
    r"(?:(?!\bin\s)[^\n])*\bin\s+)*"
    r"(?:@\[[^\]]*\]\s*)?"
    r"(?:(?:private|protected|noncomputable|unsafe)\s+"
    r"|(?:scoped|local)(?:\s*\[[^\]]*\])?\s+)*"
    r"axiom\b"
)


def check_v1() -> tuple[list[str], list[Path]]:
    """V1: report ``axiom`` declarations. Return (failures, files visited).

    The second component is the honesty half of the check: it is built inside
    the loop, so it shrinks with any filter added to the loop body, whereas
    ``iter_checked_files()`` would not (see the module docstring).
    """
    failures: list[str] = []
    visited: list[Path] = []
    checked = iter_checked_files()
    if not checked:
        # Fail-closed: an empty scan set (a broken checkout, a mis-set path)
        # would otherwise return ``([], [])`` and turn V1 green with nothing
        # examined. Mirrors the "nothing to scan" guard in ``iter_v4_files``.
        return (["V1: iter_checked_files() found no Lean file (nothing to scan)"], visited)
    for path in checked:
        visited.append(path)
        text = strip_noncode(path.read_text(encoding="utf-8"))
        for lineno, line in enumerate(text.splitlines(), start=1):
            if _AXIOM_RE.match(line):
                failures.append(f"{rel(path)}:{lineno}: axiom declaration")
    return (failures, visited)


def check_v2() -> tuple[list[str], list[Path]]:
    """V2: report ``sorry``/``admit``/``native_decide``. Return (failures, visited)."""
    failures: list[str] = []
    visited: list[Path] = []
    tokens = ("sorry", "admit", "native_decide")
    word_res = {tok: re.compile(rf"\b{re.escape(tok)}\b") for tok in tokens}
    checked = iter_checked_files()
    if not checked:
        # Fail-closed, as in ``check_v1``: no file to scan is a broken gate, not
        # a clean tree.
        return (["V2: iter_checked_files() found no Lean file (nothing to scan)"], visited)
    for path in checked:
        visited.append(path)
        relpath = rel(path)
        exempt = relpath in V2_NATIVE_DECIDE_FILE_ALLOWLIST or relpath.startswith(
            V2_NATIVE_DECIDE_DIR_ALLOWLIST
        )
        cleaned = strip_noncode(path.read_text(encoding="utf-8"))
        for lineno, line in enumerate(cleaned.splitlines(), start=1):
            for tok in tokens:
                if not word_res[tok].search(line):
                    continue
                if tok == "native_decide" and exempt:
                    continue
                failures.append(f"{relpath}:{lineno}: `{tok}`")
    return (failures, visited)


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
    # Fail-closed on duplicates: the count ratchet counts *lines*, so a name
    # repeated CAPSTONE_MIN_COUNT times would clear it while V3 audits a single
    # theorem CAPSTONE_MIN_COUNT times. A duplicate is unambiguously a config
    # mistake, so reject it outright rather than let it inflate the count.
    duplicates = sorted({name for name in names if names.count(name) > 1})
    if duplicates:
        return (
            [
                f"V3: capstones.txt has duplicate name(s) {duplicates}; each capstone "
                "must be listed once (duplicates fake the count ratchet)"
            ],
            observed,
        )
    if len(names) < CAPSTONE_MIN_COUNT:
        failures.append(
            f"V3: capstones.txt lists {len(names)} theorem(s), below the ratchet of "
            f"{CAPSTONE_MIN_COUNT} (lower CAPSTONE_MIN_COUNT deliberately to retire one)"
        )

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


def iter_v4_files() -> tuple[list[Path], list[str]]:
    """Return (tracked files under ``V4_PATHS``, hard failures) for V4.

    ``git ls-files`` is what makes the exclusion list self-maintaining: only
    committed material under ``V4_PATHS`` is scanned, so untracked scratch files
    never trip the gate and the list stays in sync with the repository. A ``git``
    invocation that fails -- or a ``git`` that is not installed at all -- is
    reported as a failure rather than silently yielding an empty file list
    (fail-closed; mirrors the guard in ``lake_available``).
    """
    try:
        proc = subprocess.run(
            ["git", "ls-files", "-z", "--", *V4_PATHS],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError as exc:  # FileNotFoundError included: no usable `git`.
        return ([], [f"V4: could not run `git ls-files`: {exc}"])
    if proc.returncode != 0:
        return ([], [f"V4: `git ls-files` failed: {proc.stderr.strip()}"])
    paths = [REPO_ROOT / name for name in proc.stdout.split("\0") if name]
    if not paths:
        return ([], ["V4: `git ls-files` matched no file (V4 has nothing to scan)"])
    return (sorted(paths), [])


def check_v4() -> tuple[list[str], list[Path]]:
    """V4: report Japanese text in tracked sources/docs. Return (failures, visited).

    A file that cannot be read or decoded is reported as a failure instead of
    being skipped. Everything tracked under ``V4_PATHS`` is text today, so an
    unreadable file means either a broken working tree or a newly committed
    binary; both deserve an explicit decision (adjust ``V4_PATHS``) rather than
    a silent unscanned file counted as "scanned". Skipping is the fail-open
    variant this gate exists to avoid; an extension allowlist was rejected
    because it would need per-file upkeep (``docs/Gemfile`` has no suffix).

    ``visited`` records the files the scan actually *processed*, not the ones it
    *opened*: a file counts as visited only after its content has been read and
    run through the line scan (the two failure arms count too -- reporting a
    read failure is itself a decision reached about the file). Recording at the
    open, as an earlier version did, left a hole: ``if path.suffix == ".json":
    continue`` placed *after* the record satisfied the coverage check while the
    file's content was never examined. Recording only once the whole-file scan
    is complete closes *that* class of skip: a per-file ``continue`` in the
    loop body (before the ``visited.append`` below) drops the file out of
    ``visited`` and ``unvisited_failures`` turns the gap into a failure.

    This guard is not total. A ``continue`` in the *inner* ``for lineno, line``
    loop skips the rest of a file's lines yet still falls through to the
    ``visited.append`` below, so a content-skip nested one level deeper would
    not be caught here (tracked as a known limitation in issue #4653). The
    coverage check defends the outer, per-file loop, where filters are the
    plausible regression.
    """
    paths, failures = iter_v4_files()
    visited: list[Path] = []
    for path in paths:
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            visited.append(path)
            failures.append(f"{rel(path)}: not valid UTF-8 text (cannot be scanned)")
            continue
        except OSError as exc:
            visited.append(path)
            failures.append(f"{rel(path)}: could not be read ({exc})")
            continue
        for lineno, line in enumerate(text.splitlines(), start=1):
            hits = _JAPANESE_RE.findall(line)
            if not hits:
                continue
            snippet = line.strip()
            if len(snippet) > 80:
                snippet = snippet[:80] + "..."
            failures.append(
                f"{rel(path)}:{lineno}: Japanese text {''.join(dict.fromkeys(hits))!r}"
                f" in: {snippet}"
            )
        # Recorded only here, once the whole file has been scanned: a
        # content-skip ``continue`` inserted anywhere above never reaches this.
        visited.append(path)
    return (failures, visited)


def unvisited_failures(label: str, expected: list[Path], visited: list[Path]) -> list[str]:
    """Report the gap between the files a check was given and the ones it read.

    Every check enumerates its files and then loops over them, and the two are
    only the same set as long as the loop body contains no filter. Comparing
    them turns "the check quietly stopped looking at a directory" -- invisible
    to every fixture test, and to a report that prints the *enumeration* size --
    into an ordinary gate failure.
    """
    missed = sorted(set(expected) - set(visited))
    extra = sorted(set(visited) - set(expected))
    out = [f"{label}: enumerated but never scanned: {rel(path)}" for path in missed]
    out += [f"{label}: scanned outside its own file list: {rel(path)}" for path in extra]
    return out


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
    parser = argparse.ArgumentParser(description="IsingModel audit gate (V1-V4).")
    parser.add_argument(
        "--full",
        action="store_true",
        help="Require V3 (capstone axiom audit) via `lake env lean`.",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="Run the gate's own test suite (scripts/test_audit_gate.py).",
    )
    args = parser.parse_args()

    if args.self_test:
        sys.path.insert(0, str(Path(__file__).resolve().parent))
        from test_audit_gate import run_suite  # noqa: PLC0415

        return run_suite()

    ok = True
    # Printed with the V1/V2 verdicts: a pass over a shrunken file set is not a
    # pass, so the coverage the gate actually achieved is part of the report --
    # and it is measured from what each check read, never from the enumeration.
    checked = iter_checked_files()

    print("== V1: no `axiom` declarations in checked Lean files ==")
    v1, v1_visited = check_v1()
    v1 += unvisited_failures("V1", checked, v1_visited)
    if v1:
        ok = False
        print(f"FAIL: {len(v1)} axiom declaration(s) found:")
        for item in v1:
            print(f"  {item}")
    else:
        print(f"PASS ({len(v1_visited)} Lean files scanned)")

    print("== V2: no sorry/admit/native_decide in checked Lean files ==")
    v2, v2_visited = check_v2()
    v2 += unvisited_failures("V2", checked, v2_visited)
    if v2:
        ok = False
        print(f"FAIL: {len(v2)} occurrence(s) found:")
        for item in v2:
            print(f"  {item}")
    else:
        print(f"PASS ({len(v2_visited)} Lean files scanned)")

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

    print("== V4: no Japanese text in tracked sources and public docs ==")
    v4, v4_visited = check_v4()
    v4 += unvisited_failures("V4", iter_v4_files()[0], v4_visited)
    if v4:
        ok = False
        # Not necessarily "N lines with Japanese": the list may also hold
        # git-level or unreadable-file failures, which are not line reports.
        print(f"FAIL: {len(v4)} problem(s) (Japanese text and/or scan errors):")
        for item in v4:
            print(f"  {item}")
    else:
        print(f"PASS ({len(v4_visited)} tracked files under {', '.join(V4_PATHS)})")

    print()
    if ok:
        print("audit gate: PASS")
        return 0
    print("audit gate: FAIL")
    return 1


if __name__ == "__main__":
    sys.exit(main())
