#!/usr/bin/env python3
"""Deletion-candidate safety scanner for the IsingModel Lean library.

Answers one question, mechanically and reproducibly: *is it safe to delete
these declarations?* It is a pre-flight for a destructive operation, not a
health gate, so it lives outside ``audit_gate.py`` (whose V1-V4 run on every
push and must stay sub-second) while **importing** that module's validated
primitives -- ``strip_noncode``, ``read_capstones``, ``REPO_ROOT``, ``LIB_DIR``,
``rel`` -- so the repository keeps a single comment/string stripper.

Why the tool exists
-------------------
Three deletion sweeps in a row mis-classified live declarations as dead. Both
symptoms had one cause: every sweep re-implemented its own ad-hoc name matcher.

* An ASCII token class ``[A-Za-z_][A-Za-z0-9_']*`` splits ``freeEnergyLambda``
  spelled with a real ``U+039B`` at the Greek letter, so the declaration key and
  the reference key break *differently* and a live lemma looks reference-zero.
* ``tex/proof-guide.tex`` spells names with ``\\_`` and ``$\\Lambda$`` /
  ``\\(\\Lambda\\)``, so a plain fixed-string search misses essentially every
  published result whose name carries a Greek letter.

Two architectural decisions follow, and they are the whole design:

1. **The candidate name is never tokenized.** Occurrences are found by a
   fixed-string search for the name plus a boundary predicate on the two
   adjacent characters. A tokenizer bug can then never make a name fail to
   match itself.
2. **The documentation channel is a first-class input.** Reference-zero *from
   Lean* does not mean deletable: a declaration may be a published result cited
   by ``README.md``, any ``docs/**/*.md`` or ``tex/proof-guide.tex``. Reading
   only Lean rescues 7 of the 10 keepers of PR #4641; reading only docs rescues
   3; both are needed.

A third rule follows from the first two and is just as load-bearing:

3. **The delete-closure runs over the candidates that are actually deleted.**
   "Consumed only by another candidate" excuses a reference only if that other
   candidate really goes away. Candidates the run itself retains -- published,
   uncertain, attribute- or kind-driven -- are therefore removed from the delete
   set *before* the fixpoint, never after. Seeding the fixpoint with every
   candidate reports a lemma as safe because its only consumer is a lemma the
   same report tells you to keep: a false ``safe-to-delete``, which for a tool
   that authorises deletions is the only fatal error class.

4. **A documentation citation that cannot be read charges every candidate.** The
   LaTeX macro table is incomplete by construction, so the normaliser meets
   spans it cannot resolve. Counting them as coverage warnings is not enough: a
   warning that changes no verdict and no exit code leaves the tool fail-open
   exactly where it claims to be fail-closed. Each unreadable span is therefore
   charged to **every** candidate name, and those candidates come out
   ``uncertain``, never ``safe-to-delete``.

5. **The Markdown channel has the same failure mode, through backtick parity.**
   Code spans are paired positionally, so a single unbalanced backtick inverts
   the parity of the rest of its line: prose is read as a citation and the
   citations are read as prose, with nothing to warn about.
   ``docs/index.md:1809`` does exactly that (three backticks where two were
   meant), and none of its 218 tokens mentioned ``magnetizationAlongExhaustion``
   though the raw line names it six times. The repair is not to skip the line --
   that drops precisely the citations with no verbatim fallback -- but to re-read
   it without pairing (:func:`pairing_independent_tokens`), which is a superset
   of every pairing, and to report the defect
   (:func:`unpaired_backticks`). A fenced run is the same failure one level up
   and reaches further -- its grammar is unbounded, so an unbalanced run pairs
   with the next one anywhere in the file -- so a fenced match is credited with
   its two delimiters and never with its body, and an odd number of runs is
   reported as well (:func:`unbalanced_fence_run`).

   The channel is deliberately *charge-only*: no span may deny a candidate.
   Seven successive attempts to decide *which* names an unread span could not be
   citing produced seven fail-open leaks of one shape -- text the normaliser had
   not explained (a macro argument, a second word, the argument of an unbraced
   accent) was read as literal name evidence and refuted the very name the macro
   spelled, so the citation was charged to nobody and the name it hid fell out
   as ``safe-to-delete``. Refutation from partially read TeX is not robustly
   implementable, so :attr:`UnreadableSpan.refutes` is now ``False``
   unconditionally and the rule set it gated is gone. Over-charging costs
   ``uncertain`` verdicts and nothing else; on the real guide it costs nothing,
   since the guide leaves no unreadable span at all.

Boundary predicate
------------------
``is_id_rest`` mirrors Lean 4's ``isIdRest``/``isLetterLike``/``isSubScriptAlnum``
exactly (so ``Lambda``/``beta``/``sigma``/``R``/subscripts are identifier
characters while ``lambda``/``Pi``/``Sigma`` are not -- Lean reserves those).
The error directions are asymmetric and the invariant is therefore one-sided:

* class too **wide**  -> real matches rejected -> references under-counted ->
  **false safe-to-delete**. Catastrophic.
* class too **narrow** -> longer identifiers split -> references over-counted ->
  false load-bearing. Merely annoying.

**``is_id_rest`` must never be a proper superset of Lean's ``isIdRest``; when in
doubt, narrow it.**

Usage
-----
    python3 scripts/dead_candidate_scan.py NAMES_FILE [options]
    python3 scripts/dead_candidate_scan.py --name foo --name bar
    python3 scripts/dead_candidate_scan.py --pattern '_ferromagnetic$'
    python3 scripts/dead_candidate_scan.py --expect scripts/audit/dead_candidate_fixtures.tsv
    python3 scripts/dead_candidate_scan.py --self-test

Exit codes: ``0`` every candidate is ``safe-to-delete`` (or ``--report-only`` /
``--expect`` satisfied); ``1`` at least one candidate is not safe; ``2``
internal inconsistency (canary failure, escaped identifier, candidate/index
disagreement, unknown candidate name, unreadable file). **``2`` must never be
swallowed by a PR script.**
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from audit_gate import (  # noqa: E402  (path bootstrap must precede the import)
    LIB_DIR,
    REPO_ROOT,
    read_capstones,
    rel,
    strip_noncode,
)

FIXTURES_FILE = REPO_ROOT / "scripts" / "audit" / "dead_candidate_fixtures.tsv"
DOCS_DIR = REPO_ROOT / "docs"
README = REPO_ROOT / "README.md"
TEX_GUIDE = REPO_ROOT / "tex" / "proof-guide.tex"

# Verdicts, ordered by decreasing severity for reporting.
PUBLISHED = "published-result"
LOAD_BEARING = "load-bearing"
UNCERTAIN = "uncertain"
SAFE = "safe-to-delete"
VERDICT_ORDER = (PUBLISHED, LOAD_BEARING, UNCERTAIN, SAFE)

EXIT_OK = 0
EXIT_NOT_SAFE = 1
EXIT_INCONSISTENT = 2


class Inconsistency(Exception):
    """Raised for a condition that invalidates the scan itself (exit code 2)."""


# ---------------------------------------------------------------------------
# 1. Lean identifier character class
# ---------------------------------------------------------------------------

# ``Lean.isLetterLike``, transcribed line by line from the primary source of the
# toolchain this repository pins (``lean-toolchain`` = ``leanprover/lean4:v4.29.0``,
# ``src/lean/Init/Meta/Defs.lean:101-109``). Ranges are inclusive.
_LETTERLIKE_RANGES: tuple[tuple[int, int], ...] = (
    (0x03B1, 0x03C9),  # lower-case Greek (minus lambda)
    (0x0391, 0x03A9),  # upper-case Greek (minus Pi and Sigma)
    (0x03CA, 0x03FB),  # Coptic letters
    (0x1F00, 0x1FFE),  # polytonic Greek extended
    (0x2100, 0x214F),  # letterlike symbols (blackboard bold reals, naturals...)
    (0x1D49C, 0x1D59F),  # script / fraktur / double-struck Latin
    (0x00C0, 0x00FF),  # Latin-1 supplement letters (minus multiplication/division)
    (0x0100, 0x017F),  # Latin Extended-A
)

# Lean removes these five from the letterlike class. Three are reserved syntax
# (lower-case lambda is the binder, upper-case Pi and Sigma are the dependent-type
# keywords); the multiplication and division signs merely sit inside the Latin-1
# letter block. Keeping any of them would widen the class, and wide is the
# catastrophic direction (see the module docstring).
_LETTERLIKE_EXCLUDED = frozenset({0x03BB, 0x03A0, 0x03A3, 0x00D7, 0x00F7})

# ``Lean.isSubScriptAlnum`` (same source, lines 111-118). Note that Lean has *no*
# superscript range: an earlier table here admitted U+207F, which made the class a
# proper superset of Lean's -- the forbidden direction.
_SUBSCRIPT_RANGES: tuple[tuple[int, int], ...] = (
    (0x1D62, 0x1D6A),
    (0x2080, 0x2089),
    (0x2090, 0x209C),
    (0x2C7C, 0x2C7C),  # subscript j
)

_ID_PUNCT = frozenset("_'!?")


def _in_ranges(code: int, ranges: tuple[tuple[int, int], ...]) -> bool:
    """Return whether ``code`` lies in any inclusive range of ``ranges``."""
    return any(lo <= code <= hi for lo, hi in ranges)


def is_letter_like(char: str) -> bool:
    """Return whether ``char`` is in Lean's ``isLetterLike`` class."""
    code = ord(char)
    if code in _LETTERLIKE_EXCLUDED:
        return False
    return _in_ranges(code, _LETTERLIKE_RANGES)


def is_id_rest(char: str) -> bool:
    """Return whether ``char`` may continue a Lean identifier.

    Mirrors ``Lean.isIdRest``: ASCII alphanumeric, ``_ ' ! ?``, letterlike, or
    subscript alphanumeric. Deliberately *not* ``str.isalnum()``, which is wider
    than Lean (it accepts the reserved Pi/Sigma/lambda and all CJK) and would
    therefore under-count references.
    """
    if "a" <= char <= "z" or "A" <= char <= "Z" or "0" <= char <= "9":
        return True
    if char in _ID_PUNCT:
        return True
    if is_letter_like(char):
        return True
    return _in_ranges(ord(char), _SUBSCRIPT_RANGES)


def is_id_first(char: str) -> bool:
    """Return whether ``char`` may start a Lean identifier (``Lean.isIdFirst``)."""
    if "a" <= char <= "z" or "A" <= char <= "Z" or char == "_":
        return True
    return is_letter_like(char)


# ---------------------------------------------------------------------------
# 2. Boundary-checked fixed-string search (authoritative matcher)
# ---------------------------------------------------------------------------

# Context of a match, read from the character to its left.
CTX_PLAIN = "plain"  # not preceded by an identifier character or a dot
CTX_DOTTED = "dotted"  # preceded by ``prefix.``


def find_occurrences(text: str, needle: str) -> list[tuple[int, str, str]]:
    """Return boundary-checked occurrences of ``needle`` in ``text``.

    Each entry is ``(index, context, dotted_prefix)`` where ``context`` is
    :data:`CTX_PLAIN` or :data:`CTX_DOTTED` and ``dotted_prefix`` is the maximal
    dotted identifier prefix immediately left of the match (empty when plain).

    The needle is used verbatim -- never split -- so no tokenizer defect can
    prevent a name from matching itself. Only the two adjacent characters are
    classified. A dot on either side is accepted: on the left it is namespace
    qualification (or a projection, resolved by the caller), on the right it is
    a projection applied to a reference.
    """
    if not needle:
        raise Inconsistency("empty candidate name")
    out: list[tuple[int, str, str]] = []
    size = len(needle)
    start = 0
    while True:
        idx = text.find(needle, start)
        if idx < 0:
            return out
        start = idx + 1
        end = idx + size
        if end < len(text) and is_id_rest(text[end]):
            continue  # part of a longer identifier
        if idx > 0:
            left = text[idx - 1]
            if left == ".":
                prefix_start = idx - 1
                while prefix_start > 0 and (
                    is_id_rest(text[prefix_start - 1]) or text[prefix_start - 1] == "."
                ):
                    prefix_start -= 1
                out.append((idx, CTX_DOTTED, text[prefix_start : idx - 1]))
                continue
            if is_id_rest(left):
                continue  # part of a longer identifier
        out.append((idx, CTX_PLAIN, ""))


_NEWLINE_RE = re.compile("\n")


def line_starts(text: str) -> list[int]:
    """Return the character offset of the start of every line of ``text``."""
    starts = [0]
    starts.extend(match.end() for match in _NEWLINE_RE.finditer(text))
    return starts


def offset_to_line(starts: list[int], offset: int) -> int:
    """Return the 1-based line number of ``offset`` given ``starts``."""
    lo, hi = 0, len(starts) - 1
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if starts[mid] <= offset:
            lo = mid
        else:
            hi = mid - 1
    return lo + 1


# ---------------------------------------------------------------------------
# 3. Declaration extraction
# ---------------------------------------------------------------------------

DECL_KINDS = (
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "instance",
    "structure",
    "class",
    "inductive",
    "example",
)
# Kinds whose deletion changes the surface API rather than only a proof: forced
# out of ``safe-to-delete`` because this tool is aimed at dead *lemmas*.
SURFACE_KINDS = frozenset({"structure", "class", "inductive", "abbrev", "def", "instance"})

# Attributes that make a declaration reachable by *tactics* rather than by name.
# A text scan structurally cannot see such a use, so they force load-bearing.
TACTIC_ATTRS = (
    "simp",
    "instance",
    "ext",
    "norm_cast",
    "push_cast",
    "fun_prop",
    "aesop",
    "gcongr",
    "elab_as_elim",
    "continuity",
    "measurability",
    "positivity",
    "bound",
    "refl",
    "symm",
    "trans",
)

_MODIFIERS = r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+|(?:scoped|local)(?:\s*\[[^\]]*\])?\s+)*"
_DECL_HEAD_RE = re.compile(
    r"^\s*" + _MODIFIERS + r"(" + "|".join(DECL_KINDS) + r")\b(.*)$",
)
_LEADING_WORD_RE = re.compile(r"[A-Za-z]+")
_HEAD_KEYWORDS = frozenset(DECL_KINDS) | {
    "private",
    "protected",
    "noncomputable",
    "unsafe",
    "partial",
    "scoped",
    "local",
    "namespace",
    "section",
    "end",
}
_NAMESPACE_RE = re.compile(r"^\s*namespace\s+([^\s]+)")
_END_RE = re.compile(r"^\s*end\b\s*([^\s]*)")
_SECTION_RE = re.compile(r"^\s*section\b\s*([^\s]*)")


@dataclass
class Decl:
    """A Lean declaration head extracted from a source file."""

    name: str  # final source name as written after the kind keyword
    full: str  # namespace-qualified name
    kind: str
    file: str  # repo-relative POSIX path
    line: int  # 1-based line of the kind keyword
    attrs: tuple[str, ...] = ()
    anonymous: bool = False

    @property
    def key(self) -> str:
        """Return the identity used throughout the graph (``file:line``-unique)."""
        return f"{self.full}@{self.file}:{self.line}"

    @property
    def final(self) -> str:
        """Return the last dot-component of the source name."""
        return self.name.rsplit(".", 1)[-1]


def _strip_name(rest: str) -> str:
    """Return the declaration name at the start of ``rest`` (may be empty)."""
    rest = rest.strip()
    if not rest:
        return ""
    if rest.startswith("«"):
        raise Inconsistency(
            "escaped identifier <<...>> found; the matcher does not model them"
        )
    out: list[str] = []
    for char in rest:
        if is_id_rest(char) or char == ".":
            out.append(char)
        else:
            break
    name = "".join(out)
    if not name or not is_id_first(name[0]):
        return ""
    return name


def _parse_attr_names(inner: str) -> tuple[str, ...]:
    """Return the attribute names listed inside an ``@[...]`` block."""
    out: list[str] = []
    for chunk in re.split(r"[,\s]+", inner):
        chunk = chunk.strip()
        if not chunk:
            continue
        name = re.split(r"[\s(\[]", chunk)[0].lstrip("↓↑←→")
        if name:
            out.append(name)
    return tuple(out)


def _scan_bracket(text: str, depth: int) -> tuple[str, str | None, int]:
    """Split ``text`` where a bracket nesting already ``depth`` deep closes.

    Returns ``(consumed, remainder, depth)``. ``remainder`` is ``None`` when the
    block is still open at the end of ``text``; otherwise it is everything after
    the closing ``]`` -- which is where ``@[simp] theorem foo`` keeps its
    declaration, so it must be parsed rather than discarded.
    """
    for idx, char in enumerate(text):
        if char == "[":
            depth += 1
        elif char == "]":
            depth -= 1
            if depth == 0:
                return text[:idx], text[idx + 1 :], 0
    return text, None, depth


def extract_decls(path: Path, cleaned: str) -> list[Decl]:
    """Return the declarations of ``cleaned`` (comment-stripped source of ``path``).

    Handles: leading ``@[...]`` attribute blocks (possibly multi-line), the
    modifier prefixes, and -- the trap that manufactured fake consumers in an
    earlier sweep -- a declaration **name on the line after the keyword**.
    Anonymous ``instance``/``example`` heads are recorded as unnamed owners:
    they consume references even though nothing can reference them.

    An attribute block is *consumed*, not skipped: ``@[simp] theorem foo ...``
    declares ``foo`` on the attribute line, and dropping the rest of the line
    would erase ``foo`` from the declaration table -- which silently re-attributes
    its body to the *preceding* declaration and turns its references into
    self-references.
    """
    relpath = rel(path)
    lines = cleaned.splitlines()
    decls: list[Decl] = []
    stack: list[str] = []  # namespace / section scopes ("" for anonymous sections)
    pending_attrs: list[str] = []
    attr_depth = 0
    attr_inner = ""  # text accumulated inside a still-open attribute block
    for idx, raw in enumerate(lines):
        lineno = idx + 1
        if attr_depth > 0:
            consumed, remainder, attr_depth = _scan_bracket(raw, attr_depth)
            attr_inner += " " + consumed
            if remainder is None:
                continue
            pending_attrs.extend(_parse_attr_names(attr_inner))
            attr_inner = ""
            raw = remainder
        stripped = raw.lstrip()
        while stripped.startswith("@["):
            consumed, remainder, attr_depth = _scan_bracket(stripped[2:], 1)
            attr_inner += consumed
            if remainder is None:
                break
            pending_attrs.extend(_parse_attr_names(attr_inner))
            attr_inner = ""
            raw = remainder
            stripped = raw.lstrip()
        if attr_depth > 0 or not stripped:
            continue
        # Cheap pre-filter: only the structural keywords can start a declaration
        # or change the scope. Everything else is proof body, the bulk of the tree.
        word = _LEADING_WORD_RE.match(stripped)
        if word is None or word.group(0) not in _HEAD_KEYWORDS:
            pending_attrs = []
            continue
        ns_match = _NAMESPACE_RE.match(raw)
        if ns_match:
            stack.append(ns_match.group(1))
            pending_attrs = []
            continue
        sec_match = _SECTION_RE.match(raw)
        if sec_match:
            stack.append("")
            pending_attrs = []
            continue
        if _END_RE.match(raw):
            if stack:
                stack.pop()
            pending_attrs = []
            continue
        head = _DECL_HEAD_RE.match(raw)
        if not head:
            if raw.strip():
                pending_attrs = []
            continue
        kind, rest = head.group(1), head.group(2)
        name = _strip_name(rest)
        if not name:
            # The name may sit on the next non-blank line.
            for follow in lines[idx + 1 : idx + 4]:
                if follow.strip():
                    name = _strip_name(follow)
                    break
        anonymous = not name
        prefix = ".".join(part for part in stack if part)
        full = f"{prefix}.{name}" if prefix and name else (name or f"<anonymous>:{lineno}")
        decls.append(
            Decl(
                name=name,
                full=full,
                kind=kind,
                file=relpath,
                line=lineno,
                attrs=tuple(sorted(set(pending_attrs))),
                anonymous=anonymous,
            )
        )
        pending_attrs = []
    return decls


# ---------------------------------------------------------------------------
# 4. Source tree model
# ---------------------------------------------------------------------------


@dataclass
class SourceFile:
    """A scanned Lean file: cleaned text, line index and declaration spans."""

    path: Path
    relpath: str
    cleaned: str
    starts: list[int]
    decls: list[Decl]
    head_lines: list[int] = field(default_factory=list)
    prose: str = ""  # comments and string bodies, joined (see extract_prose)
    prose_regions: list[tuple[int, int, str]] = field(default_factory=list)

    def prose_site(self, offset: int) -> tuple[int, str]:
        """Return the ``(line, kind)`` of the prose region holding ``offset``."""
        lo, hi = 0, len(self.prose_regions) - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if self.prose_regions[mid][0] <= offset:
                lo = mid
            else:
                hi = mid - 1
        _start, line, kind = self.prose_regions[lo]
        return line, kind

    def owner_of(self, lineno: int) -> Decl | None:
        """Return the declaration owning ``lineno`` (greatest head line <= it)."""
        lo, hi = 0, len(self.head_lines) - 1
        if hi < 0 or self.head_lines[0] > lineno:
            return None
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if self.head_lines[mid] <= lineno:
                lo = mid
            else:
                hi = mid - 1
        return self.decls[lo]


# ``strip_noncode`` blanks comments and string bodies to spaces *in place*, so a
# run of spaces in the cleaned text whose raw text is *not* blank is exactly a
# region the code scanner cannot see. Recovering the prose from the mask rather
# than from a second comment tokenizer keeps the repository's single stripper
# single. The run may be a single space: newlines are preserved, so a line
# carrying one character inside a block comment blanks to exactly one space, and
# requiring two dropped such a line (and any one-character name on it) from the
# prose channel. Ordinary code spacing is blank in the raw text too and is
# discarded by the ``strip()`` guard below rather than by the run length.
_BLANK_RUN_RE = re.compile(r"[ ]+")
_PROSE_KINDS = (("/-!", "module docstring"), ("/--", "doc comment"), ("--", "comment"),
                ("/-", "comment"))


def extract_prose(
    raw: str, cleaned: str, starts: list[int]
) -> tuple[str, list[tuple[int, int, str]]]:
    """Return ``(joined prose, regions)`` for one source file.

    A region is ``(offset in the joined text, line in the file, kind)``. The
    prose channel is **informational only**: a name mentioned in a sibling
    module docstring is not a Lean reference, but deleting it leaves that
    docstring stale, which a deletion PR needs to know.
    """
    pieces: list[str] = []
    regions: list[tuple[int, int, str]] = []
    position = 0
    kind = "comment"
    for match in _BLANK_RUN_RE.finditer(cleaned):
        text = raw[match.start() : match.end()]
        if not text.strip():
            continue  # plain indentation, not a blanked region
        if match.start() > 0 and cleaned[match.start() - 1] == '"':
            kind = "string literal"
        else:
            for opener, label in _PROSE_KINDS:
                if text.lstrip().startswith(opener):
                    kind = label
                    break
        regions.append((position, offset_to_line(starts, match.start()), kind))
        pieces.append(text)
        position += len(text) + 1
    return "\n".join(pieces), regions


def iter_scan_files() -> list[Path]:
    """Return every Lean file whose references count: library plus tests."""
    paths = sorted(LIB_DIR.rglob("*.lean"))
    umbrella = REPO_ROOT / "IsingModel.lean"
    if umbrella.exists():
        paths.append(umbrella)
    test_dir = REPO_ROOT / "test"
    if test_dir.is_dir():
        paths.extend(sorted(test_dir.rglob("*.lean")))
    return paths


@dataclass
class Tree:
    """The parsed source tree: files, declarations and the global token index."""

    files: list[SourceFile]
    decls: list[Decl]
    by_final: dict[str, list[Decl]] = field(default_factory=dict)
    by_full: dict[str, list[Decl]] = field(default_factory=dict)
    index: dict[str, list[tuple[str, int]]] = field(default_factory=dict)
    graph: dict[str, set[str]] = field(default_factory=dict)
    by_path: dict[str, SourceFile] = field(default_factory=dict)
    finals: list[tuple[str, Decl]] = field(default_factory=list)

    def file_of(self, relpath: str) -> SourceFile | None:
        """Return the scanned file with the given repo-relative path."""
        return self.by_path.get(relpath)


def _id_char_class() -> str:
    """Return a regex character class for ``is_id_rest`` characters plus ``.``.

    Derived from the same range tables as :func:`is_id_rest` so the fast
    tokenizing route and the authoritative matcher cannot drift apart; the
    per-candidate cross-check of :func:`cross_check` then verifies the two agree
    on the actual tree.
    """
    ranges: list[tuple[int, int]] = [
        (ord("0"), ord("9")),
        (ord("A"), ord("Z")),
        (ord("a"), ord("z")),
    ]
    ranges += [(ord(c), ord(c)) for c in sorted(_ID_PUNCT) + ["."]]
    for lo, hi in _LETTERLIKE_RANGES + _SUBSCRIPT_RANGES:
        start = lo
        for excluded in sorted(_LETTERLIKE_EXCLUDED):
            if lo <= excluded <= hi:
                if excluded > start:
                    ranges.append((start, excluded - 1))
                start = excluded + 1
        if start <= hi:
            ranges.append((start, hi))
    parts = []
    for lo, hi in sorted(ranges):
        parts.append(re.escape(chr(lo)) if lo == hi else f"{re.escape(chr(lo))}-{re.escape(chr(hi))}")
    return "[" + "".join(parts) + "]+"


# Maximal runs of identifier characters and dots, for the advisory index.
_RUN_RE = re.compile(_id_char_class())


def _index_tokens(cleaned: str) -> list[tuple[str, int]]:
    """Return ``(component, offset)`` for every dot-component of every run.

    This is the *tokenizing* route, kept deliberately separate from the
    authoritative matcher of section 2 so the two can be cross-checked: for
    every candidate the two must agree, and a disagreement is a hard failure.
    """
    out: list[tuple[str, int]] = []
    for match in _RUN_RE.finditer(cleaned):
        pos = match.start()
        for part in match.group(0).split("."):
            if part:
                out.append((part, pos))
            pos += len(part) + 1
    return out


def load_tree(verbose: bool = False) -> Tree:
    """Parse the working tree: every Lean file whose references count."""
    sources: list[tuple[Path, str]] = []
    for path in iter_scan_files():
        try:
            sources.append((path, path.read_text(encoding="utf-8")))
        except OSError as exc:  # pragma: no cover - unreadable working tree
            raise Inconsistency(f"{rel(path)}: could not be read ({exc})") from exc
    return build_tree(sources, verbose=verbose)


def build_tree(sources: list[tuple[Path, str]], verbose: bool = False) -> Tree:
    """Build the tree from ``(path, text)`` pairs: strip, extract, index.

    Split from :func:`load_tree` so a test can run the *whole* pipeline --
    extraction, index, dependency graph, classification -- over a synthetic
    two-file tree, instead of unit-testing the pieces and hoping they compose.
    """
    files: list[SourceFile] = []
    decls: list[Decl] = []
    for path, raw in sources:
        if "«" in raw:
            raise Inconsistency(
                f"{rel(path)}: escaped identifier <<...>> found; "
                "the matcher does not model them"
            )
        cleaned = strip_noncode(raw)
        file_decls = extract_decls(path, cleaned)
        starts = line_starts(cleaned)
        prose, prose_regions = extract_prose(raw, cleaned, starts)
        source = SourceFile(
            path=path,
            relpath=rel(path),
            cleaned=cleaned,
            starts=starts,
            decls=file_decls,
            head_lines=[decl.line for decl in file_decls],
            prose=prose,
            prose_regions=prose_regions,
        )
        files.append(source)
        decls.extend(file_decls)

    tree = Tree(files=files, decls=decls)
    tree.by_path = {source.relpath: source for source in files}
    for decl in decls:
        if decl.anonymous:
            continue
        tree.by_final.setdefault(decl.final, []).append(decl)
        tree.by_full.setdefault(decl.full, []).append(decl)
        tree.finals.append((decl.final, decl))

    # One tokenizing pass builds both the advisory occurrence index and the
    # whole-tree dependency graph (used for capstone reachability and cascade).
    # Token offsets are increasing, so line and owner are tracked incrementally
    # rather than by a binary search per token.
    index: dict[str, list[tuple[str, int]]] = defaultdict(list)
    graph: dict[str, set[str]] = defaultdict(set)
    for source in files:
        starts = source.starts
        heads = source.head_lines
        line_idx = 0
        head_idx = -1
        file_key = f"<file>:{source.relpath}"
        keys = [decl.key for decl in source.decls]
        for token, offset in _index_tokens(source.cleaned):
            targets = tree.by_final.get(token)
            if not targets:
                continue
            index[token].append((source.relpath, offset))
            while line_idx + 1 < len(starts) and starts[line_idx + 1] <= offset:
                line_idx += 1
            lineno = line_idx + 1
            while head_idx + 1 < len(heads) and heads[head_idx + 1] <= lineno:
                head_idx += 1
            owner_key = keys[head_idx] if head_idx >= 0 else file_key
            bucket = graph[owner_key]
            for target in targets:
                if target.key != owner_key:
                    bucket.add(target.key)
    tree.index = dict(index)
    tree.graph = dict(graph)
    if verbose:
        print(
            f"parsed {len(files)} files, {len(decls)} declarations, "
            f"{len(tree.by_final)} distinct final components"
        )
    return tree


# ---------------------------------------------------------------------------
# 5. Occurrence scanning (authoritative) and the reference graph
# ---------------------------------------------------------------------------


@dataclass
class Occurrence:
    """One boundary-checked textual reference to a candidate."""

    file: str
    line: int
    context: str
    prefix: str
    owner: Decl | None
    snippet: str


def scan_name(tree: Tree, name: str) -> list[Occurrence]:
    """Return every boundary-checked occurrence of ``name`` in Lean sources.

    ``name`` is matched as written; if it is dotted, only the final component is
    searched and the dotted prefix is recorded, so namespace-qualified and bare
    references are both found.
    """
    needle = name.rsplit(".", 1)[-1]
    out: list[Occurrence] = []
    for source in tree.files:
        if needle not in source.cleaned:
            continue
        raw_lines = source.cleaned.splitlines()
        for offset, context, prefix in find_occurrences(source.cleaned, needle):
            lineno = offset_to_line(source.starts, offset)
            snippet = raw_lines[lineno - 1].strip() if lineno - 1 < len(raw_lines) else ""
            out.append(
                Occurrence(
                    file=source.relpath,
                    line=lineno,
                    context=context,
                    prefix=prefix,
                    owner=source.owner_of(lineno),
                    snippet=snippet[:120],
                )
            )
    return out


def scan_prose(tree: Tree, name: str) -> list[str]:
    """Return the comment / docstring sites that mention ``name``.

    Never a verdict input: prose is not a reference, and a lemma cited only by a
    sibling module's ``/-! ... -/`` header is still dead code. It is reported
    because the deletion PR has to update those headers -- a deletion that
    builds green can still leave the documentation lying.
    """
    needle = name.rsplit(".", 1)[-1]
    out: list[str] = []
    for source in tree.files:
        if needle not in source.prose:
            continue
        for offset, _context, _prefix in find_occurrences(source.prose, needle):
            line, kind = source.prose_site(offset)
            out.append(f"{source.relpath}:{line} ({kind})")
    return out


def index_occurrences(tree: Tree, name: str) -> set[tuple[str, int]]:
    """Return ``(file, line)`` occurrences of ``name`` according to the index."""
    needle = name.rsplit(".", 1)[-1]
    out: set[tuple[str, int]] = set()
    for relpath, offset in tree.index.get(needle, []):
        source = tree.file_of(relpath)
        if source is None:  # pragma: no cover - index is built from tree.files
            continue
        out.add((relpath, offset_to_line(source.starts, offset)))
    return out


def cross_check(tree: Tree, name: str, occs: list[Occurrence]) -> list[str]:
    """Return disagreements between the authoritative scan and the index."""
    authoritative = {(occ.file, occ.line) for occ in occs}
    advisory = index_occurrences(tree, name)
    problems: list[str] = []
    for item in sorted(advisory - authoritative):
        problems.append(f"index sees {name} at {item[0]}:{item[1]}, scan does not")
    for item in sorted(authoritative - advisory):
        problems.append(f"scan sees {name} at {item[0]}:{item[1]}, index does not")
    return problems


def build_dependency_graph(tree: Tree) -> dict[str, set[str]]:
    """Return ``decl key -> keys it references`` over the whole tree.

    Built from the advisory index during :func:`load_tree` (one tokenizing pass
    for the whole tree); used only for capstone reachability and cascade, never
    for a delete/keep verdict on its own.
    """
    return tree.graph


# ---------------------------------------------------------------------------
# 6. Documentation channel
# ---------------------------------------------------------------------------

# LaTeX math macros that spell an identifier character. Printed by --explain so
# the table's incompleteness is visible rather than silent.
TEX_MACROS: dict[str, str] = {
    r"\Lambda": "Λ",
    r"\Sigma": "Σ",
    r"\Gamma": "Γ",
    r"\Delta": "Δ",
    r"\Omega": "Ω",
    r"\Theta": "Θ",
    r"\Phi": "Φ",
    r"\Psi": "Ψ",
    r"\Pi": "Π",
    r"\alpha": "α",
    r"\beta": "β",
    r"\gamma": "γ",
    r"\delta": "δ",
    r"\epsilon": "ε",
    r"\varepsilon": "ε",
    r"\zeta": "ζ",
    r"\eta": "η",
    r"\theta": "θ",
    r"\vartheta": "θ",
    r"\iota": "ι",
    r"\kappa": "κ",
    r"\mu": "μ",
    r"\nu": "ν",
    r"\xi": "ξ",
    r"\rho": "ρ",
    r"\varrho": "ρ",
    r"\sigma": "σ",
    r"\tau": "τ",
    r"\upsilon": "υ",
    r"\phi": "φ",
    r"\varphi": "φ",
    r"\chi": "χ",
    r"\psi": "ψ",
    r"\omega": "ω",
    r"\mathbb{R}": "ℝ",
    r"\mathbb{N}": "ℕ",
    r"\mathbb{Z}": "ℤ",
    r"\mathbb{Q}": "ℚ",
    r"\mathbb{C}": "ℂ",
    # Text-mode subscripts: the guide spells ``le_div_iff₀`` this way.
    **{rf"\textsubscript{{{digit}}}": chr(0x2080 + digit) for digit in range(10)},
    # Repository-local macro (tex/proof-guide.tex:44): 139 occurrences, every
    # one of them inside a declaration name.
    r"\LeanLambda": "Λ",
    # Not identifier characters, but the guide writes type signatures inside code
    # citations, so without these the whole span is unreadable and every name it
    # could be citing is forced to `uncertain`.
    r"\to": "→",
    r"\langle": "⟨",
    r"\rangle": "⟩",
}

# ``\ensuremath`` selects math mode without changing the token it wraps, so it
# is *transparent* for name matching and must be removed before the macro table
# is consulted: the guide writes ``\texttt{fieldPolymerZ\ensuremath{\mathbb{C}}}``
# and reading it needs both stages (drop the wrapper, then spell ``ℂ``). Skipping
# stage one hid all 16 published ``...ℂ...`` results (20 citations) from the TeX
# channel entirely.
_TRANSPARENT_WRAPPERS = ("ensuremath",)
# The gap before the brace is matched with ``[ \t]*`` rather than ``\s*``: a
# newline swallowed here would join two source lines and shift every TeX line
# number reported after it.
_TRANSPARENT_RE = re.compile(
    r"\\(?:" + "|".join(_TRANSPARENT_WRAPPERS) + r")[ \t]*\{((?:[^{}]|\{[^{}]*\})*)\}"
)
# Unwrapping exposes an outer layer's braces, so it repeats to a fixpoint; the
# bound only stops a pathological input from spinning.
_MAX_UNWRAP_ROUNDS = 8

_TEX_COMMENT_RE = re.compile(r"(?<!\\)%.*")
_TEX_MATH_RE = re.compile(r"\$([^$\n]*)\$|\\\(((?:[^\\]|\\(?!\)))*)\\\)")
_TEX_CODE_CMDS = r"\\(?:texttt|verb|lstinline|mintinline)\s*\{"
# The body admits one level of nested braces, because the guide writes brace
# alternation *inside* code citations (``\texttt{magnetization\_{J,h}\_lattice}``).
# A body of ``[^{}]*`` made those spans fail to match at all: no token, and no
# coverage warning either, since the warning loop iterated over the same regex.
_TEXTTT_RE = re.compile(_TEX_CODE_CMDS + r"((?:[^{}]|\{[^{}]*\})*)\}")
_TEXTTT_CMD_RE = re.compile(_TEX_CODE_CMDS)


# Line-breaking hints are written *inside* long declaration names in the guide,
# so they must vanish before matching, not merely be tolerated.
_TEX_UNESCAPE = (
    # `\dots` inside a code citation is an ellipsis shorthand for a name prefix,
    # so it must survive as one rather than be dropped.
    (r"\dots", "..."),
    (r"\ldots", "..."),
    (r"\cdots", "..."),
    (r"\allowbreak", ""),
    (r"\linebreak", ""),
    (r"\-", ""),
    (r"\_", "_"),
    (r"\{", "{"),
    (r"\}", "}"),
    (r"\$", "$"),
    (r"\%", "%"),
    (r"\&", "&"),
    (r"\#", "#"),
    (r"\,", ""),
    (r"\;", ""),
    (r"\!", ""),
)


def _apply_macro(text: str, macro: str, replacement: str) -> str:
    """Replace one LaTeX macro, honouring TeX's space-gobbling rule.

    TeX discards the whitespace that follows a *control word* (``\\allowbreak
    neg`` typesets as ``neg``), so the whitespace must go with the macro;
    control symbols such as ``\\_`` gobble nothing.
    """
    if macro not in text:
        return text
    if macro[1:].isalpha():
        return re.sub(re.escape(macro) + r"(?![A-Za-z])[ \t]*", replacement, text)
    return text.replace(macro, replacement)


def _unwrap_transparent(text: str) -> str:
    """Return ``text`` with transparent wrappers such as ``\\ensuremath`` removed."""
    for _ in range(_MAX_UNWRAP_ROUNDS):
        unwrapped = _TRANSPARENT_RE.sub(lambda m: m.group(1), text)
        if unwrapped == text:
            break
        text = unwrapped
    return text


def _normalize_tex_body(text: str) -> str:
    """Return ``text`` with comments, math macros and LaTeX escapes resolved.

    ``\\texttt{...}`` wrappers are *kept*, so the caller can still tell which
    spans are code citations. Transparent wrappers are removed *before* the
    macro table runs, because the two compose (``\\ensuremath{\\mathbb{C}}``).
    """
    text = _TEX_COMMENT_RE.sub("", text)
    text = _unwrap_transparent(text)

    def _replace_math(match: re.Match[str]) -> str:
        body = match.group(1) if match.group(1) is not None else (match.group(2) or "")
        for macro, char in TEX_MACROS.items():
            body = _apply_macro(body, macro, char)
        return body

    text = _TEX_MATH_RE.sub(_replace_math, text)
    for macro, char in TEX_MACROS.items():
        text = _apply_macro(text, macro, char)
    for escaped, plain in _TEX_UNESCAPE:
        text = _apply_macro(text, escaped, plain)
    return text


def code_citation_spans(text: str) -> list[tuple[str, int]]:
    """Return ``(body, offset)`` for every code citation, nested ones included.

    ``\\texttt`` nests in the guide (a citation whose prose carries another
    citation), and the span regex consumes the outer one whole; recursing keeps
    the inner name visible instead of swallowing it with its wrapper.
    """
    out: list[tuple[str, int]] = []
    for match in _TEXTTT_RE.finditer(text):
        body = match.group(1)
        out.append((body, match.start()))
        if _TEXTTT_CMD_RE.search(body):
            base = match.start(1)
            out.extend((inner, base + offset) for inner, offset in code_citation_spans(body))
    return out


MACRO_RESIDUE = "unnormalised macro"
UNPARSABLE_BRACES = "unparsable braces"


@dataclass(frozen=True)
class UnreadableSpan:
    """A code citation the LaTeX normaliser could not fully read.

    It is both the coverage warning printed by every run *and* the object that
    makes coverage bite: the span is charged to every candidate name
    (:meth:`could_cite`), and every one of them is forced to ``uncertain``.
    Counting the span without that step left the tool fail-closed at the level
    of the *warning* and fail-open at the level of the *verdict*, which is the
    only level that authorises a deletion.
    """

    label: str
    line: int
    kind: str
    text: str  # the span as far as it could be read

    @property
    def refutes(self) -> bool:
        """Return ``False``: **no span may ever refute a candidate name**.

        The TeX channel is charge-only. Seven successive rule sets tried to
        decide which names a partially read span could *not* be citing, and each
        one opened a new fail-open face through the same move: material the
        normaliser had not explained was read as literal name evidence and
        refuted the name it actually spelled, so the citation was charged to
        nobody and the name it hid could come out `safe-to-delete`.

        The last of them is why the rules were dropped rather than extended
        again. Macro arguments were swallowed with their macro so that
        ``\\ensuremath{\\mathbb{X}}`` could not demand an ``X`` in the cited
        name -- but only *braced* arguments were, and the LaTeX-standard unbraced
        accent ``\\'e`` leaves its argument behind: ``\\texttt{caf\\'e\\_lemma}``
        read as ``caf`` + ``e`` + ``_lemma`` refuted ``café_lemma``. That span
        satisfied every precondition the rules had, so the leak was not in the
        rules but in the premise that partially read TeX can support a
        refutation at all.

        Charging every candidate can only produce `uncertain` verdicts, never a
        false `safe-to-delete`. On the real guide it costs nothing at all: the
        coverage warnings are zero, so no candidate is charged this way today.
        """
        return False

    @property
    def message(self) -> str:
        """Return the one-line warning as printed in the report."""
        detail = (
            "unbalanced or deeply nested braces"
            if self.kind == UNPARSABLE_BRACES
            else "no macro-table entry"
        )
        return (
            f"{self.label}:{self.line}: {self.kind} in a code citation "
            f"({detail}): {self.text[:60]!r}"
        )

    def could_cite(self, name: str) -> bool:
        """Return whether this span may be a citation of ``name`` -- always yes.

        ``name`` is accepted for the caller's benefit and deliberately unused:
        the span is charged to every candidate because it may not refute any
        (:attr:`refutes`). Anything narrower would have to read the material the
        normaliser failed to read, which is precisely what produced seven
        fail-open leaks.
        """
        return not self.refutes

    def could_cite_decl(self, decl: "Decl") -> bool:
        """Return whether this span may be a citation of ``decl``, under any spelling.

        The guide cites a result both bare (``foo``) and namespace-qualified
        (``IsingModel.Ambient.foo``); either spelling keeping the span alive is
        enough to charge it, since charging is what forces `uncertain`.
        """
        return self.could_cite(decl.final) or self.could_cite(decl.full)


def normalize_tex(text: str) -> tuple[str, list[UnreadableSpan]]:
    """Return ``(normalized text, unreadable spans)`` for a LaTeX source.

    ``tex/proof-guide.tex`` writes declaration names with ``\\_`` for the
    underscore and ``$\\Lambda$`` / ``\\(\\Lambda\\)`` for the Greek letter, so a
    raw fixed-string search finds *none* of the published results whose name
    carries one. Normalisation is therefore a precondition, not a nicety.

    Steps: drop comments, unwrap transparent wrappers, unescape LaTeX
    punctuation, replace math-mode Greek / blackboard macros by the characters
    they spell, unwrap ``\\texttt{...}``. Line structure is preserved so
    reported line numbers stay usable.

    The macro table is incomplete by construction, so every ``\\texttt{...}``
    span the normaliser could not fully read is **returned rather than dropped**,
    in two flavours: a body that still contains a backslash after normalisation
    (:data:`MACRO_RESIDUE`), and an opener whose body the span regex cannot parse
    at all (:data:`UNPARSABLE_BRACES`) -- counted independently of the span
    regex, so an unparsable citation cannot disappear between the two loops.
    Nested code citations are read recursively and therefore do not count as
    residue of their enclosing span. Prose outside ``\\texttt`` is not a name
    citation and is deliberately not reported.

    What makes this fail-closed is not the count but
    :meth:`UnreadableSpan.could_cite`: an unread span downgrades **every**
    candidate to ``uncertain``. A low count is evidence of coverage only in
    combination with that downgrade -- and only for citations that leave residue
    to charge. Three shapes leave none. A ``%`` comment inside a citation
    (``L7a``) and a bare line break inside one (``L7c``) both parse into a
    perfectly clean span, so there is nothing to charge, while the newline they
    keep hides the name from the literal search as well; a code wrapper the span
    grammar does not know (``L7b``) produces no span in the first place. The
    first two are kept out of the real guide by :func:`run_tex_canary`, which
    aborts the run if any citation body in the guide contains a line break at
    all.
    """
    partial = _normalize_tex_body(text)
    spans: list[UnreadableSpan] = []
    starts = line_starts(partial)
    parsed: set[int] = set()
    for body, offset in code_citation_spans(partial):
        parsed.add(offset)
        own = _TEXTTT_RE.sub(" ", body)  # nested citations are read on their own
        if "\\" in own:
            spans.append(
                UnreadableSpan(
                    label="tex",
                    line=offset_to_line(starts, offset),
                    kind=MACRO_RESIDUE,
                    text=own,
                )
            )
    for match in _TEXTTT_CMD_RE.finditer(partial):
        if match.start() in parsed:
            continue
        # The closing brace is by definition not locatable, so the span is
        # reported up to the end of its line.
        end = partial.find("\n", match.start())
        spans.append(
            UnreadableSpan(
                label="tex",
                line=offset_to_line(starts, match.start()),
                kind=UNPARSABLE_BRACES,
                text=partial[match.start() : end if end >= 0 else len(partial)],
            )
        )
    return _TEXTTT_RE.sub(lambda m: m.group(1), partial), spans


def tex_citation_line_breaks(text: str) -> tuple[int, list[tuple[int, str]]]:
    """Return ``(citations read, broken ones)`` for a LaTeX source.

    A *broken* citation is reported as ``(line, body)``.

    A citation whose body straddles a line break is the one shape the charging
    rule cannot reach: the span parses, so nothing is charged, and the name it
    spells is split by a newline, so no literal search finds it either. It is
    invisible to the whole TeX channel while the run still reports zero coverage
    warnings -- the fail-open direction. The check is therefore run against the
    real guide on every invocation (:func:`run_tex_canary`), not merely
    documented as a limitation.

    Both flavours are caught, because both leave the same newline behind: the
    line ending in ``%`` (which TeX splices, so the typeset name has no break)
    and the bare line break (which TeX turns into a space, so the typeset name
    is wrong as well).
    """
    partial = _normalize_tex_body(text)
    starts = line_starts(partial)
    spans = code_citation_spans(partial)
    broken = sorted(
        (offset_to_line(starts, offset), body) for body, offset in spans if "\n" in body
    )
    return len(spans), broken


_MD_TOKEN_RE = re.compile(r"`([^`\n]+)`|```(.*?)```", re.DOTALL)
_BACKTICK_RE = re.compile("`")
_FENCE_RUN_RE = re.compile("`{3,}")


def unpaired_backticks(text: str) -> dict[int, int]:
    """Return ``{line: count}`` for the backticks no code span could absorb.

    The Markdown grammar above pairs backticks *positionally*: the first opens a
    span, the second closes it, the third opens the next one. One unbalanced
    backtick therefore does not merely lose its own span -- it inverts the
    parity of everything that follows it, so real citations are read as prose
    and prose is read as citations, with no error anywhere.

    That is not hypothetical. ``docs/index.md:1809`` (one 52-186-character
    progress row) spells ``ContinuousOn`.continuousAt`` with three backticks
    where two were meant; from that column on, all six occurrences of
    ``magnetizationAlongExhaustion`` on the line sit *outside* every span the
    grammar sees, and the line's 218 tokens contain none of them. Lines 1200 and
    1201 hold the sibling shape, a code span opened on one line and closed on
    the next, which ``[^`\\n]+`` cannot match at all.

    A backtick left over after the scan is the signature of both. What counts as
    "left over" is deliberately narrow on the *exonerating* side. A well-formed
    span carries no backtick inside it (``[^`\\n]+`` forbids one), so covering
    the whole match exonerates nothing but its own two delimiters. A fenced
    match is not like that: its alternative is ``re.DOTALL`` and unbounded, so
    an unbalanced run pairs with the next run *anywhere in the file* and its
    body swallows every line in between. Covering the whole fenced match would
    therefore let the very match that hides a citation certify the citation's
    backticks as read::

        text = "start ```\\ncite `_alpha_gen` here\\nand `beta{,_two}_gen`\\nend ```\\n"

    Measured on that text, whole-match covering returns ``{}`` while both
    citations are gone: the fenced body is tokenized by whitespace, and
    :func:`_nameish` rejects the pieces that still carry a backtick, so neither
    shape -- and neither has a verbatim fallback -- reaches a verdict. A fenced
    match is therefore credited with its two delimiters only, and the backticks
    in its body are reported like any other, which is what makes
    :func:`_markdown_source` re-read those lines. A fenced block that
    legitimately quotes a backtick is charged too; the price is one coverage
    warning and a superset re-read, both keep-only, and that is the direction an
    approximation is allowed to err in.
    """
    covered: list[tuple[int, int]] = []
    for match in _MD_TOKEN_RE.finditer(text):
        if match.group(1) is not None:
            covered.append((match.start(), match.end()))
        else:  # fenced: the delimiters are read, the body is not vouched for
            covered.append((match.start(), match.start() + 3))
            covered.append((match.end() - 3, match.end()))
    starts = line_starts(text)
    out: dict[int, int] = {}
    index = 0
    for match in _BACKTICK_RE.finditer(text):
        offset = match.start()
        while index < len(covered) and covered[index][1] <= offset:
            index += 1
        if index < len(covered) and covered[index][0] <= offset < covered[index][1]:
            continue
        line = offset_to_line(starts, offset)
        out[line] = out.get(line, 0) + 1
    return out


def unbalanced_fence_run(text: str) -> int | None:
    """Return the line of the fence delimiter left without a partner, else ``None``.

    Runs of three or more backticks are paired positionally too, so an odd
    number of them leaves one run to open a block that the *next* run closes --
    possibly hundreds of lines later, possibly at what was meant to be the
    opener of a real block. The citations caught inside are recovered anyway
    (:func:`unpaired_backticks` charges the body of every fenced match), so this
    check adds no token; it names the structural defect so the Markdown gets
    repaired instead of the scan quietly reading half the file as one code
    block. Charge-only, like every other coverage warning: it never reaches a
    verdict or the exit code.

    The line reported is the last run's, the one positional pairing leaves over.
    """
    starts = line_starts(text)
    runs = [offset_to_line(starts, match.start()) for match in _FENCE_RUN_RE.finditer(text)]
    return runs[-1] if len(runs) % 2 else None


def pairing_independent_tokens(line: str) -> list[str]:
    """Return the name-shaped pieces of ``line``, ignoring backtick pairing.

    Every code-span body is a maximal backtick-free substring of its line (the
    grammar forbids a backtick inside a body), so splitting on backticks yields
    a **superset** of the bodies *any* pairing could produce -- the correct one
    included. That is what makes the recovery in :func:`_markdown_source`
    fail-closed rather than a second guess: on a line whose parity is broken it
    can add citations, never drop one, whichever way the parity ran.

    The price is prose read as a citation, and it is small by construction: a
    token only reaches a verdict if it carries ``{``, ``*``, ``..`` or a leading
    ``_``/``.`` (see :func:`_apply_doc_channel`), and every such token can only
    *keep* a candidate.
    """
    out: list[str] = []
    for chunk in line.split("`"):
        out.extend(_citation_tokens(chunk))
    return out


def _nameish(token: str) -> bool:
    """Return whether ``token`` could be a declaration name or a name pattern."""
    token = token.strip()
    if not token or " " in token:
        return False
    if not ("_" in token or "." in token):
        return False
    if token.endswith(".lean"):
        return False
    allowed = set("._{},*")
    return all(is_id_rest(char) or char in allowed for char in token)


def _brace_grouped_pieces(body: str) -> list[str]:
    """Split ``body`` on the whitespace *outside* braces, dropping the rest.

    Both documentation files write a brace alternation with the spacing of
    ordinary prose -- ``freeEnergyAlongExhaustion_latticeGraph_{continuousAt,
    differentiableAt}_{beta, field, J, joint}`` is one citation of eight results,
    not seven words. Splitting the body on every whitespace run (what
    :func:`_citation_tokens` did alone) cuts that citation at each comma-space,
    and the pieces are not names: ``..._{continuousAt`` has no closing brace, so
    :func:`expand_braces` finds no group and returns it verbatim, matching
    nothing; ``field,`` and ``J,`` carry no ``_`` and :func:`_nameish` drops
    them. The whole citation therefore reaches no verdict, and -- a brace
    shorthand having no verbatim fallback -- the eight results it names come out
    uncited. Measured on the scanned documentation at ``2380eb36``: 133 such
    name-shaped tokens (102 in ``docs/index.md``, 31 in ``tex/proof-guide.tex``),
    108 of which expand onto 307 real declarations, 160 of those declarations
    reading ``safe-to-delete`` in a whole-library sweep with this citation as
    their only one -- the fatal error class.

    Whitespace *inside* a brace group is layout, so it is dropped rather than
    split on; :func:`expand_braces` already strips each alternative, so the
    canonical token this returns expands exactly like its unspaced spelling.

    The result is **not** a replacement for the whitespace split but an addition
    to it (see :func:`_citation_tokens`), because brace depth is itself an
    approximation: a body with an unclosed ``{`` never returns to depth 0, so
    every later whitespace run would be swallowed and the plain names after it
    would be lost -- the fail-open direction. Taking both splits keeps the token
    list a superset of today's, and the documentation channel is add-only (every
    token can only charge a citation, never deny one), so a superset can only
    move a verdict towards ``uncertain``/``published-result``.
    """
    out: list[str] = []
    buf: list[str] = []
    depth = 0
    for char in body:
        if char == "{":
            depth += 1
        elif char == "}" and depth:
            depth -= 1
        if char.isspace():
            if depth == 0 and buf:
                out.append("".join(buf))
                buf = []
            continue
        buf.append(char)
    if buf:
        out.append("".join(buf))
    return out


def _citation_tokens(body: str) -> list[str]:
    """Return the name-shaped pieces of one citation body, punctuation trimmed.

    Both the raw piece and the trimmed one are tested, because either order
    alone loses a shape, silently. Testing *before* trimming rejects a brace
    shorthand that carries its sentence punctuation (`` `foo{,_bar}:` ``) on
    the colon; testing *only* after trimming rejects one whose only ``_``/``.``
    lived in that punctuation (`` `foo{,bar}.` ``). Neither failure warns -- the
    token just disappears -- and a brace or glob shorthand, unlike a complete
    name, has no verbatim search to fall back on. The trimmed form is what is
    kept: the punctuation is the prose's, not the name's.

    The body is cut twice: first on every whitespace run, which is what this
    function has always returned, then on the whitespace outside braces only
    (:func:`_brace_grouped_pieces`), whose tokens are *appended* when they are
    new. The output is therefore a superset of the previous one by construction,
    and a body whose braces carry no whitespace produces the same two lists and
    so is left byte-for-byte alone.
    """
    out: list[str] = []
    for piece in body.split():
        trimmed = piece.strip(",.;:()")
        if trimmed and (_nameish(piece) or _nameish(trimmed)):
            out.append(trimmed)
    seen = set(out)
    for piece in _brace_grouped_pieces(body):
        trimmed = piece.strip(",.;:()")
        if trimmed and trimmed not in seen and (_nameish(piece) or _nameish(trimmed)):
            seen.add(trimmed)
            out.append(trimmed)
    return out


@dataclass
class DocSource:
    """A normalised documentation file with its extracted citation tokens."""

    label: str
    text: str
    starts: list[int]
    tokens: list[tuple[str, int]]  # (token, line)
    unreadable: list[UnreadableSpan]  # coverage warnings *and* uncertainty triggers
    malformed: list[str] = field(default_factory=list)  # coverage warnings, already repaired


def markdown_sources() -> list[Path]:
    """Return every Markdown file whose citations count, in a stable order.

    ``docs/index.md`` is the progress index, but it is not the only Markdown
    that cites results: ``README.md`` cites
    ``ConvergenceRegion.derivativeLimit_on_window`` and ``docs/plans/`` cites
    modules and lemmas of a refactoring plan. Reading only the index made
    "no documentation citation" -- the sentence a ``safe-to-delete`` verdict
    prints -- a claim about one file while sounding like a claim about the
    documentation, so the whole set is read.
    """
    paths = sorted(DOCS_DIR.rglob("*.md")) if DOCS_DIR.exists() else []
    if README.exists():
        paths.insert(0, README)
    return paths


def require_documentation() -> None:
    """Abort unless every documentation channel the scan claims to read exists.

    A missing file is the fail-open direction, and silently so: with no
    ``README.md``, no ``docs/index.md`` or no guide, the corresponding channel
    contributes no token and no literal text, every citation living in it
    disappears, and the run still prints "no citation in the scanned
    documentation" -- the sentence that licenses a deletion -- with a clean bill
    of health. The three files are tracked, so their absence is never a normal
    state; it is a moved path, a truncated checkout or a bad rename, and each
    must stop the scan instead of quietly shrinking its evidence base.
    """
    required = (README, DOCS_DIR / "index.md", TEX_GUIDE)
    missing = [rel(path) for path in required if not path.is_file()]
    if missing:
        raise Inconsistency(
            "documentation source(s) missing, which would silence a whole citation "
            "channel without warning: " + ", ".join(missing)
        )


def _read_doc(path: Path) -> str:
    """Return the text of a documentation file, or abort if it cannot be read."""
    try:
        return path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:  # pragma: no cover - tracked files
        raise Inconsistency(f"{rel(path)}: could not be read ({exc})") from exc


def _markdown_source(path: Path) -> DocSource:
    """Return the citation tokens of one Markdown file (its code spans).

    A line whose backticks do not pair (:func:`unpaired_backticks`) is **not
    trusted and not dropped**: dropping it is the fail-open move, since the
    citations it hides are exactly the ones with no verbatim fallback (brace
    alternations, globs, elided suffixes). Its tokens are re-read with
    :func:`pairing_independent_tokens`, whose result is a superset of every
    pairing, and the defect is reported as a coverage warning so the Markdown
    itself gets repaired rather than silently worked around. The same holds
    inside a fenced block, whose body is vouched for by nobody; an odd number of
    fence delimiters is reported on top (:func:`unbalanced_fence_run`), because
    the run left over reads an arbitrary stretch of the file as one block body.
    """
    raw = _read_doc(path)
    label = rel(path)
    tokens: list[tuple[str, int]] = []
    starts = line_starts(raw)
    for match in _MD_TOKEN_RE.finditer(raw):
        body = match.group(1) if match.group(1) is not None else (match.group(2) or "")
        lineno = offset_to_line(starts, match.start())
        for token in _citation_tokens(body):
            tokens.append((token, lineno))
    malformed: list[str] = []
    lines = raw.split("\n")
    seen = set(tokens)
    for lineno, unpaired in sorted(unpaired_backticks(raw).items()):
        line = lines[lineno - 1] if lineno - 1 < len(lines) else ""
        recovered = 0
        for token in pairing_independent_tokens(line):
            if (token, lineno) not in seen:
                seen.add((token, lineno))
                tokens.append((token, lineno))
                recovered += 1
        malformed.append(
            f"{label}:{lineno}: {unpaired} of {line.count('`')} backtick(s) pair into "
            "no code span, so the code-span grammar mis-reads this line; its tokens "
            f"were re-read without pairing ({recovered} added). Repair the Markdown."
        )
    leftover = unbalanced_fence_run(raw)
    if leftover is not None:
        malformed.append(
            f"{label}:{leftover}: an odd number of fenced-block delimiters, so this "
            "run has no partner and the grammar pairs it with the next one anywhere "
            "in the file, reading every line in between as one block body. Repair "
            "the Markdown."
        )
    return DocSource(
        label=label,
        text=raw,
        starts=starts,
        tokens=tokens,
        unreadable=[],
        malformed=malformed,
    )


def load_docs() -> list[DocSource]:
    """Return the normalised documentation sources (Markdown plus proof-guide.tex)."""
    require_documentation()
    out: list[DocSource] = [_markdown_source(path) for path in markdown_sources()]
    raw = _read_doc(TEX_GUIDE)
    # Tokens are read from the *pre-unwrap* normalisation so the \texttt
    # delimiters still mark which spans are code citations.
    partial = _normalize_tex_body(raw)
    partial_starts = line_starts(partial)
    tokens = []
    for body, offset in code_citation_spans(partial):
        lineno = offset_to_line(partial_starts, offset)
        for token in _citation_tokens(body):
            tokens.append((token, lineno))
    text, unreadable = normalize_tex(raw)
    out.append(
        DocSource(
            label=rel(TEX_GUIDE),
            text=text,
            starts=line_starts(text),
            tokens=tokens,
            unreadable=unreadable,
        )
    )
    return out


def expand_braces(token: str) -> list[str]:
    """Expand ``a{,_b,_c}d`` into the concrete names it abbreviates.

    Both documentation files use brace alternation for families of theorem
    names (``correlation_convergent{,_h,_beta}``). Failing to expand it is a
    silent false-negative generator, so the product is expanded and matched
    exactly, with the same confidence as a verbatim citation.
    """
    match = re.search(r"\{([^{}]*)\}", token)
    if not match:
        return [token]
    alternatives = match.group(1).split(",")
    head, tail = token[: match.start()], token[match.end() :]
    out: list[str] = []
    for alt in alternatives:
        for rest in expand_braces(tail):
            out.append(head + alt.strip() + rest)
    return sorted(set(out))


def glob_to_regex(token: str) -> re.Pattern[str] | None:
    """Return an anchored regex for an ellipsis/glob citation, else ``None``."""
    if not re.search(r"\.\.\.|\*|\.\.", token):
        return None
    pieces = re.split(r"(\.\.\.|\.\.|\*)", token)
    if not any(piece and piece not in {"...", "..", "*"} for piece in pieces):
        return None  # a bare wildcard names everything and cites nothing
    pattern = "".join(
        ".*?" if piece in {"...", "..", "*"} else re.escape(piece) for piece in pieces
    )
    return re.compile("^" + pattern + "$", re.UNICODE)


# ---------------------------------------------------------------------------
# 7. Classification
# ---------------------------------------------------------------------------


@dataclass
class Verdict:
    """The full result for one candidate declaration."""

    name: str
    decl: Decl
    verdict: str = SAFE
    reasons: list[str] = field(default_factory=list)
    same_file: list[Occurrence] = field(default_factory=list)
    cross_file: list[Occurrence] = field(default_factory=list)
    test_refs: list[Occurrence] = field(default_factory=list)
    doc_citations: list[str] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)  # each note forces ``uncertain``
    info: list[str] = field(default_factory=list)  # reported, but never classifies
    witness: list[str] = field(default_factory=list)

    @property
    def consumers(self) -> list[Occurrence]:
        """Return every reference outside the declaration itself."""
        return self.same_file + self.cross_file + self.test_refs


def resolve_candidate(
    tree: Tree, name: str, allow_homonym: bool
) -> tuple[Decl, list[str], list[str]]:
    """Return the declaration a candidate name denotes, its notes and its info.

    A *note* forces ``uncertain``; *info* is reported but does not classify. An
    unknown name is a hard failure (exit code 2): a stale candidate list must
    never be silently reported as deletable.
    """
    notes: list[str] = []
    info: list[str] = []
    matches = tree.by_full.get(name) or []
    if not matches:
        matches = [decl for decl in tree.by_final.get(name.rsplit(".", 1)[-1], [])]
    if not matches:
        raise Inconsistency(f"unknown candidate name `{name}` (no declaration found)")
    if len(matches) > 1:
        listing = ", ".join(f"{d.full} ({d.file}:{d.line})" for d in matches)
        if not allow_homonym:
            notes.append(f"homonymous final component: {listing}")
        else:
            # The flag is documented as *permitting* a safe verdict, so it must
            # not leave behind a note that forces uncertain regardless.
            info.append(f"homonym allowed by --allow-homonym: {listing}")
    return matches[0], notes, info


def classify(
    tree: Tree,
    names: list[str],
    docs: list[DocSource],
    allow_homonym: bool,
) -> tuple[list[Verdict], list[str], dict[str, list[str]]]:
    """Classify every candidate. Return ``(verdicts, cascade, family_labels)``."""
    capstones = set(read_capstones())
    capstone_finals = {name.rsplit(".", 1)[-1] for name in capstones}

    verdicts: list[Verdict] = []
    candidate_keys: set[str] = set()
    problems: list[str] = []
    for name in names:
        decl, notes, info = resolve_candidate(tree, name, allow_homonym)
        verdict = Verdict(name=name, decl=decl)
        verdict.notes.extend(notes)
        verdict.info.extend(info)
        occs = scan_name(tree, decl.name)
        problems.extend(cross_check(tree, decl.name, occs))
        mentions = sorted(set(scan_prose(tree, decl.name)))
        if mentions:
            verdict.info.append(
                "mentioned in prose at "
                + ", ".join(mentions[:3])
                + (f" and {len(mentions) - 3} more site(s)" if len(mentions) > 3 else "")
                + " -- deleting it leaves that text stale"
            )
        for occ in occs:
            if occ.owner is not None and occ.owner.key == decl.key:
                continue  # the declaration itself (head or recursive use)
            if occ.owner is None:
                verdict.notes.append(
                    f"file-level reference at {occ.file}:{occ.line} (outside any declaration)"
                )
            if occ.owner is not None and occ.owner.anonymous:
                verdict.notes.append(
                    f"reference inside an anonymous {occ.owner.kind} "
                    f"at {occ.file}:{occ.line}"
                )
            if occ.context == CTX_DOTTED and not decl.full.endswith(
                f".{occ.prefix}.{decl.final}"
            ) and occ.prefix not in {"_root_"} and not decl.full.startswith(
                f"{occ.prefix}."
            ):
                verdict.notes.append(
                    f"dotted-ambiguous reference `{occ.prefix}.{decl.final}` "
                    f"at {occ.file}:{occ.line}"
                )
            if occ.file.startswith("test/"):
                verdict.test_refs.append(occ)
            elif occ.file == decl.file:
                verdict.same_file.append(occ)
            else:
                verdict.cross_file.append(occ)
        verdicts.append(verdict)
        candidate_keys.add(decl.key)

    if problems:
        raise Inconsistency(
            "authoritative scan and global index disagree:\n  "
            + "\n  ".join(sorted(problems))
        )

    # Documentation channel.
    family_labels: dict[str, list[str]] = {}
    _apply_doc_channel(tree, verdicts, docs, family_labels)

    graph = build_dependency_graph(tree)
    reverse: dict[str, set[str]] = defaultdict(set)
    for src, targets in graph.items():
        for target in targets:
            reverse[target].add(src)
    capstone_keys = {
        decl.key
        for decl in tree.decls
        if decl.full in capstones or (not decl.anonymous and decl.final in capstone_finals)
    }
    reachable = _capstone_closure(graph, capstone_keys)
    key_to_decl = {decl.key: decl for decl in tree.decls}
    keyed = {verdict.decl.key: verdict for verdict in verdicts}

    # Phase 1 -- the facts that do not depend on the candidate-set closure:
    # publication, tactic reachability, surface kind, and the notes that make a
    # candidate uncertain. Every one of them means the candidate is *kept*.
    published_reasons: dict[str, str] = {}
    static_load: dict[str, list[str]] = {key: [] for key in keyed}
    uncertain_keys: set[str] = set()
    for verdict in verdicts:
        decl = verdict.decl
        key = decl.key
        if decl.full in capstones or decl.final in capstone_finals:
            published_reasons[key] = "listed in scripts/audit/capstones.txt"
        elif any(cit.startswith("exact ") for cit in verdict.doc_citations):
            published_reasons[key] = "cited verbatim in the public documentation"
        reasons = static_load[key]
        if key in reachable:
            reasons.append("inside the dependency closure of a capstone")
        tactic = [attr for attr in decl.attrs if attr in TACTIC_ATTRS]
        if tactic or decl.kind == "instance":
            reasons.append(
                "consumed by tactics, not by name "
                f"(@[{', '.join(tactic) or 'instance'}])"
            )
        if decl.kind in SURFACE_KINDS:
            reasons.append(f"`{decl.kind}` deletion changes the surface, not only a proof")
        if verdict.notes or any(
            cit.startswith(("shorthand ", "module-cited ", "unreadable "))
            for cit in verdict.doc_citations
        ):
            uncertain_keys.add(key)

    # Phase 2 -- delete-closure fixpoint: the greatest subset of the candidates
    # that is closed under consumers. The closure is only sound over the
    # candidates that are actually going to be deleted, so the ones phase 1
    # already retained are removed *before* the fixpoint runs. Seeding it with
    # every candidate (as an earlier revision did) declared a candidate safe
    # because its only consumer was another candidate that the very same run
    # reported as a keeper -- a false safe-to-delete, the one fatal error class.
    deletable = {
        key
        for key in keyed
        if key not in published_reasons and not static_load[key] and key not in uncertain_keys
    }
    while True:
        drop = set()
        for key in deletable:
            for occ in keyed[key].consumers:
                owner_key = occ.owner.key if occ.owner else f"<file>:{occ.file}"
                if owner_key not in deletable:
                    drop.add(key)
                    break
        if not drop:
            break
        deletable -= drop

    # Phase 3 -- the verdict, in decreasing severity.
    for verdict in verdicts:
        decl = verdict.decl
        key = decl.key
        if key in published_reasons:
            verdict.verdict = PUBLISHED
            verdict.reasons.append(published_reasons[key])
            continue

        load_reasons: list[str] = []
        external = [
            occ
            for occ in verdict.consumers
            if (occ.owner.key if occ.owner else f"<file>:{occ.file}") not in deletable
        ]
        if external:
            load_reasons.append(f"{len(external)} reference(s) from outside the delete set")
        load_reasons.extend(static_load[key])
        if load_reasons:
            verdict.verdict = LOAD_BEARING
            verdict.reasons.extend(load_reasons)
            verdict.witness = _witness_path(verdict, reverse, key_to_decl, capstone_keys)
            continue

        if key in uncertain_keys:
            verdict.verdict = UNCERTAIN
            verdict.reasons.extend(verdict.notes)
            verdict.reasons.extend(
                cit for cit in verdict.doc_citations if not cit.startswith("exact ")
            )
            continue

        verdict.verdict = SAFE
        verdict.reasons.append(
            "no reference outside the delete set, no citation in the scanned "
            "documentation (README.md, docs/**/*.md, tex/proof-guide.tex)"
        )

    cascade = _cascade(tree, deletable, reverse, graph, key_to_decl)
    return verdicts, cascade, family_labels


def _capstone_closure(graph: dict[str, set[str]], roots: set[str]) -> set[str]:
    """Return every declaration reachable from ``roots`` along ``uses`` edges."""
    seen: set[str] = set()
    stack = list(roots)
    while stack:
        key = stack.pop()
        for target in graph.get(key, ()):
            if target not in seen:
                seen.add(target)
                stack.append(target)
    return seen


def _witness_path(
    verdict: Verdict,
    reverse: dict[str, set[str]],
    key_to_decl: dict[str, Decl],
    capstone_keys: set[str],
) -> list[str]:
    """Return the shortest consumer chain from the candidate up to a capstone.

    A reviewer refusing a deletion needs the chain candidate -> consumer ->
    published result, not merely "1 consumer".
    """
    start = verdict.decl.key
    if not capstone_keys:
        return []
    seen = {start}
    queue: list[list[str]] = [[start]]
    while queue:
        path = queue.pop(0)
        if len(path) > 6:
            return []
        head = path[-1]
        if head in capstone_keys and len(path) > 1:
            return [
                f"{key_to_decl[key].full} ({key_to_decl[key].file}:{key_to_decl[key].line})"
                for key in path
                if key in key_to_decl
            ]
        for consumer in sorted(reverse.get(head, ())):
            if consumer not in seen:
                seen.add(consumer)
                queue.append(path + [consumer])
    return []


def _cascade(
    tree: Tree,
    deletable: set[str],
    reverse: dict[str, set[str]],
    graph: dict[str, set[str]],
    key_to_decl: dict[str, Decl],
) -> list[str]:
    """Return declarations that become reference-zero because of the deletion.

    Reported, never auto-added to the delete set: each must be re-run through
    the full classifier, since a cascade member can easily be documentation-cited.
    """
    if not deletable:
        return []
    removed = set(deletable)
    out: list[str] = []
    depth = 1
    while True:  # a genuine fixpoint: each round strictly grows ``removed``
        front: list[str] = []
        for key, decl in key_to_decl.items():
            if key in removed or decl.anonymous:
                continue
            consumers = reverse.get(key, set())
            if consumers and consumers <= removed:
                front.append(key)
        if not front:
            break
        for key in sorted(front):
            decl = key_to_decl[key]
            out.append(f"depth {depth}: {decl.full} ({decl.file}:{decl.line})")
        removed |= set(front)
        depth += 1
    return out


def _resolve_fragment(
    tree: Tree, name: str, cache: dict[str, list[Decl] | None]
) -> list[Decl] | None:
    """Return the declarations a documentation *fragment* could denote.

    A fragment is a suffix (``_univ_zero_eq``) or a wildcard citation
    (``..._J_deriv_eq_le``, ``*_continuous_joint``). ``None`` means the fragment
    is unusable. Results are cached because documentation repeats the same
    family labels dozens of times.
    """
    if name in cache:
        return cache[name]
    pattern = glob_to_regex(name)
    matched: list[Decl] | None
    if pattern is not None:
        matched = [decl for final, decl in tree.finals if pattern.match(final)]
    elif name.startswith(("_", ".")):
        matched = [decl for final, decl in tree.finals if final.endswith(name)]
    else:
        matched = None
    cache[name] = matched
    return matched


def elided_prefix_matches(fragment: str, matched: list[Decl], cited: set[str]) -> list[Decl]:
    """Return the matches of a suffix ``fragment`` whose elided prefix is cited too.

    Both documentation files abbreviate a run of sibling results by writing the
    first one in full and eliding the shared prefix of the rest::

        `magnetizationAlongExhaustion_continuous_beta_gen` + `_differentiable_beta_gen`
        + `_continuous_field_gen` + ...

    Those suffixes are **not** family labels, but ``_differentiable_beta_gen``
    matches three declarations (correlation / magnetization / susceptibility),
    so the family-label rule attributed the citation to nobody and
    ``magnetizationAlongExhaustion_differentiable_beta_gen`` came out
    ``safe-to-delete`` while docs/index.md:1809 cited it -- a false
    ``safe-to-delete``, the one fatal error class.

    Charging *every* match instead was measured before it was rejected: 531 of
    the 759 distinct fragment-shaped tokens that resolve at all match two
    declarations or more, and charging all of them touches 5895 of the library's
    11000 declarations, including all 92 currently-safe ``_ferromagnetic``
    candidates. Swept over the whole library it collapses ``safe-to-delete``
    from 1458 verdicts to 232 (an 84% reduction) and turns the fixtures red
    (``--expect``: FAIL, 1 of 18). It is therefore rejected not as
    unimplementable but as useless: the 232 survivors are what is left after the
    rule has stopped tracking which citation names which result, so they are not
    a basis anyone should delete from.

    The rule kept is the one the notation actually states: a match is charged
    when the prefix the fragment elides is *itself* cited on the same line
    (2206 charges over 1077 distinct declarations, measured on the scanned
    documentation). It only ever adds citations, so it can only turn
    ``safe-to-delete`` into ``uncertain``, never the reverse. It is *not* inert
    on genuine family labels, and the calibration this module ships is what that
    costs: on the 223 ``_ferromagnetic`` candidates, switching the rule off
    leaves 92 ``safe-to-delete`` and switching it on leaves 47. The label
    ``_ferromagnetic`` is itself charged 155 times (``_pos`` 9 times), because
    the documentation does spell a sibling out in full on those lines; charging
    that one label accounts for 13 of the 45 that move, and other elided
    fragments on the same rows for the remaining 32. What still rescues nobody
    is a family label on a line that elides nothing -- the label alone, with no
    prefix anyone wrote down.
    """
    out: list[Decl] = []
    for decl in matched:
        prefix = decl.final[: len(decl.final) - len(fragment)]
        if prefix and any(other.startswith(prefix) for other in cited):
            out.append(decl)
    return out


def _cited_declaration_names(tree: Tree, doc: DocSource) -> dict[int, set[str]]:
    """Return ``{line: cited final names}`` for the tokens that name a declaration.

    Only real declaration names are collected: prose that happens to be
    name-shaped must not license an elision (:func:`elided_prefix_matches`).
    """
    finals = {final for final, _decl in tree.finals}
    out: dict[int, set[str]] = defaultdict(set)
    for token, lineno in doc.tokens:
        for name in expand_braces(token) if "{" in token else [token]:
            final = name.rsplit(".", 1)[-1]
            if final in finals:
                out[lineno].add(final)
    return out


# A glob/ellipsis citation that resolves to at most this many declarations is
# charged to *all* of them; above it the citation is filed as a family label and
# charged to nobody. The knob exists because the same "attributed to nobody"
# exoneration that produced the false ``safe-to-delete`` repaired by
# :func:`elided_prefix_matches` on the *suffix* channel was still live on the
# *glob* channel: ``docs/index.md:1427`` writes
# ``freeEnergyAlongExhaustion_latticeGraph_{eq_inv_*,eq_log_div_card,nonneg*,
# ge_log_two*}``, whose ``ge_log_two*`` alternative names 2 declarations, and
# ``docs/index.md:1328`` writes ``freeEnergy_*_tendsto_of_abs_h``, which names 4;
# both resolve exactly, and both named only declarations the scanner then
# reported as carrying "no citation in the scanned documentation".
#
# Measured on the scanned documentation (main 171ddd4f): 254 occurrences of a
# non-suffix wildcard token resolving to >= 2 declarations, 218 distinct
# patterns, with match counts n distributed
# ``2:98, 3:22, 4:27, 5:19, 6:9, 7:6, 8:4, 9:9, 10:0, 11:4, 12:2, 13-24:21,
# 26-98:19, 176-219:14``. The distribution is bimodal in *meaning*: small n is almost
# always one result with one variant slot (``mayerPartialSum_*_two``,
# ``freeEnergyΛ_continuous_*``), large n is a genuine family label
# (``correlation_*_*`` matches 219, ``freeEnergyAlongExhaustion_*`` 202).
#
# **The count is a cost knob, not a semantic criterion.** No count separates the
# two classes: ``docs/index.md:2193`` writes
# ``correlationAlongExhaustion_..._ferromagnetic`` as a genuine elision whose
# unbounded ``...`` also swallows an unrelated lower bound, giving a precise
# citation with n = 11, and that over-match is what caps the threshold at 10 (at
# N >= 11 the ground-truth ``safe-to-delete`` fixture row turns ``uncertain`` and
# ``--expect`` goes red).
#
# The value below is that ceiling, because the knob is one-sided: raising it can
# only *remove* declarations from ``safe-to-delete``, never add one, so the
# largest value the fixtures still admit is also the safest. Measured on the
# whole library (main 171ddd4f, 10872 declarations): N = 8 covers 185 of the 254
# occurrences (73%) and reports 980 ``safe-to-delete``; N = 9 and N = 10 both
# cover 194 (76%) and report 976. The four names N = 8 would still hand to a
# deletion PR -- named by the nine 9-match occurrences of the bin list above --
# are ``correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_nonneg``,
# ``correlationAlongExhaustion_latticeGraph_nonneg`` and
# ``vdPolymerFamilies_sumAlongExhaustion_sandwich{,_sharp}_ferromagnetic``. The
# ``_ferromagnetic`` calibration family (43/79/66/35 of 223) and its 112
# zero-consumer count are identical at 8, 9 and 10, so the stricter number costs
# no test churn at all. The price of sitting on the ceiling is that a future
# ``docs/index.md`` elision widening the 11-match citation turns ``--expect``
# red; that is the fail-closed direction and is meant to be read as a signal,
# not silenced by lowering the knob.
#
# **Globs above the threshold remain a known fail-open residue**: they still
# charge nobody, so a declaration cited only by such a label can still be
# reported ``safe-to-delete``. They are printed by :func:`report` under
# "documentation family labels", and closing them is the human keep-check's job
# -- candidate enumeration is not permission.
MAX_CHARGED_GLOB_MATCHES = 10


def _apply_doc_channel(
    tree: Tree,
    verdicts: list[Verdict],
    docs: list[DocSource],
    family_labels: dict[str, list[str]],
) -> None:
    """Attach documentation citations to each candidate.

    Exact and brace-expanded citations mark a published result; wildcard and
    single-match fragment citations only make the candidate uncertain. A
    fragment matching two or more declarations is charged by channel:

    * a ``_``/``.`` **suffix** fragment is a family label attributed to nobody
      (the ``_ferromagnetic`` trap) **unless** the prefix it elides is cited on
      the same line, in which case it is a shorthand for the siblings that share
      that prefix and is charged to them (:func:`elided_prefix_matches`);
    * a **glob/ellipsis** fragment is charged to every declaration it names when
      it names at most :data:`MAX_CHARGED_GLOB_MATCHES` of them, and is a family
      label attributed to nobody above that count. Exonerating *every*
      multi-match glob (as this function did until the threshold landed) is the
      same "attributed to nobody" fail-open the suffix channel was repaired for:
      ``docs/index.md:1427`` cites ``..._ge_log_two*`` (as a brace alternative)
      and both declarations it names came out ``safe-to-delete`` reading "no
      citation in the scanned documentation".

    A citation the normaliser could not read is attached too, to **every**
    candidate (:meth:`UnreadableSpan.could_cite`; the channel is charge-only).
    That is what turns the coverage warnings into a verdict: without it a name
    invisible to the TeX channel could still come out ``safe-to-delete``.
    """
    by_name: dict[str, list[Verdict]] = defaultdict(list)
    for verdict in verdicts:
        by_name[verdict.decl.final].append(verdict)
        by_name[verdict.decl.full].append(verdict)
    fragment_cache: dict[str, list[Decl] | None] = {}

    for doc in docs:
        lines = doc.text.splitlines()
        cited_names = _cited_declaration_names(tree, doc)
        # (a) verbatim occurrences of the candidate name.
        for verdict in verdicts:
            needle = verdict.decl.final
            if needle not in doc.text:
                continue
            for offset, _context, _prefix in find_occurrences(doc.text, needle):
                lineno = offset_to_line(doc.starts, offset)
                snippet = lines[lineno - 1].strip() if lineno - 1 < len(lines) else ""
                verdict.doc_citations.append(
                    f"exact {doc.label}:{lineno}: {snippet[:110]}"
                )
                break
        # (b) brace-alternation, wildcard and fragment tokens.
        for token, lineno in doc.tokens:
            expanded = expand_braces(token) if "{" in token else [token]
            for name in expanded:
                targets = by_name.get(name) or by_name.get(name.rsplit(".", 1)[-1])
                if targets and "{" in token:
                    for verdict in targets:
                        verdict.doc_citations.append(
                            f"exact {doc.label}:{lineno}: brace citation `{token}`"
                        )
                if "*" not in name and ".." not in name and not name.startswith(("_", ".")):
                    continue
                matched = _resolve_fragment(tree, name, fragment_cache)
                if matched is None:
                    continue
                charged = matched
                if len(matched) >= 2:
                    if name.startswith(("_", ".")):
                        charged = elided_prefix_matches(
                            name, matched, cited_names.get(lineno, set())
                        )
                    elif len(matched) <= MAX_CHARGED_GLOB_MATCHES:
                        charged = matched
                    else:
                        charged = []
                    if not charged:
                        family_labels.setdefault(
                            f"{doc.label}:{lineno} `{token}`",
                            [f"{len(matched)} declarations"],
                        )
                if charged:
                    keys = {decl.key for decl in charged}
                    # The count makes the report self-explaining: a reader can
                    # tell a two-match glob charged in full from a family label
                    # one of whose members the elided prefix rescued.
                    detail = (
                        f" ({len(charged)} of the {len(matched)} declarations it names)"
                        if len(matched) > 1
                        else ""
                    )
                    for verdict in verdicts:
                        if verdict.decl.key in keys:
                            verdict.doc_citations.append(
                                f"shorthand {doc.label}:{lineno}: `{token}`{detail}"
                            )
        # (c) module citations.
        for verdict in verdicts:
            tail = verdict.decl.file.split("/", 1)[-1]
            if tail and tail in doc.text:
                verdict.doc_citations.append(
                    f"module-cited {doc.label}: defining module `{tail}` is cited"
                )
        # (d) citations that could not be read, charged to every name they could
        # have been citing.
        for span in doc.unreadable:
            for verdict in verdicts:
                if span.could_cite_decl(verdict.decl):
                    verdict.doc_citations.append(
                        f"unreadable {doc.label}:{span.line}: a citation this scan "
                        f"cannot read ({span.kind}) may name this declaration"
                    )


# ---------------------------------------------------------------------------
# 8. Canary and self-tests
# ---------------------------------------------------------------------------

CANARY_CHARS = ("Λ", "β", "σ")  # capital Lambda, beta, sigma


def run_canary(tree: Tree) -> tuple[int, dict[str, int]]:
    """Assert every Unicode-bearing declaration can find *itself*.

    This is the generalised signature of every past incident: a tokenizer that
    splits a name at a Greek letter makes the declaration invisible to a search
    for its own name. Cheap, unconditional, and aborts the run on failure.
    """
    per_char = {char: 0 for char in CANARY_CHARS}
    names: list[Decl] = []
    for decl in tree.decls:
        if decl.anonymous:
            continue
        if any(char in decl.name for char in CANARY_CHARS):
            names.append(decl)
            for char in CANARY_CHARS:
                if char in decl.name:
                    per_char[char] += 1
    failures: list[str] = []
    for decl in names:
        source = next((f for f in tree.files if f.relpath == decl.file), None)
        if source is None:  # pragma: no cover
            failures.append(f"{decl.full}: defining file vanished")
            continue
        if not find_occurrences(source.cleaned, decl.final):
            failures.append(f"{decl.full} ({decl.file}:{decl.line}) cannot find itself")
    empty = [char for char, count in per_char.items() if count == 0]
    if empty:
        failures.append(
            "canary degenerated: no declaration contains " + ", ".join(repr(c) for c in empty)
        )
    if failures:
        raise Inconsistency("canary failure:\n  " + "\n  ".join(failures[:20]))
    return len(names), per_char


def run_tex_canary() -> int:
    """Assert no code citation in the guide is split across source lines.

    The declaration canary above asks whether a name can find *itself* in its
    defining file; this one asks the same question of the guide, and for the
    same reason: a citation broken across a line raises no coverage warning, so
    the run prints a clean bill of health while the cited name is invisible to
    both halves of the TeX channel (no span to charge, no literal hit to find).
    Four published results were hidden that way and were only rescued -- by
    accident -- by a second citation in ``docs/``.

    Unconditional and cheap, like the declaration canary, and it aborts the run
    rather than warning: this is the guard that keeps ``L7a``/``L7c`` a
    statement about the real guide and not merely about the parser. A guide that
    is *absent* silences the same channel just as completely, so that too aborts
    (:func:`require_documentation`) rather than returning a vacuous zero.
    Returns the number of code citations checked.
    """
    require_documentation()
    raw = _read_doc(TEX_GUIDE)
    citations, broken = tex_citation_line_breaks(raw)
    if broken:
        listing = "\n  ".join(
            f"{rel(TEX_GUIDE)}:{line}: {' '.join(body.split())[:80]!r}"
            for line, body in broken[:20]
        )
        raise Inconsistency(
            f"{len(broken)} code citation(s) in {rel(TEX_GUIDE)} are broken across a "
            "line, which makes the name invisible to the TeX channel with no "
            "warning; join each citation onto one line (use `\\allowbreak` for the "
            f"break hint):\n  {listing}"
        )
    return citations


def char_class_selftest() -> None:
    """Assert the identifier class matches Lean's, in both directions."""
    for char in "λΠΣ×÷ⁿ":  # reserved syntax, or outside Lean's tables
        if is_id_rest(char):
            raise Inconsistency(f"is_id_rest({char!r}) must be False (Lean excludes it)")
    for char in "Λβσℝ₀ⱼÀÿĀſ_'!?aZ0":
        if not is_id_rest(char):
            raise Inconsistency(f"is_id_rest({char!r}) must be True")
    for char in " ().,¬":
        if is_id_rest(char):
            raise Inconsistency(f"is_id_rest({char!r}) must be False")


# ---------------------------------------------------------------------------
# 9. Reporting
# ---------------------------------------------------------------------------

BANNER = """\
LIMITS: this scan is textual. It cannot see simp/aesop set usage, tactic-generated
references, open/export-shortened names, or metaprogrammed names. It does not check
autoImplicit binder drift (a `#check @` dump is a separate gate). Doc rows that depend
on a lemma without naming it are invisible. Run with --lean on a green build to
cross-check the elaborated dependency graph; run --explain for the full table.
A "safe-to-delete" verdict is a necessary, not a sufficient, condition for deletion."""

# Raw: the text quotes LaTeX (``\texttt``, ``\verb``, ``\beta``), and a cooked
# literal turned those backslashes into control characters -- ``--explain``
# printed a tab where the macro name belonged.
LIMITATIONS = r"""L1 simp/aesop/gcongr/fun_prop set membership -- no textual occurrence exists.
   Mitigation: attribute detection forces load-bearing; --lean sees the real term.
L2 open-shortened and export-aliased names -- the reference text can be shorter than
   any dot-suffix of the declaration. Mitigation: dot-suffix search, then --lean.
L3 tactic-generated references (exact?, omega, decide, norm_num extensions,
   unifier-found instances) -- no source text at all. Mitigation: --lean.
L4 autoImplicit is ON in this repository: deleting a neighbour can silently change an
   inferred implicit binder of a survivor. Out of scope; use a `#check @` before/after
   dump as a separate gate.
L5 string-literal and metaprogramming references -- strip_noncode blanks string bodies
   by design. Mitigation: --lean.
L6 documentation prose that depends on a lemma without naming it -- unmatchable in
   principle. Mitigation: the module-cited metadata, then human review.
L7 the TeX macro table is incomplete by construction, so the normaliser meets
   `\texttt{...}` spans it cannot fully read. Mitigation: such a span is not
   dropped but charged to *every* candidate name, which forces `uncertain`; the
   coverage warnings printed with every run are those same spans. The channel is
   **charge-only**: no span refutes anything, whatever its shape. Seven successive
   rule sets tried to decide which names an unread span could not be citing, and
   each opened a new fail-open face the same way -- unexplained material read as
   literal name evidence refuted the name it actually spelled, so the citation was
   charged to nobody. The last one settled it: macro arguments were swallowed with
   their macro (`\ensuremath{\mathbb{X}}`, `\textsubscript{k}`, `\'{e}` each spell
   one character), but only *braced* arguments were, so the LaTeX-standard unbraced
   accent in `\texttt{caf\'e\_lemma}` left `e` behind as a readable fragment and
   refuted `café_lemma` while satisfying every precondition then in force. So the
   residue is no longer a refutation rule: charging every candidate can only cost
   `uncertain` verdicts, and on the real guide it costs nothing, the guide leaving
   no unreadable span at all. What remains are the shapes charging never reaches,
   and they escape for two different reasons. A line break inside a citation (L7a
   with a comment, L7c without one) *does* produce a span, and a clean one, so there
   is nothing to charge -- while the newline it keeps also hides the name from the
   literal search. An unrecognised wrapper (L7b) produces no span at all. The
   line-break shapes are now excluded from the real guide by an unconditional canary,
   so they are a property of the parser, not a live gap; the wrapper shape is still
   editorial.
L7a a `%` comment inside a code citation is a silent gap. TeX splices the comment's
   line into the next one (`\texttt{foo% c` + newline + `\beta bar}` typesets
   `fooβbar`), but comment stripping keeps the line break, so the span parses
   cleanly, raises no warning, normalises to `foo`+newline+`βbar`, and a literal
   search for `fooβbar` finds nothing: the name is charged to nobody. This is the
   counterexample to "a citation that cannot be read is always charged" -- charging
   only applies to material that produced a span. Mitigation: `run_tex_canary`
   rejects any citation in the guide whose body contains a line break, so this
   shape cannot re-enter unnoticed; write `\allowbreak` for the break hint.
L7b only a *recognised* code wrapper is charged, and only in its braced form: the
   span grammar reads `\texttt{...}`, `\verb{...}`, `\lstinline{...}` and
   `\mintinline{...}`, so the delimiter form the last three normally take
   (`\verb|foo\_bar|`) is no span, and `\mintinline{lean}{foo\_bar}` is read as a
   span spelling its language argument (`lean`) rather than the name. The guide
   uses none of those three today (only `\texttt`), so that approximation is not
   live. A name written with any other wrapper (`{\tt caf\'{e}\_lemma}`) is
   likewise not a citation for this scan, so it raises no span and no warning. It
   is *not* generally invisible: normalisation runs over the whole document, not
   only inside spans, so a wrapper-less ASCII name (`{\tt foo\_bar}`) is still
   found by the literal search that rescues published results. What escapes both
   channels is the intersection: a name outside a recognised span *and* written
   with any markup whose normalisation does not reproduce the name. A character
   the macro table cannot spell (`caf\'e`) is only one way in; an unbraced accent,
   a surviving macro or an intervening break do it too. Mitigation is
   editorial: cite code with `\texttt` in the guide. This gap and L7a/L7c are why a
   machine-readable citation macro shared by the guide and this scanner remains the
   permanent fix; PR #4647 records the analysis.
L7c a bare line break inside a code citation is the same gap as L7a without the
   comment: `\texttt{foo\_` + newline + `bar}` parses as one span, raises no
   warning, and normalises to `foo_`+newline+`bar`, which no search for `foo_bar`
   finds. It also typesets wrongly (TeX turns the break into a space *inside* the
   name), so it is a documentation bug as well as a scanner blind spot. Four
   published results were hidden this way in the guide and were rescued only by an
   unrelated `docs/` citation. Both shapes are now forbidden by the same canary.
L7d the doc channel reads README.md, every docs/**/*.md and tex/proof-guide.tex.
   A citation living anywhere else (a GitHub issue, a PR body, a .self-local note,
   a TeX file other than the guide) is invisible, so "no documentation citation"
   means "none in those files". Mitigation: keep published results cited from the
   scanned set; the module-cited metadata catches file-level mentions.
L8 the scanner reads the working tree, not the git index. Run it on a clean tree.
L9 a name mentioned only in a comment or a module docstring is reported (with the
   site and the kind of prose) but never classifies: prose is not a reference, so
   such a lemma really is dead code -- it is the surrounding *documentation* the
   deletion PR must update, or the tree keeps building green while its headers lie.
   The prose is recovered from the comment mask, down to a single blanked
   character, so a one-character name on its own line inside a block comment is
   seen too; what the mask cannot distinguish is prose from an equally long run
   of ordinary code spacing, which is why blank raw text is discarded. The *site*
   of a mention is exact; its *kind* label is a best effort, because a masked run
   that does not itself carry the opener (a continuation line of the same block)
   inherits the kind of the preceding run. The label never changes a verdict.
L10 Markdown code spans are paired positionally, so one unbalanced backtick inverts
   the parity of the rest of its line and the tokenizer swaps prose for citations.
   The line is not skipped (that would drop the brace/glob/suffix citations, the
   ones with no verbatim fallback) but re-read without pairing, which is a superset
   of every pairing; the defect is printed as a Markdown coverage warning. The
   fenced alternative is unbounded and DOTALL, so an unbalanced run of three or
   more backticks pairs with the next run anywhere in the file and would hide
   every citation in between; a fenced match is therefore credited with its two
   delimiters only, its body's backticks are reported like any other, and an odd
   number of fence runs is reported on top. A fenced block that legitimately
   quotes a backtick pays one warning and one superset re-read for that. Two
   shapes escape the *superset* step and stay editorial: a code span opened on one
   line and closed on the next is unmatchable by `[^`\n]+` in either pairing (the
   warning still fires on both lines), and prose read as a citation this way can
   only add `uncertain`, never remove it.
L11 a suffix citation matching two or more declarations (`_pos`, `_ferromagnetic`)
   is a family label attributed to nobody, unless the prefix it elides is cited on
   the same line, which is the documentation's own abbreviation for a run of
   siblings. That exception is not rare: `_ferromagnetic` is charged 155 times and
   `_pos` 9 times, so the rule keeps real family labels alive wherever the row also
   spells a sibling out. Charging every match of every family label regardless was
   measured and rejected: it touches 5895 of 11000 declarations, collapses
   `safe-to-delete` from 1458 to 232 (an 84% reduction) and turns `--expect` red,
   which is not a stricter tool but one whose verdicts no longer track which
   citation names which result. So a family label on a line that elides nothing
   still rescues nobody, and a lemma named only by one is dead code whose
   *documentation* the deletion PR must update.
L12 a glob/ellipsis citation naming more than MAX_CHARGED_GLOB_MATCHES (10)
   declarations is charged to nobody -- the live fail-open residue of this tool.
   At or below the threshold every match is charged, which repairs the leak that
   let `docs/index.md:1427` (`..._ge_log_two*`, a brace alternative naming 2
   declarations) and `docs/index.md:1328` (`freeEnergy_*_tendsto_of_abs_h`,
   naming 4) read as citing nobody; above it,
   a broad label (`correlation_*_*` names 219 declarations) would charge whole
   subsystems, so it is filed and printed instead. The count is a cost knob and
   not a semantic criterion: `docs/index.md:2193` is a precise elision that
   over-matches onto 11 declarations, so a precise citation *can* sit above the
   threshold and rescue nobody. Mitigation: the labels are printed under
   "documentation family labels" on every run and must be read by hand before a
   deletion -- candidate enumeration is not permission."""


def report(
    verdicts: list[Verdict],
    cascade: list[str],
    family_labels: dict[str, list[str]],
    warnings: list[UnreadableSpan],
    malformed: list[str],
    canary: tuple[int, dict[str, int]],
    tex_citations: int,
    elapsed: float,
    report_only: bool,
) -> None:
    """Print the human-readable report (deterministic: every list is sorted)."""
    count, per_char = canary
    print("== dead-candidate scan ==")
    print(
        f"canary: {count} declarations carrying "
        + ", ".join(f"{char!r}x{per_char[char]}" for char in CANARY_CHARS)
        + " each find themselves: PASS"
    )
    print(
        f"canary: {tex_citations} code citations in {rel(TEX_GUIDE)}, none broken "
        "across a line: PASS"
    )
    print()
    buckets: dict[str, list[Verdict]] = {name: [] for name in VERDICT_ORDER}
    for verdict in verdicts:
        buckets[verdict.verdict].append(verdict)
    for name in VERDICT_ORDER:
        group = sorted(buckets[name], key=lambda v: v.decl.full)
        print(f"-- {name}: {len(group)} --")
        for verdict in group:
            decl = verdict.decl
            print(f"  {decl.full}  [{decl.kind}]  {decl.file}:{decl.line}")
            for reason in verdict.reasons:
                print(f"      reason: {reason}")
            for item in verdict.info:
                print(f"      info: {item}")
            for label, group_occs in (
                ("same-file", verdict.same_file),
                ("cross-file", verdict.cross_file),
                ("test", verdict.test_refs),
            ):
                for occ in sorted(group_occs, key=lambda o: (o.file, o.line))[:10]:
                    owner = occ.owner.full if occ.owner else "<file level>"
                    print(f"      {label} consumer: {occ.file}:{occ.line} in {owner}")
                if len(group_occs) > 10:
                    print(f"      ... and {len(group_occs) - 10} more {label} consumers")
            for citation in sorted(set(verdict.doc_citations))[:6]:
                print(f"      doc: {citation}")
            if verdict.witness:
                print("      witness path: " + " -> ".join(verdict.witness))
            if decl.attrs:
                print(f"      attributes: @[{', '.join(decl.attrs)}]")
        print()

    print(f"-- cascade (informational, never auto-deleted): {len(cascade)} --")
    for item in cascade[:40]:
        print(f"  {item}")
    if len(cascade) > 40:
        print(f"  ... and {len(cascade) - 40} more")
    print()
    print(
        f"-- documentation family labels: {len(family_labels)} "
        f"(a glob naming more than {MAX_CHARGED_GLOB_MATCHES} declarations, or a bare "
        "suffix label; attributed to no declaration -- a KNOWN fail-open residue, "
        "close it by hand before deleting anything these lines could be citing) --"
    )
    for label in sorted(family_labels)[:20]:
        print(f"  {label}: {family_labels[label][0]}")
    if len(family_labels) > 20:
        print(f"  ... and {len(family_labels) - 20} more")
    print()
    print(
        f"-- coverage warnings: {len(warnings)} "
        "(each forces `uncertain` on every candidate it could be citing) --"
    )
    for warning in warnings[:10]:
        print(f"  {warning.message}")
    if len(warnings) > 10:
        print(f"  ... and {len(warnings) - 10} more")
    print()
    print(
        f"-- coverage warnings, Markdown backtick parity: {len(malformed)} "
        "(the line's tokens are re-read without pairing, so no citation is lost) --"
    )
    for item in malformed[:10]:
        print(f"  {item}")
    if len(malformed) > 10:
        print(f"  ... and {len(malformed) - 10} more")
    print()
    print(f"elapsed: {elapsed:.1f}s")
    print()
    if report_only:
        print(
            "NON-EVIDENTIAL: --report-only always exits 0. "
            "Its output must not be pasted as deletion evidence in a PR."
        )
    print(BANNER)


# ---------------------------------------------------------------------------
# 10. Fixture (regression) mode
# ---------------------------------------------------------------------------


def read_fixtures(path: Path) -> list[tuple[str, str, str]]:
    """Read ``name <TAB> expected-class <TAB> provenance`` rows."""
    rows: list[tuple[str, str, str]] = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) < 2:
            raise Inconsistency(f"malformed fixture row: {raw!r}")
        rows.append((parts[0].strip(), parts[1].strip(), parts[2].strip() if len(parts) > 2 else ""))
    return rows


def run_expect(tree: Tree, docs: list[DocSource], path: Path) -> int:
    """Run the fixture regression suite. Return the process exit code."""
    rows = read_fixtures(path)
    verdicts, _cascade, family_labels = classify(
        tree, [row[0] for row in rows], docs, allow_homonym=False
    )
    by_name = {verdict.name: verdict for verdict in verdicts}
    failures: list[str] = []
    for name, expected, provenance in rows:
        actual = by_name[name].verdict
        if expected == "not-safe":
            ok = actual != SAFE
        else:
            ok = actual == expected
        status = "ok  " if ok else "FAIL"
        print(f"{status} {name}: expected {expected}, got {actual}   ({provenance})")
        if not ok:
            failures.append(name)
    print()
    if failures:
        print(f"fixtures: FAIL ({len(failures)} of {len(rows)})")
        return EXIT_NOT_SAFE
    print(f"fixtures: PASS ({len(rows)} rows)")
    print(f"family labels observed: {len(family_labels)}")
    return EXIT_OK


# ---------------------------------------------------------------------------
# 11. Optional Lean cross-check (--lean)
# ---------------------------------------------------------------------------

DUMP_DEPS = REPO_ROOT / "scripts" / "audit" / "DumpDeps.lean"


def lean_dependency_edges() -> dict[str, set[str]]:
    """Return ``constant -> used constants`` from the elaborated environment.

    Requires a green build (all oleans current). This is the one instrument that
    sees ``simp``-set usage and tactic-generated references, so it is used as a
    *validator of the text scanner*, not as the primary verdict.
    """
    proc = subprocess.run(
        ["lake", "env", "lean", str(DUMP_DEPS)],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        raise Inconsistency(
            "`lake env lean scripts/audit/DumpDeps.lean` failed (a green build is "
            f"required for --lean):\n{proc.stderr.strip()[:2000]}"
        )
    edges: dict[str, set[str]] = {}
    for line in proc.stdout.splitlines():
        if "\t" not in line:
            continue
        source, targets = line.split("\t", 1)
        edges[source.strip()] = {t for t in targets.split() if t}
    if not edges:
        # An empty dump is indistinguishable from "nothing is used by anything",
        # so accepting it would print "no consumer missed" while checking nothing.
        raise Inconsistency(
            "`lake env lean scripts/audit/DumpDeps.lean` produced no dependency "
            "edges; the cross-check would be vacuous (is the build green?)"
        )
    return edges


def _lean_aliases(full: str) -> set[str]:
    """Return the names under which ``full`` can appear in the elaborated dump.

    The text scanner records a namespace-qualified source name (``Ambient.foo``)
    while Lean prints the absolute name (``IsingModel.Ambient.foo``), so the two
    spellings of the same declaration are matched -- and *only* those two.
    Comparing final components alone (as an earlier revision did) let ``A.foo``
    stand in for ``B.foo`` and hid a genuinely unseen consumer.
    """
    if full.startswith("IsingModel."):
        return {full, full[len("IsingModel.") :]}
    return {full, f"IsingModel.{full}"}


def lean_cross_check(
    verdicts: list[Verdict], edges: dict[str, set[str]]
) -> tuple[list[str], list[str]]:
    """Return ``(hard failures, advisory findings)`` from the elaborated graph.

    Every candidate is compared, not only the ``safe-to-delete`` ones: an unseen
    consumer is a defect of the text scanner wherever it appears. It is fatal on
    a ``safe-to-delete`` verdict (the tool would authorise a bad deletion) and
    advisory elsewhere (the verdict is already "keep", so the risk is a wrong
    *reason*, not a wrong action).
    """
    reverse: dict[str, set[str]] = defaultdict(set)
    for source, targets in edges.items():
        for target in targets:
            reverse[target].add(source)
    problems: list[str] = []
    advisories: list[str] = []
    for verdict in verdicts:
        full = verdict.decl.full
        aliases = _lean_aliases(full)
        lean_consumers: set[str] = set()
        for key in aliases:
            lean_consumers |= reverse.get(key, set())
        lean_consumers -= aliases
        if not lean_consumers:
            continue
        text_consumers: set[str] = set()
        for occ in verdict.consumers:
            if occ.owner is not None:
                text_consumers |= _lean_aliases(occ.owner.full)
        unseen = sorted(lean_consumers - text_consumers)
        if not unseen:
            continue
        message = f"{full}: Lean sees consumers {unseen[:5]} that the text scan does not"
        if verdict.verdict == SAFE:
            problems.append(message)
        else:
            advisories.append(f"[{verdict.verdict}] {message}")
    return problems, advisories


# ---------------------------------------------------------------------------
# 12. CLI
# ---------------------------------------------------------------------------


def read_names_file(path: Path) -> list[str]:
    """Read one candidate name per line, ignoring blanks and ``#`` comments."""
    names: list[str] = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if line and not line.startswith("#"):
            names.append(line)
    return names


def collect_names(args: argparse.Namespace, tree: Tree) -> list[str]:
    """Return the candidate list assembled from the CLI arguments."""
    names: list[str] = []
    if args.names_file:
        names.extend(read_names_file(Path(args.names_file)))
    names.extend(args.name or [])
    if args.pattern:
        regex = re.compile(args.pattern, re.UNICODE)
        names.extend(
            sorted(
                decl.full
                for decl in tree.decls
                if not decl.anonymous and regex.search(decl.name)
            )
        )
    seen: set[str] = set()
    out: list[str] = []
    for name in names:
        if name not in seen:
            seen.add(name)
            out.append(name)
    return out


def build_parser() -> argparse.ArgumentParser:
    """Return the command-line parser."""
    parser = argparse.ArgumentParser(
        description="Deletion-candidate safety scanner for the IsingModel library."
    )
    parser.add_argument("names_file", nargs="?", help="file with one declaration name per line")
    parser.add_argument("--name", action="append", help="add a single candidate name")
    parser.add_argument("--pattern", help="add every declaration whose name matches this regex")
    parser.add_argument("--json", dest="json_path", help="write machine-readable verdicts here")
    parser.add_argument(
        "--report-only", action="store_true", help="always exit 0 (output is non-evidential)"
    )
    parser.add_argument("--expect", help="regression mode against a fixtures TSV")
    parser.add_argument(
        "--lean", action="store_true", help="cross-check the elaborated graph (needs a green build)"
    )
    parser.add_argument(
        "--allow-homonym", action="store_true", help="permit safe for a colliding final component"
    )
    parser.add_argument("--explain", action="store_true", help="print the full limitation table")
    parser.add_argument("--self-test", action="store_true", help="run the built-in test suite")
    return parser


def write_json(path: Path, verdicts: list[Verdict], cascade: list[str]) -> None:
    """Write the verdicts as JSON so a PR body can be generated deterministically."""
    payload = {
        "verdicts": [
            {
                "name": verdict.name,
                "full": verdict.decl.full,
                "kind": verdict.decl.kind,
                "file": verdict.decl.file,
                "line": verdict.decl.line,
                "verdict": verdict.verdict,
                "reasons": verdict.reasons,
                "consumers": sorted(
                    f"{occ.file}:{occ.line}" for occ in verdict.consumers
                ),
                "doc_citations": sorted(set(verdict.doc_citations)),
                "witness": verdict.witness,
            }
            for verdict in sorted(verdicts, key=lambda v: v.decl.full)
        ],
        "cascade": cascade,
    }
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    """Run the scanner and return the process exit code."""
    args = build_parser().parse_args(argv)
    started = time.time()
    try:
        char_class_selftest()
        if args.explain:
            print(LIMITATIONS)
            print()
            print("TeX macro table (incomplete by construction):")
            for macro in sorted(TEX_MACROS):
                print(f"  {macro} -> {TEX_MACROS[macro]}")
            print()
        if args.self_test:
            from test_dead_candidate_scan import run_suite  # noqa: PLC0415

            return run_suite()

        tree = load_tree()
        canary = run_canary(tree)
        tex_citations = run_tex_canary()
        docs = load_docs()
        warnings = [span for doc in docs for span in doc.unreadable]
        malformed = [item for doc in docs for item in doc.malformed]

        if args.expect:
            return run_expect(tree, docs, Path(args.expect))

        names = collect_names(args, tree)
        if not names:
            print("no candidate names given (pass a NAMES_FILE, --name or --pattern)")
            return EXIT_INCONSISTENT

        verdicts, cascade, family_labels = classify(tree, names, docs, args.allow_homonym)
        if args.lean:
            problems, advisories = lean_cross_check(verdicts, lean_dependency_edges())
            for advisory in advisories[:20]:
                print(f"--lean advisory: {advisory}")
            if len(advisories) > 20:
                print(f"--lean advisory: ... and {len(advisories) - 20} more")
            if problems:
                raise Inconsistency(
                    "text scanner bug (Lean sees consumers the text scan missed); "
                    "add these to the fixtures:\n  " + "\n  ".join(problems)
                )
            print(
                f"--lean cross-check: {len(verdicts)} candidate(s) compared against the "
                "elaborated graph; no consumer seen by Lean was missed on a "
                "safe-to-delete verdict"
            )
        if args.json_path:
            write_json(Path(args.json_path), verdicts, cascade)
        report(
            verdicts,
            cascade,
            family_labels,
            warnings,
            malformed,
            canary,
            tex_citations,
            time.time() - started,
            args.report_only,
        )
        if args.report_only:
            return EXIT_OK
        return EXIT_OK if all(v.verdict == SAFE for v in verdicts) else EXIT_NOT_SAFE
    except Inconsistency as exc:
        print(f"INCONSISTENT: {exc}", file=sys.stderr)
        return EXIT_INCONSISTENT


if __name__ == "__main__":
    sys.exit(main())
