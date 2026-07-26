#!/usr/bin/env python3
"""Fail-closed audit of ``.lean`` path citations in ``tex/`` and ``docs/``.

The public proof guide and ``docs/index.md`` name Lean source files by path.
Refactors move and delete those files, so the documents accumulate citations
that no longer point anywhere. Four successive attempts to clean that up (the
history behind PR #4714) failed the same way: a scan produced an *exoneration*
("only these N are left"), the exoneration was wrong because the scan had not
covered some citation variant, and the fix added one more special case.

``dev-principles`` names both the rule that was broken -- an approximate scan
may be used to *charge* but never to *exonerate* -- and the remedy once a defect
recurs twice: remove the exonerating capability rather than patch it again.
This tool is built around that inversion.

The two invariants
------------------
1. **A citation is resolved only by exact evidence.** ``RESOLVED`` requires the
   token to be a *component-aligned* suffix of exactly one **git-tracked**
   ``.lean`` path, to carry at least one directory component, and to be
   *delimited*: a match glued to neighbouring path text (``/X/Y.lean``,
   ``../X/Y.lean``, ``X/Y.lean.bak``) is charged as the whole glued run and is
   never truncated into a different path that happens to resolve. No archive
   tag, no section heading, no neighbouring line and no filesystem copy can
   resolve anything. Every other outcome -- no match, several matches, a bare
   basename, a token that does not normalise -- is a finding. There is
   deliberately no "probably fine" bucket and **no exemption channel at all**:
   nothing written in a document can make a citation stop being charged (see
   "Why there is no exemption channel" below).

2. **Coverage audit.** Every raw ``.lean`` occurrence in every target must be
   accounted for by the extractor: per line ``line.count(".lean")`` must equal
   the number of tokens (plus explicitly enumerated non-citation acknowledgements)
   attributed to that line, and the per-file sums must agree. One unaccounted
   occurrence fails the whole run. This is what converts "the scan missed a
   variant" -- a silent fail-open, and the actual failure mode of the four
   previous attempts -- into a loud failure. It runs always, before resolution,
   it cannot be disabled by a flag, it is not part of the baseline (it can never
   be "accepted"), and a coverage failure -- like any hard failure -- suppresses
   the findings report **in every format** (``text``, ``tsv`` and ``json``
   alike, and no baseline can be written from such a run): printing "280
   dangling" from an extractor that is provably incomplete is the artefact that
   has to stop being produced, and it would still be that artefact if it were
   printed as TSV.

Decision table
--------------
Let ``suffix_matches(tok)`` be the set of tracked paths of which ``tok`` is a
component-aligned suffix (whole path components compared -- never a substring or
``endswith`` test, so ``Ball/Real.lean`` does not match ``.../SmallBall/Real.lean``).

===  =========================================================  =========================
R1   exactly one match **and** the token contains ``/``          ``RESOLVED``
R2   no match                                                    ``MISSING``
R3   two or more matches                                         ``AMBIGUOUS``
R4   exactly one match but the token has no ``/``                ``BASENAME_ONLY``
R5   token does not normalise (brace, ``..``, glued neighbour)   ``MALFORMED``
R6   a target does not exist or is not tracked                   hard failure ``TARGET``
R7   an unaccounted raw ``.lean`` occurrence                     hard failure ``COVERAGE``
R8   citations in a target below its floor                       hard failure ``VACUOUS``
R9   tracked ``.lean`` files below ``MIN_TRACKED_LEAN``          hard failure ``VACUOUS``
R10  a resolved path outside ``ALLOWED_TRACKED_PREFIXES``        hard failure ``CONTAMINATED``
===  =========================================================  =========================

``RESOLVED`` is silent; ``MISSING``, ``AMBIGUOUS``, ``BASENAME_ONLY`` and
``MALFORMED`` are findings and gate the exit code through the baseline ratchet.
``SELFREF`` (below) is advisory. The table is total and it is closed: a citation
lands in exactly one row, and there is no row a document can put itself into.

Why the resolution set is ``git ls-files``
------------------------------------------
Measured on this repository: a filesystem walk finds **112,420** ``.lean`` files
(``.lake/`` holds mathlib, and ``.self-local/benchmarks/`` holds untracked
copies of the tree), while ``git ls-files`` finds **2,018**. A walk therefore
exonerates essentially any citation, including one that points at a file this
repository deleted. The tracked set needs no allow/deny list to stay correct,
and R10 asserts that whatever *does* resolve lives under a path the project
owns, so a future tracked copy of the tree cannot silently widen the set.
There is deliberately no ``--ref`` option: the working tree's tracked set is the
only resolution source.

Why there is no exemption channel
---------------------------------
Nothing a document says about a citation changes that citation's verdict. A
reference to an archived, deleted or renamed artefact is charged like any other,
and the *only* place an accepted finding is recorded is the committed baseline:
a file outside the documents, keyed per finding, whose growth is reviewable.

That is a removal, not an omission. Two exoneration mechanisms were built or
measured here, and both are gone:

* **Archive-tag resolution.** Measured: the heading-scoped variant rescues **0**
  citations, while the unconditional variant exonerates **276 of 280** no-match
  citations -- 0% useful, 98.6% fail-open. Never implemented.
* **A per-citation ``citation-audit:`` comment directive**, verified against the
  named archive tag. This one *was* implemented, and the same defect -- a
  *quotation* of the syntax arming a real exemption -- was found three times,
  each round answering it with one more enumerated spelling:

  - ``6eefda79`` shipped the directive read from anywhere on any line;
  - ``e4531116`` closed the mid-sentence quotation, and the sample printed
    inside a ``Verbatim`` or a fenced block, by requiring a comment line;
  - ``4093c387`` closed the sample printed inside any *other* verbatim
    environment (``verbatim``, ``lstlisting``, ``alltt``) and the one indented
    into a Markdown code block.

  An enumeration is not an invariant: it covers the renderings *these two
  documents* happen to use, while LaTeX and Markdown have unboundedly many more
  (``VerbatimOut``, ``filecontents``, ``comment``, ``<pre>`` and ``<details>``
  were all still open when the mechanism was deleted). Live population across
  both targets, over all three rounds: **zero** directives -- the feature was
  charging a maintenance cost against no use whatsoever.

``dev-principles`` fixes what to do here: a defect that recurs twice is removed
structurally rather than patched again, and "do not have the capability" is the
first candidate. Deciding whether a line is an instruction or a rendering of one
means rendering LaTeX and Markdown, which a text approximation cannot do; and
the rule this module is built on says an approximation may charge but may not
exonerate. So the capability is gone, and with it the question of which
environment names are enumerated for exemption purposes -- an unlisted
environment can no longer arm anything, because there is nothing to arm.

The cost is real and is accepted deliberately: a *legitimate* citation of an
archived artefact can no longer be expressed as resolved. It stays a ``MISSING``
finding and is carried as a baseline row. That is the intended trade -- charging
is monotone and needs no adjudication, exonerating is neither. If a per-citation
exemption is ever wanted, it belongs in the baseline file as an explicit,
diffable registration outside the documents, never in a syntax the documents
themselves can quote.

Verbatim environments are still tracked (:data:`VERBATIM_ENVIRONMENT`), for
*extraction* and not for exemption: they decide whether a tex line is scanned
literally or split into macro arguments plus residue, and they are what allows a
source-line wrap to be rejoined into the one path the document wrote. Both
belong to reading the document, and both charge.

Self-reference detection (``SELFREF``, advisory)
------------------------------------------------
Sentences of the shape "X now lives in ``A/X.lean`` and is re-exported by the
old ``X.lean``" become vacuous once the two paths are the same file. Detection
shares this module's extractor on purpose -- a second script would mean a second
approximation that drifts -- but is a separate class with its own baseline rows
and **does not gate the exit code**: cue-word matching can only under-detect, so
it is charge-only, and its silence must never be read as "no vacuous sentences
remain".

Usage
-----
::

    python3 scripts/citation_audit.py                      # default targets, ratchet, text report
    python3 scripts/citation_audit.py --targets FILE ...   # explicit targets
    python3 scripts/citation_audit.py --format tsv         # the count-of-record
    python3 scripts/citation_audit.py --format json        # for tooling
    python3 scripts/citation_audit.py --write-baseline PATH
    python3 scripts/citation_audit.py --strict             # require zero unresolved (end state)
    python3 scripts/citation_audit.py --self-test          # scripts/test_citation_audit.py

Exit code 0 iff the coverage audit passes, no hard failure fired, and no
finding exceeds the baseline; under ``--strict``, iff there are no findings at
all. The baseline is a multiset keyed on ``(class, target, token)``: comparing
totals would let one fix pay for one regression, and line numbers churn on every
unrelated edit, so they are payload and are excluded from the key.

Honesty note
------------
The extraction layer is a text approximation of LaTeX and Markdown and is
best-effort *charging* only. Green tests do not mean the tokeniser is complete;
completeness is what the coverage audit and human review of edge cases are for.
CI wiring (a ``V5`` in ``scripts/audit_gate.py`` or a workflow step) is a
configuration change and is deliberately not part of this script: there is no
adapter function here either, because an adapter written before its caller
exists is guesswork, and the obvious guess -- returning findings and
self-references as one list -- would silently promote the advisory ``SELFREF``
class into a gating one. A future wiring commit calls :func:`audit` and reads
``Report.findings`` (gating), ``Report.coverage`` and ``Report.hard`` (hard
failures), ``Report.visited`` (scanned-set honesty) and ``Report.selfrefs``
(advisory, must not gate) explicitly.

Runtime: Python 3.9 standard library only; no ``lake``, no network.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterable, List, NamedTuple, Optional, Sequence, Set, Tuple

# Repository root = parent of the ``scripts`` directory holding this file.
REPO_ROOT = Path(__file__).resolve().parent.parent
BASELINE_FILE = REPO_ROOT / "scripts" / "audit" / "citation_baseline.tsv"

# Documents whose ``.lean`` citations are audited by default.
TARGETS = ("tex/proof-guide.tex", "docs/index.md")

# Anti-vacuity floors (R8/R9). A tokeniser that stops matching, or a target
# accidentally emptied, would otherwise report "0 findings, all clean" -- the
# most convincing possible false pass. Lowering these constants is the cheapest
# way to disarm the whole tool, so each move must be deliberate, in the same
# commit, with a reason. Measured on the tree this file was written against:
# 1,333 citations in the tex, 2,698 in the markdown, 2,018 tracked .lean files.
MIN_CITATIONS = {"tex/proof-guide.tex": 1200, "docs/index.md": 2400}
MIN_TRACKED_LEAN = 1800

# Floor applied to a target passed on the command line that has no entry in
# ``MIN_CITATIONS``: auditing a document in which the extractor found nothing at
# all is never a meaningful pass.
DEFAULT_MIN_CITATIONS = 1

# A resolved citation must land inside the part of the tree this project owns.
# Measured: 2,017 of the 2,018 tracked ``.lean`` files match (the exception is
# ``scripts/audit/DumpDeps.lean``, a helper no document cites). The assertion is
# on *resolved* paths, so it fires exactly when a citation is answered by
# something like a ``.self-local/benchmarks/`` copy of a deleted file.
ALLOWED_TRACKED_PREFIXES = ("IsingModel/", "IsingModel.lean", "test/")

# Verdict classes.
RESOLVED = "RESOLVED"
MISSING = "MISSING"
AMBIGUOUS = "AMBIGUOUS"
BASENAME_ONLY = "BASENAME_ONLY"
MALFORMED = "MALFORMED"
SELFREF = "SELFREF"

# Classes that are findings and gate the exit code.
FINDING_CLASSES = (MISSING, AMBIGUOUS, BASENAME_ONLY, MALFORMED)
# Classes that are reported and baselined but never gate the exit code.
ADVISORY_CLASSES = (SELFREF,)
ALL_CLASSES = (
    RESOLVED,
    MISSING,
    AMBIGUOUS,
    BASENAME_ONLY,
    MALFORMED,
    SELFREF,
)

# ---------------------------------------------------------------------------
# Lexical layer
# ---------------------------------------------------------------------------

# Verbatim environments. Only ``Verbatim`` (fancyvrb) is in use today
# (measured: 423 ``\begin{Verbatim}``, no ``verbatim``/``lstlisting``/``alltt``),
# but the whole family is enumerated for the same reason ``MACRO`` below lists
# ``\lstinline`` and ``\verb``: an unlisted spelling is an unhandled variant the
# moment someone writes it.
#
# What being inside one of these environments changes is *extraction only*: the
# line is scanned literally rather than split into macro arguments plus residue,
# and a source-line wrap may be rejoined (see :data:`WRAP_PREFIX`) so the one
# path the document wrote is the one that gets charged. It confers no exemption
# on anything -- this module has no exemption channel to confer -- so an
# environment missing from this list can only change how a block is tokenised,
# never whether its citations are charged.
#
# The name test is case-insensitive and accepts the starred and prefixed forms,
# so ``verbatim``, ``Verbatim*``, ``BVerbatim`` and ``SaveVerbatim`` are all
# covered. Environment options (``\begin{lstlisting}[language=Lean]``) follow the
# closing brace and are ignored. Closing requires the *same* name that opened, so
# a mismatched ``\end`` cannot end verbatim treatment early; an environment left
# open runs to the end of the file, which is the fail-closed direction.
ENVIRONMENT_BEGIN = re.compile(r"\\begin\{([^{}]*)\}")
ENVIRONMENT_END = re.compile(r"\\end\{([^{}]*)\}")
VERBATIM_ENVIRONMENT = re.compile(
    r"(?:B|L|S|Save)?(?:verbatim|verbatimtab|semiverbatim|alltt|lstlisting|listing|minted)\*?",
    re.IGNORECASE,
)

# Inline macros that carry a path. ``\texttt`` and ``\path`` are the ones in use
# (965 / 72 invocations whose argument holds a ``.lean``, out of 10,892 / 145
# invocations in all); ``\lstinline`` and ``\verb`` are listed because they
# would otherwise be an unhandled variant the moment someone uses one. Nested
# ``\texttt`` inside a ``\section{...}`` heading is handled by the residue scan.
MACRO = re.compile(r"\\(?:texttt|path|lstinline|verb)\{((?:\\.|[^{}\\])*)\}")

# A citation token: starts with an identifier character, may contain one brace
# group (the ``Dir/{A, B}.lean`` shorthand), ends in ``.lean``. The leading
# ``[A-Za-z0-9_]`` is what makes a prose ".lean" *not* a token -- those
# occurrences are handled by ``NON_CITATION`` below, never ignored.
#
# The pattern has no boundary of its own on either side: it starts at the first
# identifier character it can and stops at the last ``.lean`` it can reach, so
# on ``../X/Y.lean`` it yields ``X/Y.lean`` and on ``X/Y.lean.bak`` it again
# yields ``X/Y.lean`` -- a *different* path from the one written, handed to the
# resolver as if the document had written it. Truncating a citation until it
# resolves is an exoneration, so every match is widened by :func:`glued_text`
# before anything else looks at it.
TOKEN = re.compile(r"[A-Za-z0-9_][A-Za-z0-9_.+/-]*(?:\{[^}]*\}[A-Za-z0-9_.+/-]*)?\.lean")

# Brace shorthand splitter, applied to a whole token.
BRACE = re.compile(r"^(.*?)\{([^}]*)\}(.*)\.lean$")

# Characters a citation may start with, and the characters it may contain.
TOKEN_START_CHARS = frozenset(
    "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_"
)
TOKEN_CHARS = TOKEN_START_CHARS | frozenset(".+/-")

# Characters that must not touch a match on either side. It is ``TOKEN_CHARS``
# plus ``~``: everything a path may contain (so a match cannot be a truncation
# of a longer path-like run) plus the one leading character a shell-style home
# path adds. Used both for the boundary widening in :func:`glued_text` and for
# the test that keeps ``NON_CITATION`` from degenerating into a wildcard.
TOKEN_EDGE_CHARS = TOKEN_CHARS | frozenset("~")

# Raw ``.lean`` occurrences that are deliberately *not* citations. This is an
# enumeration of exact spellings, not a pattern, and it must stay one: the
# coverage audit is only as strong as this list is short. Each entry is
# acknowledged only when it is delimited on both sides (see
# :func:`acknowledge_non_citations`), because "any ``.lean`` preceded by a
# non-token character" would acknowledge every uncovered variant there is and
# dissolve the guard completely.
NON_CITATION = ("**/*.lean", "*.lean", ".lean")

# Characters after which a bare ".lean" reads as the file extension rather than
# as a truncated citation. Enumerated for the same reason as ``NON_CITATION``.
NON_CITATION_LEFT_DELIMITERS = frozenset(" \t`(\"'")

# Source-line wrap inside a verbatim block: a line that is nothing but a path
# prefix, continued at column 0 by the rest of the path on the next line. Both
# halves are deliberately strict. The prefix must *itself* look like a path
# (so an ASCII-tree header such as ``+-- Inequalities/`` never starts a join)
# and the continuation must begin in column 0 with an identifier character (so
# an indented tree entry such as ``    GKS.lean`` is never joined onto it).
# Without that strictness the join would reconstruct a directory from tree
# layout, which is the inference this tool exists to refuse.
WRAP_PREFIX = re.compile(r"^[A-Za-z0-9_][A-Za-z0-9_.+/-]*/$")
WRAP_CONTINUATION = re.compile(r"^[A-Za-z0-9_]")

# Cue words that make a repeated citation inside one paragraph a self-reference
# rather than an ordinary repetition.
SELFREF_CUE = re.compile(
    r"re-exported|legacy|split into|former split|merged into|now lives in"
    r"|lives in|live in|\bold\b"
)


def verbatim_environment_opened(line: str) -> Optional[str]:
    """Return the name of the verbatim environment ``line`` opens, else ``None``.

    The first verbatim-family ``\\begin{...}`` on the line wins; a line that
    opens only prose environments opens nothing. The name is returned rather
    than a boolean so :func:`verbatim_environment_closes` can require the
    matching ``\\end``.
    """
    for match in ENVIRONMENT_BEGIN.finditer(line):
        if VERBATIM_ENVIRONMENT.fullmatch(match.group(1)):
            return match.group(1)
    return None


def verbatim_environment_closes(line: str, name: str) -> bool:
    """Return whether ``line`` closes the open verbatim environment ``name``."""
    return any(match.group(1) == name for match in ENVIRONMENT_END.finditer(line))


def unescape(text: str) -> str:
    """Undo the LaTeX/Markdown backslash escapes that appear inside a citation.

    Applied before tokenising, so ``Foo/Bar\\_Baz.lean`` is one token spelling
    the real filename. None of these substitutions can create or destroy a
    ``.lean`` substring, which is what lets the coverage audit count raw
    occurrences on the original line and captured tokens on the unescaped text.
    """
    return (
        text.replace("\\_", "_")
        .replace("\\{", "{")
        .replace("\\}", "}")
        .replace("\\%", "%")
        .replace("\\&", "&")
    )


def expand(token: str) -> List[str]:
    """Expand the ``Dir/{A, B}.lean`` shorthand into one token per alternative.

    A token whose braces do not form exactly one flat group is returned
    unchanged *with its braces*, so :func:`normalise` classifies it
    ``MALFORMED``. Silently stripping the braces -- the obvious repair -- would
    invent a filename and hand it to the resolver, which is an exoneration.
    """
    if "{" not in token and "}" not in token:
        return [token]
    match = BRACE.match(token)
    if not match:
        return [token]
    prefix, alternatives, suffix = match.group(1) or "", match.group(2), match.group(3)
    expanded = [
        prefix + alternative.strip() + suffix + ".lean"
        for alternative in alternatives.split(",")
        if alternative.strip()
    ]
    return expanded or [token]


def glued_text(text: str, start: int, end: int) -> str:
    """Return the whole run of path characters a ``TOKEN`` match sits inside.

    ``TOKEN`` matches without boundaries (see its comment), so a match is only
    evidence about the document when nothing path-like touches it. Widening to
    the maximal run of :data:`TOKEN_EDGE_CHARS` returns the text *as written*:
    equal to the match when it was delimited, and strictly longer -- and hence
    rejected by :func:`normalise` -- when it was a truncation of ``/X/Y.lean``,
    ``./X/Y.lean``, ``../X/Y.lean``, ``~/X/Y.lean``, ``X/Y.lean.bak`` or
    ``X/Y.leanx``. Charging the glued run is the fail-closed reading: the tool
    must not repair a citation into one that resolves.
    """
    left, right = start, end
    while left > 0 and text[left - 1] in TOKEN_EDGE_CHARS:
        left -= 1
    while right < len(text) and text[right] in TOKEN_EDGE_CHARS:
        right += 1
    return text[left:right]


def normalise(token: str) -> Optional[str]:
    """Return the token if it is a well-formed relative path, else ``None``.

    ``None`` means ``MALFORMED`` (R5). Rejected: leftover braces; anything that
    does not end in ``.lean`` (``X/Y.lean.bak``, ``X/Y.leanx``); a character no
    path component of this repository may hold (``~`` and everything else
    outside :data:`TOKEN_CHARS`); a first character that is not an identifier
    character (``/X.lean``, ``./X.lean``, ``../X.lean``); an empty component;
    and ``.``/``..`` components anywhere. Each of those would otherwise be
    handed to a suffix lookup that answers a different question from the one the
    document asked.

    The predicate is total on the *glued* text the extractor hands over (see
    :func:`glued_text`), which is what makes the absolute-path and ``..`` rows of
    the decision table reachable at all: ``TOKEN`` on its own would have
    truncated those spellings into a plain relative path before this is called.
    """
    if "{" in token or "}" in token:
        return None
    if not token.endswith(".lean"):
        return None
    if any(char not in TOKEN_CHARS for char in token):
        return None
    if token[0] not in TOKEN_START_CHARS:
        return None
    parts = token.split("/")
    for part in parts:
        if part in ("", ".", ".."):
            return None
    return token


# ---------------------------------------------------------------------------
# Resolution set (tracked files only)
# ---------------------------------------------------------------------------


class GitError(RuntimeError):
    """A git query failed; treated as a hard failure, never as an empty answer."""


def _git(args: Sequence[str]) -> str:
    """Run ``git`` in the repository root and return stdout."""
    try:
        proc = subprocess.run(
            ["git", *args],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError as exc:  # pragma: no cover - git missing is an environment fault
        raise GitError(f"git {' '.join(args)}: {exc}") from exc
    if proc.returncode != 0:
        raise GitError(f"git {' '.join(args)}: {proc.stderr.strip()}")
    return proc.stdout


def tracked_lean_files() -> List[str]:
    """Return every git-tracked ``.lean`` path, sorted.

    This is the *only* resolution source. It is not a filesystem enumeration on
    purpose: see the module docstring (112,420 files on disk against 2,018
    tracked). Anything reachable only through ``.lake/`` or an untracked
    scratch copy must not be able to answer a citation.
    """
    out = _git(["ls-files", "-z", "--", "*.lean"])
    return sorted(path for path in out.split("\0") if path)


def tracked_paths() -> Set[str]:
    """Return every git-tracked path (used to verify the targets themselves)."""
    out = _git(["ls-files", "-z"])
    return {path for path in out.split("\0") if path}


def suffix_map(paths: Iterable[str]) -> Dict[str, Set[str]]:
    """Map every component-aligned tail of every path to the paths having it.

    Component alignment is the whole point: the lookup is an exact dictionary
    hit on ``"/"``-joined whole components, so ``Ball/Real.lean`` can never be
    answered by ``.../SmallBall/Real.lean`` the way a string ``endswith`` test
    would answer it.
    """
    table: Dict[str, Set[str]] = defaultdict(set)
    for path in paths:
        parts = path.split("/")
        for index in range(len(parts)):
            table["/".join(parts[index:])].add(path)
    return table


# ---------------------------------------------------------------------------
# Extraction
# ---------------------------------------------------------------------------


class Citation(NamedTuple):
    """One citation occurrence, after unescaping and brace expansion.

    There is no field for an exemption because there is no exemption channel: a
    citation carries what the document wrote and where, and nothing else.
    """

    target: str
    line: int
    variant: str
    token: str


def scan_units(line: str, is_tex: bool, in_verbatim: bool) -> List[Tuple[str, str]]:
    """Split a line into ``(variant, text)`` chunks that cover its ``.lean`` hits.

    Verbatim and Markdown lines are scannable whole. In LaTeX prose the macro
    arguments are scanned first and the whole macro invocation is then blanked,
    so ``\\texttt{Foo/Bar.lean}`` yields the argument once and the residue scan
    still sees bare tokens written outside any macro. The blanking preserves
    column positions and removes no ``.lean``, so the union of the chunks
    accounts for exactly the occurrences of the original line.
    """
    if in_verbatim:
        return [("verbatim", line)]
    if not is_tex:
        return [("bare", line)]
    units: List[Tuple[str, str]] = []
    masked = list(line)
    for match in MACRO.finditer(line):
        units.append(("macro", match.group(1)))
        for index in range(match.start(), match.end()):
            masked[index] = " "
    units.append(("bare", "".join(masked)))
    return units


def acknowledge_non_citations(text: str, spans: List[Tuple[int, int]]) -> int:
    """Count the ``.lean`` occurrences outside ``spans`` that ``NON_CITATION`` explains.

    An occurrence is acknowledged only if the text ending there is one of the
    enumerated spellings *and* it is delimited on both sides. Without the
    delimiter test the ``".lean"`` entry alone would match at every position and
    the coverage audit would acknowledge everything, including exactly the
    uncovered variants it exists to expose.
    """
    covered = bytearray(len(text))
    for start, end in spans:
        for index in range(start, end):
            covered[index] = 1
    acknowledged = 0
    for match in re.finditer(re.escape(".lean"), text):
        start, end = match.start(), match.end()
        if covered[start]:
            continue
        for spelling in NON_CITATION:
            begin = end - len(spelling)
            if begin < 0 or text[begin:end] != spelling:
                continue
            left = text[begin - 1] if begin > 0 else ""
            right = text[end] if end < len(text) else ""
            if left and left not in NON_CITATION_LEFT_DELIMITERS:
                continue
            if right and right in TOKEN_EDGE_CHARS:
                continue
            acknowledged += 1
            break
    return acknowledged


def extract(target: str, text: str) -> Tuple[List[Citation], List[str]]:
    """Extract every citation from a document and audit the extractor's coverage.

    Returns ``(citations, coverage_failures)``. The second list is the keystone
    guard: it holds one entry per line whose raw ``.lean`` count differs from the
    number of tokens attributed to it, plus one entry if the per-file totals
    disagree (an attribution bug that cancels across lines).

    The function reads the document only as a source of tokens. It parses no
    instructions out of it -- no exemption directive, no comment syntax, no
    fenced-block scope -- so the only thing a document can do to this pass is
    contain more or fewer citations.
    """
    is_tex = target.endswith(".tex")
    lines = text.split("\n")
    citations: List[Citation] = []
    coverage: List[str] = []

    verbatim_env: Optional[str] = None
    pending_wrap: Optional[Tuple[int, str]] = None
    captured_total = 0
    raw_total = 0

    for number, line in enumerate(lines, start=1):
        raw = line.count(".lean")
        raw_total += raw

        in_verbatim = verbatim_env is not None
        opened = verbatim_environment_opened(line) if is_tex else None
        begins = opened is not None
        ends = bool(
            is_tex
            and verbatim_env is not None
            and verbatim_environment_closes(line, verbatim_env)
        )
        # The delimiter line is scanned as ordinary prose rather than skipped:
        # a ``.lean`` written in ``\begin{Verbatim}[label=Foo.lean]`` would
        # otherwise escape the coverage arithmetic entirely.
        verbatim_line = in_verbatim and not begins and not ends

        report_line = number
        scan_text = line
        wrapped = False

        if verbatim_line:
            continues = (
                pending_wrap is not None
                and bool(WRAP_CONTINUATION.match(line))
                and bool(WRAP_PREFIX.match(pending_wrap[1]))
            )
            if continues and pending_wrap is not None:
                report_line = pending_wrap[0]
                scan_text = pending_wrap[1] + line.strip()
                wrapped = True
            pending_wrap = None
            # ``rstrip`` and not ``strip``: an indented line is a tree entry, not
            # a wrapped source line, and stripping its indentation first would
            # let ``    Inequalities/`` join a column-0 ``GKS.lean`` below it --
            # rebuilding a path out of tree layout, which is the one inference
            # this tool exists to refuse.
            candidate = scan_text.rstrip()
            if raw == 0 and WRAP_PREFIX.match(candidate):
                pending_wrap = (report_line, candidate)

        if raw or ".lean" in scan_text:
            captured = 0
            for unit_variant, unit_text in scan_units(scan_text, is_tex, verbatim_line):
                if ".lean" not in unit_text:
                    continue
                unescaped = unescape(unit_text)
                spans: List[Tuple[int, int]] = []
                for match in TOKEN.finditer(unescaped):
                    spans.append((match.start(), match.end()))
                    raw_token = match.group(0)
                    captured += 1
                    token_variant = "verbatim-wrap" if wrapped else unit_variant
                    if "{" in raw_token:
                        token_variant += "+brace"
                    # What the document wrote, not what the pattern could reach.
                    # A glued match is charged whole and is never brace-expanded:
                    # expanding it would hand the resolver alternatives nobody
                    # wrote, which is the same repair by another route.
                    written = glued_text(unescaped, match.start(), match.end())
                    if written != raw_token:
                        token_variant += "+glued"
                        expansions = [written]
                    else:
                        expansions = expand(raw_token)
                    for expanded in expansions:
                        citations.append(
                            Citation(
                                target=target,
                                line=report_line,
                                variant=token_variant,
                                token=expanded,
                            )
                        )
                captured += acknowledge_non_citations(unescaped, spans)
            captured_total += captured
            if captured != raw:
                snippet = line.strip()
                if len(snippet) > 160:
                    snippet = snippet[:160] + "..."
                coverage.append(
                    f"COVERAGE {target}:{number} raw={raw} captured={captured} :: {snippet}"
                )

        # Verbatim state for the next line. With ``pending_wrap`` this is the
        # whole of the per-line state machine, and both are extraction state:
        # one line can change how the next is *read* (a wrapped path rejoined
        # into the path the document wrote), never whether it is charged. The
        # extractor holds no pending or active exemption of any kind.
        if begins:
            verbatim_env = opened
            pending_wrap = None
        elif ends:
            verbatim_env = None
            pending_wrap = None

    if captured_total != raw_total:
        coverage.append(
            f"COVERAGE {target}: file totals disagree raw={raw_total} captured={captured_total}"
        )
    return citations, coverage


# ---------------------------------------------------------------------------
# Classification
# ---------------------------------------------------------------------------


class Finding(NamedTuple):
    """One classified citation (or self-reference) worth reporting."""

    cls: str
    target: str
    token: str
    line: int
    variant: str


class Resolver:
    """Answers "does this citation point at a file this repository has?".

    Holds exactly one table, built from the tracked set. There is no per-tag or
    per-history table: a path that exists only in an archive tag, in an older
    commit or in an untracked copy is not a file this repository has, and no
    argument written in a document can add a second table to consult. Every
    method is total, pure and deterministic.
    """

    def __init__(self, tracked: Sequence[str]) -> None:
        self.tracked = list(tracked)
        self.table = suffix_map(self.tracked)

    def matches(self, token: str) -> Set[str]:
        """Return the tracked paths ``token`` is a component-aligned suffix of."""
        return self.table.get(token, set())


def classify(citation: Citation, resolver: Resolver) -> Tuple[str, Optional[str]]:
    """Return ``(class, resolved_path)`` for one citation.

    ``resolved_path`` is set only for ``RESOLVED``; the caller checks it against
    ``ALLOWED_TRACKED_PREFIXES`` (R10). The order of the tests is the decision
    table of the module docstring, and there is no branch that turns "several
    matches" or "no directory component" into a pass.

    The function's arguments are the whole of its input: a token and the tracked
    suffix table. It cannot see the document's prose, so no wording anywhere can
    reach this decision -- which is what makes "there is no exemption channel" a
    property of the code rather than a promise about how it is used.
    """
    token = normalise(citation.token)
    if token is None:
        return (MALFORMED, None)

    hits = resolver.matches(token)
    if len(hits) == 0:
        return (MISSING, None)
    if len(hits) >= 2:
        return (AMBIGUOUS, None)
    if "/" not in token:
        return (BASENAME_ONLY, None)
    return (RESOLVED, next(iter(hits)))


def selfref_findings(target: str, text: str, citations: Sequence[Citation]) -> List[Finding]:
    """Report paragraphs whose repeated citation makes their sentence vacuous.

    Two citations in one blank-line-delimited paragraph whose paths are
    component-aligned suffixes of each other, with a re-export cue on some line
    strictly between them, are reported once per ``(paragraph, token pair)``.
    The paragraph is the unit of the finding, so a paragraph that cites the same
    file eleven times is one self-reference and not fifty-five.

    Charge-only by construction: a cue word this list does not know, or one
    split across a line break, under-detects, and nothing here can make a
    citation resolve. Its silence must therefore never be read as "no vacuous
    sentences remain".

    Known limitation, stated rather than papered over: "blank-line-delimited
    paragraph" is a LaTeX notion. ``docs/index.md`` has 76 blank lines in 2,331,
    so one Markdown "paragraph" can hold 674 citations and any cue word anywhere
    in that block pairs everything with everything. The Markdown rows this
    produces are consequently dominated by that artefact -- which is precisely
    why this class is advisory, separately baselined, and outside the exit code.
    """
    lines = text.split("\n")
    # Cue positions as a prefix sum: "is there a cue strictly between lines a
    # and b" then costs O(1), which matters because the Markdown target has
    # paragraphs with hundreds of citations.
    cue_upto = [0] * (len(lines) + 2)
    running = 0
    for number, line in enumerate(lines, start=1):
        if SELFREF_CUE.search(line):
            running += 1
        cue_upto[number] = running
    for number in range(len(lines) + 1, len(cue_upto)):
        cue_upto[number] = running

    def cue_between(first: int, second: int) -> bool:
        """Whether some line strictly between ``first`` and ``second`` holds a cue."""
        if second - first < 2:
            return False
        return cue_upto[second - 1] - cue_upto[first] > 0

    paragraph_of: Dict[int, int] = {}
    index = 0
    for number, line in enumerate(lines, start=1):
        if not line.strip():
            index += 1
        paragraph_of[number] = index

    # Per paragraph, per token: the first and last line that cites it. For two
    # token groups the earliest citation of one and the latest of the other span
    # the widest interval, so testing that single pair decides the whole group
    # pair exactly -- no approximation, and no quadratic blow-up in occurrences.
    spans: Dict[int, Dict[str, Tuple[int, int, str]]] = defaultdict(dict)
    for citation in citations:
        paragraph = paragraph_of.get(citation.line, -1)
        entry = spans[paragraph].get(citation.token)
        if entry is None:
            spans[paragraph][citation.token] = (citation.line, citation.line, citation.variant)
        else:
            spans[paragraph][citation.token] = (
                min(entry[0], citation.line),
                max(entry[1], citation.line),
                entry[2],
            )

    findings: List[Finding] = []
    for paragraph in sorted(spans):
        tokens = sorted(spans[paragraph])
        for left_index, left in enumerate(tokens):
            for right in tokens[left_index:]:
                if not suffix_related(left, right):
                    continue
                left_first, left_last, variant = spans[paragraph][left]
                right_first, right_last, _ = spans[paragraph][right]
                if cue_between(left_first, right_last):
                    first, second = left, right
                    line = left_first
                elif cue_between(right_first, left_last):
                    first, second = right, left
                    line = right_first
                else:
                    continue
                findings.append(
                    Finding(
                        cls=SELFREF,
                        target=target,
                        token=f"{first} >> {second}",
                        line=line,
                        variant=variant,
                    )
                )
    return findings


def suffix_related(left: str, right: str) -> bool:
    """Return whether one path is a component-aligned suffix of the other."""
    first, second = left.split("/"), right.split("/")
    length = min(len(first), len(second))
    return first[-length:] == second[-length:]


# ---------------------------------------------------------------------------
# Audit
# ---------------------------------------------------------------------------


class Report(NamedTuple):
    """Everything one run produced, including what it failed to do."""

    targets: List[str]
    visited: List[str]
    tracked: int
    citations: Dict[str, int]
    raw_occurrences: Dict[str, int]
    counts: Dict[str, Dict[str, int]]
    findings: List[Finding]
    selfrefs: List[Finding]
    coverage: List[str]
    hard: List[str]

    @property
    def ok_structurally(self) -> bool:
        """Whether the run itself is trustworthy (no coverage or hard failure)."""
        return not self.coverage and not self.hard


def audit(targets: Optional[Sequence[str]] = None) -> Report:
    """Audit ``targets`` (default :data:`TARGETS`) and return the full report.

    Never raises on document content: a malformed document produces findings,
    and an environment fault (git unavailable, target missing) produces a hard
    failure. Both are visible in the returned report rather than as a traceback,
    so a caller cannot mistake an aborted run for a clean one.
    """
    selected = list(targets) if targets is not None else list(TARGETS)
    visited: List[str] = []
    hard: List[str] = []
    coverage: List[str] = []
    findings: List[Finding] = []
    selfrefs: List[Finding] = []
    citation_counts: Dict[str, int] = {}
    raw_counts: Dict[str, int] = {}
    counts: Dict[str, Dict[str, int]] = {}

    try:
        tracked = tracked_lean_files()
        tracked_all = tracked_paths()
    except GitError as exc:
        return Report(
            targets=selected,
            visited=[],
            tracked=0,
            citations={},
            raw_occurrences={},
            counts={},
            findings=[],
            selfrefs=[],
            coverage=[],
            hard=[f"GIT {exc}"],
        )

    if len(tracked) < MIN_TRACKED_LEAN:
        hard.append(
            f"VACUOUS resolution set has {len(tracked)} tracked .lean files, "
            f"below MIN_TRACKED_LEAN={MIN_TRACKED_LEAN}"
        )
    resolver = Resolver(tracked)

    for target in selected:
        path = REPO_ROOT / target
        if not path.is_file():
            hard.append(f"TARGET {target}: not a file")
            continue
        if target not in tracked_all:
            hard.append(f"TARGET {target}: not tracked by git")
            continue
        text = path.read_text(encoding="utf-8")
        citations, target_coverage = extract(target, text)
        visited.append(target)
        coverage.extend(target_coverage)
        raw_counts[target] = text.count(".lean")
        citation_counts[target] = len(citations)

        floor = MIN_CITATIONS.get(target)
        if floor is None:
            # Renaming a default target without measuring a floor for it would
            # silently drop that target's anti-vacuity guard to 1.
            if target in TARGETS:
                hard.append(f"VACUOUS {target}: default target with no measured citation floor")
            floor = DEFAULT_MIN_CITATIONS
        if len(citations) < floor:
            hard.append(
                f"VACUOUS {target}: {len(citations)} citations, below floor {floor}"
            )

        per_class: Dict[str, int] = {name: 0 for name in ALL_CLASSES}
        for citation in citations:
            verdict, resolved_path = classify(citation, resolver)
            per_class[verdict] += 1
            if resolved_path is not None and not resolved_path.startswith(
                ALLOWED_TRACKED_PREFIXES
            ):
                hard.append(
                    f"CONTAMINATED {target}:{citation.line}: {citation.token} resolved to "
                    f"{resolved_path}, outside {ALLOWED_TRACKED_PREFIXES}"
                )
            if verdict in FINDING_CLASSES:
                findings.append(
                    Finding(verdict, target, citation.token, citation.line, citation.variant)
                )
        target_selfrefs = selfref_findings(target, text, citations)
        per_class[SELFREF] = len(target_selfrefs)
        selfrefs.extend(target_selfrefs)
        counts[target] = per_class

    # Scanned-set honesty, in the ``audit_gate.unvisited_failures`` spirit: a run
    # that opened no document is the cheapest possible false pass (empty
    # ``TARGETS``, or a filter added to the loop above), and "0 findings" from it
    # would otherwise be indistinguishable from a clean tree.
    if not visited:
        hard.append("VACUOUS no target was scanned; the run checked nothing")
    for target in selected:
        if target in visited:
            continue
        if not any(item.startswith(f"TARGET {target}:") for item in hard):
            hard.append(f"TARGET {target}: enumerated but never scanned")

    return Report(
        targets=selected,
        visited=visited,
        tracked=len(tracked),
        citations=citation_counts,
        raw_occurrences=raw_counts,
        counts=counts,
        findings=findings,
        selfrefs=selfrefs,
        coverage=coverage,
        hard=hard,
    )


# ---------------------------------------------------------------------------
# Baseline and ratchet
# ---------------------------------------------------------------------------


class Row(NamedTuple):
    """One baseline row: a finding key, its multiplicity, and a payload line."""

    cls: str
    target: str
    token: str
    count: int
    first_line: int


def aggregate(findings: Sequence[Finding]) -> List[Row]:
    """Aggregate findings into baseline rows keyed on ``(class, target, token)``.

    Line numbers are payload, not key: they churn on every unrelated edit, and a
    baseline that changed with them would be undiffable and would stop being
    read.
    """
    counter: Counter = Counter()
    first: Dict[Tuple[str, str, str], int] = {}
    for finding in findings:
        key = (finding.cls, finding.target, finding.token)
        counter[key] += 1
        if key not in first or finding.line < first[key]:
            first[key] = finding.line
    return [
        Row(cls, target, token, count, first[(cls, target, token)])
        for (cls, target, token), count in sorted(counter.items())
    ]


def render_baseline(report: Report) -> str:
    """Render the canonical TSV: header comments, census lines, then the rows.

    A run that is not structurally sound (coverage mismatch or hard failure)
    renders **no census and no rows**, only what went wrong. This is the same
    rule :func:`format_text` states, applied where it matters most: the TSV is
    the count-of-record, so a census printed here from a provably incomplete
    extractor is the exact artefact the module docstring says must stop being
    produced -- and it would be quoted as a count precisely because it is the
    machine-readable form.
    """
    lines = [
        "# citation-audit v1 baseline -- the count-of-record for .lean citations.",
        "#",
        "# Rows are keyed on (class, target, token) with a multiplicity; first_line is",
        "# payload and is excluded from the ratchet comparison. SELFREF rows are",
        "# advisory: they are recorded so drift is visible in review, and they never",
        "# gate the exit code.",
        "#",
        "# Regenerate with:",
        "#   python3 scripts/citation_audit.py --write-baseline scripts/audit/citation_baseline.tsv",
        "# A baseline that grew without a stated reason is a review signal: remediation",
        "# is supposed to shrink it monotonically.",
    ]
    if not report.ok_structurally:
        lines.append("#")
        lines.append(
            "# UNTRUSTWORTHY RUN: the extractor did not account for every .lean "
            "occurrence,"
        )
        lines.append("# so no census and no rows are published. What failed:")
        for item in list(report.coverage) + list(report.hard):
            lines.append(f"#!\t{item}")
        return "\n".join(lines) + "\n"
    lines.append(f"#tracked\t{report.tracked}")
    for target in report.visited:
        census = ",".join(
            f"{name}={report.counts[target][name]}"
            for name in ALL_CLASSES
            if report.counts[target][name]
        )
        lines.append(
            f"#census\t{target}\t{report.citations[target]}\t"
            f"{report.raw_occurrences[target]}\t{census}"
        )
    lines.append("class\ttarget\ttoken\tcount\tfirst_line")
    for row in aggregate(list(report.findings) + list(report.selfrefs)):
        lines.append(f"{row.cls}\t{row.target}\t{row.token}\t{row.count}\t{row.first_line}")
    return "\n".join(lines) + "\n"


def read_baseline(path: Path) -> Tuple[Counter, Dict[str, Dict[str, int]], int]:
    """Read a baseline file into ``(multiset, census, tracked)``.

    The census comment lines are machine-readable on purpose: the committed
    baseline records ``RESOLVED`` too, which the rows cannot, so a pin test can
    detect a silent change in the extractor rather than only in the debt.
    """
    multiset: Counter = Counter()
    census: Dict[str, Dict[str, int]] = {}
    tracked = 0
    for line in path.read_text(encoding="utf-8").split("\n"):
        if not line.strip():
            continue
        if line.startswith("#tracked\t"):
            tracked = int(line.split("\t")[1])
            continue
        if line.startswith("#census\t"):
            fields = line.split("\t")
            target = fields[1]
            entries = {}
            for item in fields[4].split(",") if len(fields) > 4 and fields[4] else []:
                name, _, value = item.partition("=")
                entries[name] = int(value)
            entries["citations"] = int(fields[2])
            entries["raw"] = int(fields[3])
            census[target] = entries
            continue
        if line.startswith("#") or line.startswith("class\t"):
            continue
        fields = line.split("\t")
        multiset[(fields[0], fields[1], fields[2])] += int(fields[3])
    return (multiset, census, tracked)


def ratchet(current: Counter, baseline: Counter) -> Tuple[List[str], int]:
    """Compare finding multisets; return ``(regressions, cleared count)``.

    A totals-only comparison is not enough: one fix plus one regression nets to
    zero and the document silently rots. The comparison is therefore per key,
    and a key absent from the baseline is a regression at count one.
    """
    regressions: List[str] = []
    cleared = 0
    for key, count in sorted(current.items()):
        allowed = baseline.get(key, 0)
        if count > allowed:
            cls, target, token = key
            regressions.append(
                f"NEW {cls} {target} {token} (baseline {allowed}, now {count})"
            )
    for key, count in baseline.items():
        cleared += max(0, count - current.get(key, 0))
    return (regressions, cleared)


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------


def format_tsv(report: Report) -> str:
    """Render the canonical TSV report (same shape as the baseline)."""
    return render_baseline(report)


def format_json(report: Report) -> str:
    """Render the report as JSON for tooling.

    ``trustworthy`` is the machine-readable form of the suppression rule: when
    it is ``false``, ``counts`` and ``findings`` are empty because they were
    withheld, not because the documents were clean. A consumer that reads only
    ``findings`` therefore sees nothing to act on and nothing to quote, which is
    the intended fail-closed reading of an incomplete run.
    """
    trustworthy = report.ok_structurally
    payload = {
        "schema": 1,
        "trustworthy": trustworthy,
        "tracked_lean_files": report.tracked,
        "targets": [
            {
                "path": target,
                "citations": report.citations.get(target, 0),
                "raw_occurrences": report.raw_occurrences.get(target, 0),
            }
            for target in report.visited
        ],
        "coverage": {"ok": not report.coverage, "mismatches": report.coverage},
        "hard_failures": report.hard,
        "counts": (
            {target: report.counts[target] for target in report.visited}
            if trustworthy
            else {}
        ),
        "findings": [
            {
                "class": finding.cls,
                "target": finding.target,
                "token": finding.token,
                "line": finding.line,
                "variant": finding.variant,
            }
            for finding in list(report.findings) + list(report.selfrefs)
        ]
        if trustworthy
        else [],
    }
    return json.dumps(payload, indent=1, sort_keys=True) + "\n"


def format_text(
    report: Report, regressions: Sequence[str], cleared: int, strict: bool = False
) -> str:
    """Render the human report.

    A coverage failure or a hard failure suppresses the finding census entirely,
    the same rule :func:`render_baseline` and :func:`format_json` apply, so no
    format publishes numbers a structurally unsound run produced. Printing "280
    dangling" from an extractor that is provably incomplete is the artefact this
    tool exists to stop producing, so the run reports what it cannot do instead
    of what it thinks it found.
    """
    out: List[str] = []
    out.append(f"== citation audit ({report.tracked} tracked .lean files) ==")
    for target in report.visited:
        out.append(
            f"  {target}: {report.raw_occurrences[target]} raw .lean occurrences, "
            f"{report.citations[target]} citations"
        )
    if report.coverage:
        out.append("")
        out.append(f"COVERAGE FAIL: {len(report.coverage)} unaccounted .lean occurrence(s).")
        out.append("The extractor is incomplete, so the findings below are NOT reported.")
        for item in report.coverage[:40]:
            out.append(f"  {item}")
        if len(report.coverage) > 40:
            out.append(f"  ... {len(report.coverage) - 40} more")
    else:
        out.append("coverage: OK (every raw .lean occurrence accounted for)")
    if report.hard:
        out.append("")
        out.append(f"HARD FAILURES: {len(report.hard)}")
        for item in report.hard:
            out.append(f"  {item}")
        if not report.coverage:
            out.append("The run is not trustworthy, so the findings below are NOT reported.")
    if report.ok_structurally:
        out.append("")
        for target in report.visited:
            census = "  ".join(
                f"{name}={report.counts[target][name]}"
                for name in ALL_CLASSES
                if report.counts[target][name]
            )
            out.append(f"{target}: {census}")
        unresolved = len(report.findings)
        out.append("")
        out.append(f"findings (gating): {unresolved}    self-references (advisory): "
                   f"{len(report.selfrefs)}")
        label = "strict" if strict else "ratchet"
        if regressions:
            suffix = "unresolved citation(s)" if strict else "finding(s) above the baseline"
            out.append(f"{label}: FAIL -- {len(regressions)} {suffix}")
            for item in regressions[:40]:
                out.append(f"  {item}")
            if len(regressions) > 40:
                out.append(f"  ... {len(regressions) - 40} more")
        elif strict:
            out.append("strict: OK -- every citation resolves")
        else:
            out.append(f"ratchet: OK -- {cleared} finding(s) cleared, 0 new")
        out.append("(use --format tsv for the full per-token list)")
    return "\n".join(out) + "\n"


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------


def main(argv: Optional[Sequence[str]] = None) -> int:
    """Run the citation audit and return the process exit code."""
    parser = argparse.ArgumentParser(
        description="Fail-closed audit of .lean citations in the project's documents."
    )
    parser.add_argument(
        "--targets",
        nargs="+",
        metavar="PATH",
        help="Documents to audit (default: %s)." % ", ".join(TARGETS),
    )
    parser.add_argument(
        "--format",
        choices=("text", "tsv", "json"),
        default="text",
        help="Report format; tsv is the count-of-record.",
    )
    parser.add_argument(
        "--baseline",
        metavar="PATH",
        default=str(BASELINE_FILE),
        help="Baseline to ratchet against (default: scripts/audit/citation_baseline.tsv).",
    )
    parser.add_argument(
        "--write-baseline",
        metavar="PATH",
        help="Regenerate a baseline file (every default target must be scanned).",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Require zero unresolved citations, not merely no regression.",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="Run this tool's own test suite (scripts/test_citation_audit.py).",
    )
    args = parser.parse_args(list(argv) if argv is not None else None)

    if args.self_test:
        sys.path.insert(0, str(Path(__file__).resolve().parent))
        from test_citation_audit import run_suite  # noqa: PLC0415

        return run_suite()

    report = audit(args.targets)

    if args.write_baseline:
        destination = Path(args.write_baseline)
        if not destination.is_absolute():
            destination = REPO_ROOT / destination
        if not report.ok_structurally:
            print(format_text(report, [], 0), end="")
            print("refusing to write a baseline from an untrustworthy run")
            return 1
        if set(report.visited) != set(TARGETS):
            # The file is the count-of-record for *all* targets, and it is
            # rendered from this run alone, so a partial run would silently drop
            # every row of the targets it did not open -- shrinking the recorded
            # debt without fixing a single citation, and leaving the ratchet with
            # nothing to compare against later.
            missing = sorted(set(TARGETS) - set(report.visited))
            extra = sorted(set(report.visited) - set(TARGETS))
            print(format_text(report, [], 0), end="")
            print(
                "refusing to write a baseline from a partial target set "
                f"(not scanned: {missing or 'none'}; not a default target: {extra or 'none'})"
            )
            return 1
        previous: Counter = Counter()
        if destination.is_file():
            previous, _, _ = read_baseline(destination)
        current: Counter = Counter()
        for row in aggregate(list(report.findings) + list(report.selfrefs)):
            current[(row.cls, row.target, row.token)] = row.count
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(render_baseline(report), encoding="utf-8")
        added = sum(max(0, count - previous.get(key, 0)) for key, count in current.items())
        removed = sum(max(0, count - current.get(key, 0)) for key, count in previous.items())
        print(f"wrote {destination}")
        print(f"delta: +{added} finding(s), -{removed} finding(s) versus the previous file")
        return 0

    current = Counter()
    for row in aggregate(list(report.findings)):
        current[(row.cls, row.target, row.token)] = row.count
    advisory = Counter()
    for row in aggregate(list(report.selfrefs)):
        advisory[(row.cls, row.target, row.token)] = row.count

    regressions: List[str] = []
    cleared = 0
    baseline_path = Path(args.baseline)
    if not baseline_path.is_absolute():
        baseline_path = REPO_ROOT / baseline_path
    if args.strict:
        regressions = [
            f"UNRESOLVED {finding.cls} {finding.target}:{finding.line} {finding.token}"
            for finding in report.findings
        ]
    elif report.ok_structurally:
        if not baseline_path.is_file():
            report.hard.append(f"BASELINE {baseline_path}: missing")
        else:
            baseline, _, _ = read_baseline(baseline_path)
            gating = Counter(
                {key: count for key, count in baseline.items() if key[0] in FINDING_CLASSES}
            )
            audited = set(report.visited)
            gating = Counter(
                {key: count for key, count in gating.items() if key[1] in audited}
            )
            regressions, cleared = ratchet(current, gating)
            advisory_baseline = Counter(
                {
                    key: count
                    for key, count in baseline.items()
                    if key[0] in ADVISORY_CLASSES and key[1] in audited
                }
            )
            advisory_new, _ = ratchet(advisory, advisory_baseline)
            for item in advisory_new:
                print(f"advisory (not gating): {item}")

    if args.format == "tsv":
        print(format_tsv(report), end="")
    elif args.format == "json":
        print(format_json(report), end="")
    else:
        print(format_text(report, regressions, cleared, args.strict), end="")

    ok = report.ok_structurally and not regressions
    if args.format == "text":
        print("citation audit: PASS" if ok else "citation audit: FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
