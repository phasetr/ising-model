#!/usr/bin/env python3
"""Ratchet on *recognized* inventory-claim syntax in canonical prose (Issue #4980).

What this is
------------
Hand-maintained canonical prose in this repository -- Lean module ``/-!``
headers, ``docs/index.md`` and ``tex/proof-guide.tex`` -- carries a second copy
of a mechanically derivable fact: *how many* declarations a module holds, and
*which module* a group of declarations now lives in.  Those sentences are true
when written and false after the next split, which is why the same stale-header
defect has now recurred three times.  The operational rule they violate is the
**split-stability test**: if moving a declaration between modules -- without
changing the mathematical contract -- would make a sentence false, that sentence
does not belong in hand-maintained canonical prose.

This script does exactly one thing: it counts the claim shapes it recognizes and
refuses to let that population grow.

What this is **not**
--------------------
It is **not** a verdict on whether a header is correct, current, or complete.
It never recomputes a declaration count, so it cannot tell a right number from a
wrong one, and it must never be read as saying that headers are clean.  Natural
language expresses extension facts in unlimited forms; five are recognized here
(:data:`CLAIM_CLASSES`) and everything else is invisible to it.  A green run
means "no *recognized* claim shape was added", nothing more, and the report says
so in those words on every invocation.

The predecessor design proposed a second predicate -- flag a header citing a
backticked declaration name that does not exist in the module -- and it was
measured before being dropped: it fires on 751 files / 1692 tokens against ~93
known defects (signal-to-noise ~5 %), because headers legitimately cite upstream
dependencies and because ~39 % of the backticked tokens in claim headers are
glob/brace family patterns (``magnetization{Λ,AlongExhaustion,Infinite}``) that
are not resolvable identifiers by construction.  Making it total would need a
glob expander, i.e. the finite-grammar-growth lane this repository has already
retired twice.  **It is deliberately not implemented here**, and the anti-scope
test suite pins that.

Charge-only
-----------
There is no exemption channel: no allowlist, no "probably fine" bucket, no way
to mark a finding acceptable.  The baseline is a **high-water mark**, not an
allowlist -- an entry says "this claim existed on the pinned commit", never
"this claim is fine".  The tool can charge; it can never exonerate.  That is
what makes it categorically unlike the retired ``safe-to-delete`` scanner: it
certifies no meaning and authorizes no operation.

Ratchet
-------
The population is a **multiset keyed** ``(class, target, token)``
(:data:`BASELINE_FILE`).  A key absent from the baseline, or present with a
larger count than the baseline records, fails the run.  Fixing one claim
therefore cannot pay for introducing another: there is no scalar to offset.  A
key whose live count is *below* the baseline is reported as slack to be re-pinned
with ``--baseline``, and never fails.

At baseline zero the rule becomes an absolute lexical ban on the recognized
shapes and the checker stays wired in permanently.  Baseline *maintenance* ends
there; the defect does not become impossible, so the checker is frozen, not
retired.

Conservation (the reason a silent skip cannot hide here)
--------------------------------------------------------
Every run asserts three identities, and a failure of any of them **suppresses
the findings report in every output format** -- a run that cannot account for
its own inputs reports nothing rather than something reassuring:

``K0``
    every target the tracked-file query returned was opened and accounted for.
    A read error is a failure, never a skip.

``K1``
    for every target and every claim class, the number of *records* the pipeline
    produced equals the number of raw anchor matches counted directly on the
    flattened file.  The two sides are computed by structurally different code
    (a plain ``findall`` versus mask -> flatten -> ``finditer`` -> per-match
    extractor), so an extractor that returns ``None`` for a token it cannot
    resolve -- the shape of the ``_resolve_fragment`` zero-match fail-open this
    repository has already been bitten by -- shows up as a hard failure instead
    of a quietly shorter report.

``K2``
    the anchor matches found on the prose-masked text equal the raw anchor
    matches whose span lies inside a single prose region.  This is the mask's
    own cross-check: a nesting bug in the comment scanner moves sites between
    the two sides and fails here.

Unparseable and missing inputs are **charged**, not skipped: a module with no
``/-!`` block (:data:`MISSING_DOC`), a file whose comment structure does not
terminate (:data:`UNTERMINATED`), and an anchor that does not sit inside prose
(:data:`NON_PROSE`) are all findings.  Global totals are deliberately *not*
pinned -- they move legitimately as modules are added -- so the conservation
laws are per-run, not frozen scalars.

Scope
-----
The tracked set only (``git ls-files``), never a filesystem walk: the source of
truth for "which files exist" is the VCS index, and this repository has been
bitten by scanners that read untracked or ignored content.

Usage
-----
    python3 scripts/header_inventory_claim_ratchet.py             # --check (default)
    python3 scripts/header_inventory_claim_ratchet.py --baseline  # re-pin (stdout)
    python3 scripts/header_inventory_claim_ratchet.py --findings  # every finding, TSV
    python3 scripts/header_inventory_claim_ratchet.py --self-test # run the test suite

Exit code 0 iff the conservation laws hold and no key is new or grown; 1
otherwise.
"""

from __future__ import annotations

import argparse
import bisect
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path
from typing import Callable, Iterable, NamedTuple

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent
BASELINE_FILE = SCRIPT_DIR / "audit" / "header_claim_baseline.tsv"

#: The Lean source root whose module docstrings are canonical prose.
LEAN_ROOT = "IsingModel"

#: The hand-maintained canonical documents.  ``docs/index.md`` is the single
#: source of truth for progress and ``tex/proof-guide.tex`` is the published
#: proof guide; both carry the same claim shapes as the Lean headers.
DOC_TARGETS: tuple[str, ...] = ("docs/index.md", "tex/proof-guide.tex")

#: The sentinel a masked-out (non-prose) character becomes.  It appears in no
#: source file and in no anchor, so a regex cannot match across it.
MASK = "\x00"


# --------------------------------------------------------------------------
# Comment / prose decomposition
# --------------------------------------------------------------------------


class Decomposition(NamedTuple):
    """The prose regions of one source file.

    ``regions`` are half-open ``(start, end)`` spans of *comment bodies* in the
    original text, delimiters excluded, in increasing order and non-overlapping.
    ``terminated`` is ``False`` when the scan ended inside a block comment or a
    string literal, which is charged rather than ignored.
    """

    regions: tuple[tuple[int, int], ...]
    terminated: bool


#: The only three-character sequences that can change the scanner's state, plus
#: the string delimiter.  Driving the scan off ``re.search`` rather than a
#: per-character loop keeps a 1900-file pass well under a second.
_SCAN_TOKEN = re.compile(r"--|/-|-/|\"")

#: A string literal body after the opening quote, honouring backslash escapes.
_STRING_BODY = re.compile(r'(?:[^"\\]|\\.)*"')


def decompose(text: str) -> Decomposition:
    """Return the comment-body regions of Lean-like ``text``.

    Lean block comments **nest**: ``/- outer /- inner -/ still a comment -/`` is
    one comment, and a non-greedy ``/-.*?-/`` closes it at the first ``-/``,
    which would split one region into a region plus a stretch of apparent code.
    That is not a cosmetic error here -- a claim sitting after the inner ``-/``
    would move from the prose side to the non-prose side of ``K2`` -- so the
    nesting is tracked explicitly.

    ``--`` inside a block comment, and ``/-`` inside a line comment or a string
    literal, are inert.  Markdown and TeX have no such structure, so their whole
    text is one region (see :func:`decompose_document`).
    """
    regions: list[tuple[int, int]] = []
    index = 0
    depth = 0
    start = 0
    length = len(text)
    while index < length:
        match = _SCAN_TOKEN.search(text, index)
        if match is None:
            break
        token = match.group(0)
        if depth > 0:
            if token == "/-":
                depth += 1
            elif token == "-/":
                depth -= 1
                if depth == 0:
                    regions.append((start, match.start()))
            index = match.end()
            continue
        if token == "/-":
            depth = 1
            start = match.end()
            index = match.end()
            continue
        if token == "--":
            end = text.find("\n", match.end())
            end = length if end < 0 else end
            regions.append((match.end(), end))
            index = end
            continue
        if token == '"':
            body = _STRING_BODY.match(text, match.end())
            index = length if body is None else body.end()
            continue
        # A stray ``-/`` at depth 0 is not a comment boundary; step past it.
        index = match.end()
    return Decomposition(regions=tuple(regions), terminated=depth == 0)


def decompose_document(text: str) -> Decomposition:
    """Return the whole of ``text`` as one prose region.

    ``docs/index.md`` and ``tex/proof-guide.tex`` are prose end to end; there is
    no code/comment distinction to get wrong, so the decomposition is total and
    ``K2`` degenerates to "every anchor is in prose" for them -- which is the
    honest statement, not a weakening.
    """
    return Decomposition(regions=((0, len(text)),), terminated=True)


def apply_mask(text: str, regions: Iterable[tuple[int, int]]) -> str:
    """Return ``text`` with every character outside ``regions`` replaced by :data:`MASK`.

    Length is preserved, so offsets stay comparable with the original.
    """
    out: list[str] = []
    previous = 0
    for start, end in regions:
        out.append(MASK * (start - previous))
        out.append(text[start:end])
        previous = end
    out.append(MASK * (len(text) - previous))
    return "".join(out)


# --------------------------------------------------------------------------
# Whitespace flattening (with an offset map back to the original text)
# --------------------------------------------------------------------------


class Flat(NamedTuple):
    """Whitespace-flattened text plus the original offset of each character."""

    text: str
    offsets: tuple[int, ...]

    def origin(self, index: int) -> int:
        """Return the original offset of flattened character ``index``."""
        if not self.offsets:
            return 0
        return self.offsets[min(index, len(self.offsets) - 1)]


#: One maximal whitespace run or one maximal non-whitespace run.  Flattening
#: run-by-run rather than character-by-character is what keeps a 1900-file pass
#: (about 15 MB of prose) inside a second.
_RUN = re.compile(r"\s+|\S+")


def flatten(text: str) -> Flat:
    """Collapse every whitespace run to a single space, keeping an offset map.

    Claim sentences wrap across lines (``Narrow child module for\\nthe 12 ...``),
    so every anchor is matched on the flattened text; the offset map is what
    turns a flattened match back into a line number.  :data:`MASK` is not
    whitespace, so masked regions survive flattening as solid runs that no
    anchor can match across.
    """
    chars: list[str] = []
    offsets: list[int] = []
    for run in _RUN.finditer(text):
        if text[run.start()].isspace():
            chars.append(" ")
            offsets.append(run.start())
        else:
            chars.append(run.group(0))
            offsets.extend(range(run.start(), run.end()))
    return Flat(text="".join(chars), offsets=tuple(offsets))


def line_starts(text: str) -> tuple[int, ...]:
    """Return the offset of the first character of every line of ``text``."""
    starts = [0]
    position = text.find("\n")
    while position >= 0:
        starts.append(position + 1)
        position = text.find("\n", position + 1)
    return tuple(starts)


def line_of(starts: tuple[int, ...], offset: int) -> int:
    """Return the 1-based line number holding ``offset``."""
    return bisect.bisect_right(starts, offset)


# --------------------------------------------------------------------------
# Quantities
# --------------------------------------------------------------------------

#: Written-out cardinals.  Unit 4's own scan of this corpus lost 40 % of its
#: recall to a single missing article, and the word forms outnumber the numerals
#: here almost three to one, so both spellings are first-class.
WORD_NUMBERS: dict[str, int] = {
    "one": 1, "two": 2, "three": 3, "four": 4, "five": 5, "six": 6, "seven": 7,
    "eight": 8, "nine": 9, "ten": 10, "eleven": 11, "twelve": 12, "thirteen": 13,
    "fourteen": 14, "fifteen": 15, "sixteen": 16, "seventeen": 17, "eighteen": 18,
    "nineteen": 19, "twenty": 20, "thirty": 30, "forty": 40, "fifty": 50,
}

#: Quantifiers that assert a population without naming its size.  They fail the
#: split-stability test exactly as a numeral does ("the remaining wrappers"
#: changes meaning the moment a sibling module is carved out), so they are
#: charged, with the word itself as the token.
VAGUE_QUANTIFIERS = frozenset(
    {"several", "many", "various", "numerous", "multiple", "both", "remaining", "few"}
)

_WORD_ALTERNATION = "|".join(sorted(WORD_NUMBERS, key=len, reverse=True))

#: A quantity as it appears in prose: a numeral, a cardinal word, or a
#: hyphenated compound (``twenty-four``).
QUANTITY = rf"(?:\d+|(?:{_WORD_ALTERNATION})(?:-(?:{_WORD_ALTERNATION}))?)"

#: The repository-artifact nouns a count can quantify.  Deliberately closed and
#: deliberately *not* including mathematical objects (``parts``, ``ingredients``,
#: ``arguments``, ``cases``): a count of those is a statement about the
#: mathematics and survives a module split, so it is out of scope by
#: construction rather than by an exemption.
INVENTORY_NOUN = (
    r"(?:wrappers?|lemmas?|theorems?|declarations?|corollar(?:y|ies)|instances?"
    r"|definitions?|defs?|specializations?|aliases|alias|statements?|properties"
    r"|modules?|files?|variants?)"
)

#: Characters and words that end a claim: the window between a quantity and its
#: noun may not cross a sentence break, a table-cell boundary, a comment
#: delimiter or a masked region.  Without this the window happily reaches from
#: ``its two arguments.`` in one doc comment into the word ``lemma`` of the
#: declaration underneath it, which is a pure false positive.
_WINDOW = rf"(?:(?!\.\s|;|\||-/|/-)[^{MASK}\n]){{0,70}}?"


def resolve_quantity(raw: str) -> tuple[str, bool]:
    """Return ``(token, is_quantity)`` for the head word ``raw``.

    ``token`` is the normalized claim token: a decimal string for a numeral or
    cardinal word, the lower-cased word for a vague quantifier.  ``is_quantity``
    is ``False`` for anything else, which is *accounted but not charged* -- a
    header reading ``Narrow child module for concrete latticeGraph
    specializations`` states no count, and inventing a charge for it would make
    the tool's population meaningless.
    """
    word = raw.strip().strip(",.;:!?)(`*").lower()
    if word.isdigit():
        return word, True
    if word in VAGUE_QUANTIFIERS:
        return word, True
    if word in WORD_NUMBERS:
        return str(WORD_NUMBERS[word]), True
    if "-" in word:
        parts = word.split("-")
        if len(parts) == 2 and all(part in WORD_NUMBERS for part in parts):
            return str(WORD_NUMBERS[parts[0]] + WORD_NUMBERS[parts[1]]), True
    return word, False


# --------------------------------------------------------------------------
# Claim classes
# --------------------------------------------------------------------------

#: The three referents the measured grammar actually uses.  Recording which one
#: a shape means is the whole reason the classes are separate: ``(9 theorems)``
#: counts part of *this* module while ``The 13 ... now live in `X` `` counts part
#: of a *different* one, and collapsing them would key two unrelated populations
#: to the same module.
THIS_MODULE = "this-module"
THIS_MODULE_SUBSET = "this-module-subset"
OTHER_MODULE = "other-module"

REFERENTS = (THIS_MODULE, THIS_MODULE_SUBSET, OTHER_MODULE)

#: Structural charge classes -- inputs the scan could not inspect.  They are
#: findings rather than skips: a file the checker cannot read must not silently
#: gain a clean bill of health.
MISSING_DOC = "MISSING_MODULE_DOC"
UNTERMINATED = "UNTERMINATED_COMMENT"
NON_PROSE = "NON_PROSE_ANCHOR"


class Claim(NamedTuple):
    """One extracted claim: the ratchet key plus where it was found."""

    kind: str
    target: str
    token: str
    line: int
    charged: bool
    note: str

    @property
    def key(self) -> tuple[str, str, str]:
        """The multiset key of the ratchet."""
        return (self.kind, self.target, self.token)


class ClaimClass(NamedTuple):
    """A recognized claim shape: its anchor, its referent and its extractor.

    ``extract`` receives the flattened text and one anchor match and returns
    ``(token, charged, note)``.  It is **total**: every anchor match yields
    exactly one record, so a token it cannot resolve becomes a charge with a
    note rather than a dropped row.  ``K1`` is what enforces that contract.
    """

    name: str
    referent: str
    anchor: re.Pattern[str]
    extract: Callable[[str, re.Match[str]], tuple[str, bool, str]]
    summary: str


#: The ``Narrow child module`` opener.  ``re.IGNORECASE``, like every other
#: anchor here, and that flag is load-bearing rather than cosmetic: prose is not
#: case-normalized, so the same sentence appears sentence-initially and
#: paragraph-medially (``... moved to a narrow child module ...``), and an anchor
#: keyed to the capitalized spelling silently sees none of the lowercase ones.
#: Missing it here made the largest class -- 68 % of the pinned population --
#: bypassable by a one-character edit.
_NARROW_CHILD_ANCHOR = re.compile(r"Narrow child module", re.IGNORECASE)

#: ``for [the] <head word>`` immediately after the anchor.  No ``\A``: the
#: pattern is applied with a ``pos`` argument, which ``\A`` ignores (it means
#: "start of string", not "start of the search"), and getting that wrong silently
#: turns every head quantity into an unresolved token.
_HEAD_QUANTITY = re.compile(r"\s*for\s+(?:the\s+)?(\S+)")


def _extract_narrow_child(flat: str, match: re.Match[str]) -> tuple[str, bool, str]:
    """Extract the head quantity of ``Narrow child module for [the] N ...``.

    The quantity is taken from the head position only.  A later numeral in the
    same sentence usually belongs to a section number (``§18.3-§18.4``) or to a
    cited identifier, so reaching for it would buy recall with false charges;
    the parenthetical and predicate classes below pick up the counts that are
    stated elsewhere in the sentence.
    """
    head = _HEAD_QUANTITY.match(flat, match.end())
    if head is None:
        return "-", True, "no `for` clause after the anchor"
    token, is_quantity = resolve_quantity(head.group(1))
    if is_quantity:
        return token, True, ""
    return "-", False, f"no quantity (head word {token!r})"


_PAREN_ANCHOR = re.compile(rf"\(\s*({QUANTITY})\s+({INVENTORY_NOUN})\s*\)", re.IGNORECASE)


def _extract_paren(flat: str, match: re.Match[str]) -> tuple[str, bool, str]:
    """Extract ``(13 theorems)`` -- a count of a subset of this module."""
    token, is_quantity = resolve_quantity(match.group(1))
    noun = match.group(2).lower()
    if not is_quantity:
        return f"?:{noun}", True, f"unresolved quantity {match.group(1)!r}"
    return f"{token}:{noun}", True, ""


_POSSESSIVE_ANCHOR = re.compile(
    rf"\bits\s+({QUANTITY})\s+{_WINDOW}({INVENTORY_NOUN})\b", re.IGNORECASE
)


def _extract_possessive(flat: str, match: re.Match[str]) -> tuple[str, bool, str]:
    """Extract ``its 4 properties`` -- a count of a subset of this module."""
    token, is_quantity = resolve_quantity(match.group(1))
    noun = match.group(2).lower()
    if not is_quantity:
        return f"?:{noun}", True, f"unresolved quantity {match.group(1)!r}"
    return f"{token}:{noun}", True, ""


_PREDICATE_ANCHOR = re.compile(
    rf"\b(?:cover(?:s|ing)?|contains?|holds?|collects?|groups?|bundles?|comprises?)"
    rf"\s+(?:the\s+)?({QUANTITY})\s+{_WINDOW}({INVENTORY_NOUN})\b",
    re.IGNORECASE,
)


def _extract_predicate(flat: str, match: re.Match[str]) -> tuple[str, bool, str]:
    """Extract ``covers three of the four declarations`` -- a count of this module."""
    token, is_quantity = resolve_quantity(match.group(1))
    noun = match.group(2).lower()
    if not is_quantity:
        return f"?:{noun}", True, f"unresolved quantity {match.group(1)!r}"
    return f"{token}:{noun}", True, ""


#: ``now live[s|d] in``.  ``re.IGNORECASE`` for the same reason as
#: :data:`_NARROW_CHILD_ANCHOR`: a sentence-initial ``Now live in `X` `` is the
#: identical claim, and the subject patterns this anchor is paired with
#: (:data:`_SUBJECT_HEAD`, :data:`_SUBJECT_TAIL`) already ignore case, so a
#: case-sensitive anchor was the one asymmetric link in the chain.
_RELOCATION_ANCHOR = re.compile(r"now\s+live(?:s|d)?\s+in", re.IGNORECASE)

#: The destination as written just after ``now live in``: a backticked module or
#: file name, or a ``\texttt{...}`` one in the TeX guide.  No ``\A`` -- see
#: :data:`_HEAD_QUANTITY` for why that would silently erase every destination.
_DESTINATION = re.compile(r"[\s(]*(?:`([^`]+)`|\\texttt\{([^}]*)\})")

#: The *subject* of a relocation claim: ``the|these|its|all`` + a quantity + an
#: inventory noun, optionally followed by a connective clause, running right up
#: to ``now live in``.
#:
#: Every part of that shape is load-bearing, and each was added to kill a
#: measured false positive rather than on suspicion.  A free backwards search for
#: "some quantity earlier in the paragraph" charged 468 of this tree's 767
#: relocation sentences, mostly by borrowing a number from an adjacent bullet of
#: the same ``## Moved:`` block.  Requiring the inventory noun removes
#: ``(under `0 ≤ β`, `0 ≤ J`) now live in``.  Requiring the determiner removes
#: ``Step 241 interior `ContinuousAt` wrappers) now live in`` and the ``PR
#: #1861`` / ``Issue #4501`` references, without an ever-growing list of number
#: prefixes to exclude.  The connective tail is what keeps the archetype
#: ``the three ... wrappers were split out again in PR #2354 and now live in X``
#: (docs/index.md:1393, the F4 site) inside the population.
#:
#: Split into head and tail so the *nearest* subject wins: ``re.search`` is
#: leftmost-first, which would bind ``now live in`` to the first determiner in
#: the window rather than to the noun phrase actually in front of it.
_SUBJECT_HEAD = re.compile(
    rf"(?:^|(?<=[^\w`]))(?:the|these|its|all)\s+({QUANTITY})\b", re.IGNORECASE
)
_SUBJECT_TAIL = re.compile(
    rf"\s*{_WINDOW}{INVENTORY_NOUN}\b(?:(?!\.\s|;|\||-/|/-)[^{MASK}\n]){{0,80}}?\Z",
    re.IGNORECASE,
)


def relocation_subject(window: str) -> re.Match[str] | None:
    """Return the nearest quantified subject ending at ``window``'s end."""
    nearest: re.Match[str] | None = None
    for head in _SUBJECT_HEAD.finditer(window):
        if _SUBJECT_TAIL.match(window, head.end()) is not None:
            nearest = head
    return nearest


def _extract_relocation(flat: str, match: re.Match[str]) -> tuple[str, bool, str]:
    """Extract ``The 13 ... wrappers now live in `X` `` -- a count of *another* module.

    Only the quantified form is charged.  The unquantified
    ``... wrappers now live in `X` `` is an ownership claim that the convention
    also bans, but it states no inventory size, so charging it would drag ~740
    compatibility-umbrella sentences into a population this tool is not the
    right instrument for.  They are accounted, reported as out-of-charge-scope,
    and explicitly *not* exonerated.
    """
    destination = "?"
    tail = _DESTINATION.match(flat, match.end())
    if tail is not None:
        destination = (tail.group(1) or tail.group(2) or "?").strip()
    subject = relocation_subject(flat[max(0, match.start() - 200):match.start()])
    if subject is None:
        return "-", False, f"no quantified subject (-> {destination})"
    token, is_quantity = resolve_quantity(subject.group(1))
    if not is_quantity:
        return f"?->{destination}", True, "unresolved quantity"
    return f"{token}->{destination}", True, ""


CLAIM_CLASSES: tuple[ClaimClass, ...] = (
    ClaimClass(
        name="NARROW_CHILD",
        referent=THIS_MODULE,
        anchor=_NARROW_CHILD_ANCHOR,
        extract=_extract_narrow_child,
        summary="`Narrow child module for [the] N ...` -- the size of this module",
    ),
    ClaimClass(
        name="PAREN_COUNT",
        referent=THIS_MODULE_SUBSET,
        anchor=_PAREN_ANCHOR,
        extract=_extract_paren,
        summary="`(N theorems)` -- the size of a group inside this module",
    ),
    ClaimClass(
        name="POSSESSIVE_COUNT",
        referent=THIS_MODULE_SUBSET,
        anchor=_POSSESSIVE_ANCHOR,
        extract=_extract_possessive,
        summary="`its N properties` -- the size of a group inside this module",
    ),
    ClaimClass(
        name="PREDICATE_COUNT",
        referent=THIS_MODULE,
        anchor=_PREDICATE_ANCHOR,
        extract=_extract_predicate,
        summary="`covers/contains/holds N <artifacts>` -- the size of this module",
    ),
    ClaimClass(
        name="RELOCATION",
        referent=OTHER_MODULE,
        anchor=_RELOCATION_ANCHOR,
        extract=_extract_relocation,
        summary="`The N ... now live in `Mod`` -- the size of a *different* module",
    ),
)

#: The module docstring opener whose absence is charged as :data:`MISSING_DOC`.
_MODULE_DOC = "/-!"


# --------------------------------------------------------------------------
# Scanning one source
# --------------------------------------------------------------------------


class Source(NamedTuple):
    """One scanned input: its ratchet target name, its text and its kind."""

    target: str
    path: str
    text: str
    is_lean: bool


class SourceReport(NamedTuple):
    """The findings and conservation ledger of one source."""

    source: Source
    claims: tuple[Claim, ...]
    conservation: tuple[str, ...]


def scan_source(source: Source) -> SourceReport:
    """Scan one source, returning its claims and its conservation failures.

    Three passes per class, deliberately written as different computations so
    that they can disagree:

    1. ``raw`` -- ``anchor.finditer`` on the flattened *whole* text.
    2. ``prose`` -- ``anchor.finditer`` on the flattened *masked* text.
    3. the record pipeline, which walks the raw matches, decides for each
       whether its span lies inside a single prose region, and calls the class
       extractor.

    ``K1`` requires (3) to produce exactly as many records as (1); ``K2``
    requires (2) to equal the subset of (1) that sits inside prose.
    """
    text = source.text
    decomposition = decompose(text) if source.is_lean else decompose_document(text)
    raw = flatten(text)
    prose = flatten(apply_mask(text, decomposition.regions))
    starts = line_starts(text)
    claims: list[Claim] = []
    failures: list[str] = []

    if not decomposition.terminated:
        claims.append(
            Claim(UNTERMINATED, source.target, "-", 1, True, "comment or string never closed")
        )
    if source.is_lean and _MODULE_DOC not in text:
        claims.append(
            Claim(MISSING_DOC, source.target, "-", 1, True, "no `/-!` module docstring to inspect")
        )

    for claim_class in CLAIM_CLASSES:
        raw_matches = list(claim_class.anchor.finditer(raw.text))
        prose_matches = list(claim_class.anchor.finditer(prose.text))
        before = len(claims)
        inside = 0
        for match in raw_matches:
            begin = raw.origin(match.start())
            finish = raw.origin(max(match.end() - 1, match.start()))
            in_prose = any(start <= begin and finish < end for start, end in decomposition.regions)
            line = line_of(starts, begin)
            if in_prose:
                inside += 1
                token, charged, note = claim_class.extract(raw.text, match)
                claims.append(
                    Claim(claim_class.name, source.target, token, line, charged, note)
                )
            else:
                claims.append(
                    Claim(
                        NON_PROSE,
                        source.target,
                        claim_class.name,
                        line,
                        True,
                        "anchor outside any comment body",
                    )
                )
        # Counted from the records that were actually appended, never from the
        # loop's own bookkeeping: an early `continue` -- the shape a "skip the
        # tokens I cannot resolve" edit takes -- has to be what this number
        # misses, otherwise K1 would only ever confirm its own arithmetic.
        produced = len(claims) - before
        if produced != len(raw_matches):
            failures.append(
                f"K1 {source.target} [{claim_class.name}]: "
                f"{len(raw_matches)} raw anchor(s) produced {produced} record(s)"
            )
        if len(prose_matches) != inside:
            failures.append(
                f"K2 {source.target} [{claim_class.name}]: "
                f"{len(prose_matches)} masked anchor(s) but {inside} raw anchor(s) inside prose"
            )
    return SourceReport(source=source, claims=tuple(claims), conservation=tuple(failures))


# --------------------------------------------------------------------------
# The tracked target set
# --------------------------------------------------------------------------


def tracked_paths(root: Path = REPO_ROOT) -> tuple[str, ...]:
    """Return the repo-relative paths of every target, from ``git ls-files``.

    The VCS index -- not the filesystem -- is the source of truth for which
    files exist: a scanner that walks the tree reads build artefacts, editor
    backups and ignored scratch copies, and this repository has been bitten by
    exactly that.
    """
    result = subprocess.run(
        ["git", "-C", str(root), "ls-files", "-z", "--", LEAN_ROOT, *DOC_TARGETS],
        capture_output=True,
        text=True,
        check=True,
    )
    paths = [entry for entry in result.stdout.split("\0") if entry]
    return tuple(sorted(path for path in paths if path.endswith(".lean") or path in DOC_TARGETS))


def module_name(path: str) -> str:
    """Return the dotted Lean module name of ``path``."""
    return path[: -len(".lean")].replace("/", ".")


def load_sources(root: Path = REPO_ROOT, paths: Iterable[str] | None = None) -> tuple[
    tuple[Source, ...], tuple[str, ...]
]:
    """Read every target, returning ``(sources, K0 failures)``.

    A path that cannot be read is a ``K0`` failure, never a skip.
    """
    wanted = tuple(paths) if paths is not None else tracked_paths(root)
    sources: list[Source] = []
    failures: list[str] = []
    for path in wanted:
        try:
            text = (root / path).read_text(encoding="utf-8")
        except OSError as error:
            failures.append(f"K0 {path}: tracked but unreadable ({error})")
            continue
        is_lean = path.endswith(".lean")
        sources.append(
            Source(
                target=module_name(path) if is_lean else path,
                path=path,
                text=text,
                is_lean=is_lean,
            )
        )
    if len(sources) + len(failures) != len(wanted):
        failures.append(
            f"K0: {len(wanted)} tracked target(s) but {len(sources)} read "
            f"and {len(failures)} failed"
        )
    return tuple(sources), tuple(failures)


# --------------------------------------------------------------------------
# Baseline
# --------------------------------------------------------------------------

BASELINE_HEADER = """\
# Inventory-claim baseline (scripts/header_inventory_claim_ratchet.py, Issue #4980).
#
# A HIGH-WATER MARK, NOT AN ALLOWLIST.  An entry records that the claim existed
# on the commit this file was pinned at; it never says the claim is acceptable.
# There is no exemption channel and no way to mark a finding fine: the only
# legal edit is downward, produced by `--baseline` after real prose was fixed.
#
# One upward correction is on the record, and it is the only kind that can ever
# be legitimate: the pin moved 713 -> 740 when `NARROW_CHILD`'s anchor gained the
# `re.IGNORECASE` flag every other anchor already carried.  No prose changed and
# no repair had been made; 27 lowercase occurrences that had always been there
# simply became visible to a detector that had been blind to them.  A repair
# campaign must never raise this file, and any future increase needs a public
# reason of exactly this shape.
#
# Multiset keyed (class, target, token): a key that is absent here, or present
# with a smaller count than the tree now holds, fails the gate.  One fix
# therefore cannot pay for one regression -- there is no scalar to offset.
#
# Pinned deliberately BEFORE any repair, so every later repair PR is measured
# against a commitment that already exists on main rather than against a number
# it computed for itself.
#
# columns: class<TAB>target<TAB>token<TAB>count
"""


def format_baseline(counts: Counter[tuple[str, str, str]]) -> str:
    """Render a charged-claim multiset in baseline-file format."""
    lines = [BASELINE_HEADER]
    for (kind, target, token), count in sorted(counts.items()):
        lines.append(f"{kind}\t{target}\t{token}\t{count}")
    if not counts:
        lines.append("# (empty: no recognized inventory claim on the current tree)")
    return "\n".join(lines) + "\n"


def parse_baseline(text: str) -> tuple[Counter[tuple[str, str, str]], list[str]]:
    """Parse baseline text into ``(multiset, errors)``.

    A malformed line is an error rather than a silently dropped entry: a
    baseline that quietly loses rows would ratchet the population *up*.
    """
    counts: Counter[tuple[str, str, str]] = Counter()
    errors: list[str] = []
    for lineno, raw in enumerate(text.splitlines(), start=1):
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        fields = raw.split("\t")
        if len(fields) != 4:
            errors.append(f"line {lineno}: expected 4 tab-separated fields, got {len(fields)}")
            continue
        kind, target, token, count = fields
        if not count.strip().isdigit() or int(count) <= 0:
            errors.append(f"line {lineno}: count {count!r} is not a positive integer")
            continue
        key = (kind, target, token)
        if key in counts:
            errors.append(f"line {lineno}: duplicate baseline key {key}")
        counts[key] += int(count)
    return counts, errors


def read_baseline(path: Path = BASELINE_FILE) -> tuple[Counter[tuple[str, str, str]], list[str]]:
    """Read and parse the baseline file (an absent file means an empty one)."""
    if not path.exists():
        return Counter(), []
    return parse_baseline(path.read_text(encoding="utf-8"))


# --------------------------------------------------------------------------
# The run
# --------------------------------------------------------------------------


class Report(NamedTuple):
    """The verdict of one ratchet run."""

    sources: tuple[Source, ...]
    claims: tuple[Claim, ...]
    conservation: tuple[str, ...]

    @property
    def charged(self) -> Counter[tuple[str, str, str]]:
        """The charged-claim multiset, i.e. the ratchet population."""
        return Counter(claim.key for claim in self.claims if claim.charged)

    @property
    def accounted(self) -> tuple[Claim, ...]:
        """Anchor sites that were classified but state no inventory size."""
        return tuple(claim for claim in self.claims if not claim.charged)

    @property
    def sound(self) -> bool:
        """Whether ``K0``/``K1``/``K2`` all held on this run."""
        return not self.conservation


def build_report(root: Path = REPO_ROOT, paths: Iterable[str] | None = None) -> Report:
    """Scan every tracked target and return the run's verdict."""
    sources, failures = load_sources(root, paths)
    claims: list[Claim] = []
    conservation = list(failures)
    for source in sources:
        scanned = scan_source(source)
        claims.extend(scanned.claims)
        conservation.extend(scanned.conservation)
    return Report(sources=sources, claims=tuple(claims), conservation=tuple(conservation))


class Comparison(NamedTuple):
    """The ratchet comparison of a live population against the baseline."""

    new: tuple[tuple[tuple[str, str, str], int], ...]
    grown: tuple[tuple[tuple[str, str, str], int, int], ...]
    slack: tuple[tuple[tuple[str, str, str], int, int], ...]

    @property
    def regressed(self) -> bool:
        """Whether the population grew (the only failing direction)."""
        return bool(self.new or self.grown)


def compare(
    live: Counter[tuple[str, str, str]], baseline: Counter[tuple[str, str, str]]
) -> Comparison:
    """Compare a live population against the baseline, per key.

    Per key, never in aggregate: a scalar comparison would let one repaired
    header pay for one newly written claim, which is precisely the accounting
    the multiset key exists to forbid.
    """
    new = tuple(sorted((key, count) for key, count in live.items() if key not in baseline))
    grown = tuple(
        sorted(
            (key, count, baseline[key])
            for key, count in live.items()
            if key in baseline and count > baseline[key]
        )
    )
    slack = tuple(
        sorted(
            (key, live.get(key, 0), count)
            for key, count in baseline.items()
            if live.get(key, 0) < count
        )
    )
    return Comparison(new=new, grown=grown, slack=slack)


CONTRACT_LINES = (
    "Contract: this ratchet detects RECOGNIZED legacy inventory syntax and holds its",
    "population non-increasing.  It does NOT recompute any count, does NOT determine",
    "whether a header is semantically current, and asserts NOTHING about prose it does",
    "not recognize.  A pass never means the headers are clean.",
)


def print_report(report: Report, baseline: Counter[tuple[str, str, str]],
                 baseline_errors: Iterable[str]) -> bool:
    """Print the human-readable verdict; return whether the ratchet passes."""
    for line in CONTRACT_LINES:
        print(line)
    print("== Inputs ==")
    lean = sum(1 for source in report.sources if source.is_lean)
    print(f"  {len(report.sources)} tracked target(s): {lean} Lean module(s) + "
          f"{len(report.sources) - lean} document(s)")

    print("== Conservation (K0 inputs / K1 records / K2 mask) ==")
    if report.sound:
        print("  PASS: every tracked target accounted for; "
              "raw anchors == records == masked anchors")
    else:
        print(f"  FAIL: {len(report.conservation)} conservation failure(s); "
              "the findings report is suppressed for this run")
        for failure in report.conservation:
            print(f"      {failure}")
        print("FAIL: conservation broken -- no claim verdict is reported")
        return False

    live = report.charged
    comparison = compare(live, baseline)
    print("== Recognized claim classes ==")
    for claim_class in CLAIM_CLASSES:
        charged = sum(count for (kind, _t, _k), count in live.items() if kind == claim_class.name)
        accounted = sum(1 for claim in report.accounted if claim.kind == claim_class.name)
        print(f"  {claim_class.name} [{claim_class.referent}]: {charged} charged, "
              f"{accounted} accounted-but-unquantified -- {claim_class.summary}")
    for kind in (NON_PROSE, MISSING_DOC, UNTERMINATED):
        charged = sum(count for (name, _t, _k), count in live.items() if name == kind)
        print(f"  {kind}: {charged} charged (unparseable/uninspectable input, charged not skipped)")

    print("== Ratchet ==")
    print(f"  baseline {sum(baseline.values())} charge(s) over {len(baseline)} key(s) "
          f"in {BASELINE_FILE.name}")
    print(f"  live     {sum(live.values())} charge(s) over {len(live)} key(s)")
    ok = True
    for message in baseline_errors:
        print(f"  FAIL: malformed baseline: {message}")
        ok = False
    for key, count in comparison.new:
        print(f"  FAIL: new claim (absent from the baseline) x{count}: {key[0]} {key[1]} {key[2]}")
        ok = False
    for key, count, was in comparison.grown:
        print(f"  FAIL: claim count grew {was} -> {count}: {key[0]} {key[1]} {key[2]}")
        ok = False
    if comparison.slack:
        print(f"  INFO: {len(comparison.slack)} baseline key(s) now below their pin; "
              "re-pin with --baseline (never a failure)")

    print(
        "PASS: no recognized inventory claim was added (this says nothing about "
        "unrecognized prose, nor about whether any surviving claim is true)"
        if ok
        else "FAIL: the recognized inventory-claim population grew"
    )
    return ok


def format_findings(report: Report) -> str:
    """Render every finding as TSV (suppressed unless the run is sound)."""
    lines = ["# " + line for line in CONTRACT_LINES]
    lines.append("class\ttarget\ttoken\tline\tcharged\tnote")
    for claim in sorted(report.claims, key=lambda c: (c.target, c.line, c.kind, c.token)):
        lines.append(
            f"{claim.kind}\t{claim.target}\t{claim.token}\t{claim.line}\t"
            f"{'charged' if claim.charged else 'accounted'}\t{claim.note}"
        )
    return "\n".join(lines) + "\n"


SUPPRESSED = (
    "# SUPPRESSED: the run's conservation laws failed, so no finding is reported.\n"
)


def main(argv: list[str] | None = None) -> int:
    """CLI entry point.  Return 0 on success, 1 on failure."""
    parser = argparse.ArgumentParser(
        description="Ratchet on recognized inventory-claim syntax in canonical prose."
    )
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--check", action="store_true",
                       help="Check the live population against the baseline (default).")
    group.add_argument("--baseline", action="store_true",
                       help="Print the live charged population in baseline-file format.")
    group.add_argument("--findings", action="store_true",
                       help="Print every finding, charged and accounted, as TSV.")
    group.add_argument("--self-test", action="store_true",
                       help="Run the ratchet's own test suite.")
    args = parser.parse_args(argv)

    if args.self_test:
        from test_header_inventory_claim_ratchet import run_suite  # noqa: PLC0415

        return run_suite()

    report = build_report()
    if args.baseline or args.findings:
        if not report.sound:
            sys.stdout.write(SUPPRESSED)
            for failure in report.conservation:
                sys.stdout.write(f"# {failure}\n")
            return 1
        sys.stdout.write(format_baseline(report.charged) if args.baseline
                         else format_findings(report))
        return 0

    baseline, errors = read_baseline()
    return 0 if print_report(report, baseline, errors) else 1


if __name__ == "__main__":
    sys.path.insert(0, str(SCRIPT_DIR))
    sys.exit(main())
