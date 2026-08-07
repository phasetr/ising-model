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

That comparison is against the baseline **in the same checkout**, which is
exactly as strong as the baseline file is honest -- regenerating the pin makes
the tree agree with itself by construction.  ``--check-baseline-drift`` is the
other half: it compares this checkout's pin against the one on the base branch
and requires every movement to be explained by the diff (:func:`check_drift`,
rules ``B1``/``B2``/``B3``).  Without it, "repair one claim, write another,
re-pin" is a clean pass.

At baseline zero the rule becomes an absolute lexical ban on the recognized
shapes and the checker stays wired in permanently.  Baseline *maintenance* ends
there; the defect does not become impossible, so the checker is frozen, not
retired.  Nothing here asserts that the live population is non-zero: the tests
prove the detector still works on fixtures, so the suite does not turn red as
the campaign succeeds.

Reading the number (the caveat that outranks the number)
--------------------------------------------------------
**A fall in the charge count is not evidence that prose was repaired.**  The
grammar is finite by design, so a claim reworded into a shape it does not
recognize leaves the tree exactly as stale and the count exactly as much lower.
The count moving down is a prompt to read the ``--findings`` diff, never a
substitute for reading it, and no repair PR may be reviewed on its totals.  The
vocabulary has already been the bypass once: the cardinal list stopped at
``fifty``, so ``for sixty foo wrappers`` was *accounted* -- silently free --
while ``for twelve foo wrappers`` was charged.  What closed that hole was
extending a closed class (English cardinals, the ``~N``/``about N``/``N,NNN``/
``N+`` idioms) and, behind it, the fail-closed rule in
:func:`resolve_quantity`: a quantity fragment that starts with a digit or with a
hedge is charged even when the normalizer cannot resolve it.

Conservation (the reason a silent skip cannot hide here)
--------------------------------------------------------
Every run asserts four identities, and a failure of any of them **suppresses
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
    matches whose span maps back inside a single prose region.  This checks the
    mask/flatten/offset arithmetic -- that a match found on the masked text and
    a match projected through the offset map land in the same place -- and
    **nothing more**.  In particular it does *not* detect a decomposition or
    nesting bug: both of its sides are computed from the same
    ``decomposition.regions``, so a wrong region set moves them together and
    ``K2`` stays green.  That is what ``K3`` is for.

``K3``
    the comment decomposition agrees, region for region, with
    :func:`reference_regions` -- a second decomposition written as a plain
    character-by-character state machine.  This is the check that can actually
    contradict a nesting bug, because it shares no code with the scanner it
    audits.  Lean sources only; a document has no comment structure to get
    wrong.

Unparseable and missing inputs are **charged**, not skipped: a module with no
``/-!`` block in syntax position (:data:`MISSING_DOC`), a file whose comment
structure or string literal does not terminate (:data:`UNTERMINATED`), and an
anchor that does not sit inside prose (:data:`NON_PROSE`) are all findings.
Global totals are deliberately *not* pinned -- they move legitimately as modules
are added -- so the conservation laws are per-run, not frozen scalars.

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
    python3 scripts/header_inventory_claim_ratchet.py --check-baseline-drift
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

#: Repo-relative paths, because the drift check reads both of them out of a
#: *commit* (``git show <ref>:<path>``) as well as out of the working tree.
BASELINE_REPO_PATH = "scripts/audit/header_claim_baseline.tsv"
DETECTOR_REPO_PATH = "scripts/header_inventory_claim_ratchet.py"

BASELINE_FILE = REPO_ROOT / BASELINE_REPO_PATH

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
    ``terminated`` is ``False`` when the scan ended inside a block comment or
    inside a string literal, either of which is charged rather than ignored.
    ``module_doc`` records whether a ``/-!`` block was opened in *syntax
    position* -- at comment depth zero, as a real comment opener -- which is
    what :data:`MISSING_DOC` is charged from.
    """

    regions: tuple[tuple[int, int], ...]
    terminated: bool
    module_doc: bool


#: The only three-character sequences that can change the scanner's state, plus
#: the string delimiter.  Driving the scan off ``re.search`` rather than a
#: per-character loop keeps a 1900-file pass well under a second.
_SCAN_TOKEN = re.compile(r"--|/-|-/|\"")

#: A string literal body after the opening quote, honouring backslash escapes.
_STRING_BODY = re.compile(r'(?:[^"\\]|\\.)*"')

#: The module docstring opener whose absence is charged as :data:`MISSING_DOC`.
#: It counts only where :func:`decompose` finds it in syntax position: a plain
#: substring search -- which is what this started as -- is satisfied by
#: ``def marker : String := "/-!"`` or by ``-- /-!``, so writing the three
#: characters anywhere in the file exonerated the module.
_MODULE_DOC = "/-!"


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
    module_doc = False
    lexical_error = False
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
            # Only an opener at depth 0 can be *the* module docstring; a `/-!`
            # inside a string literal, a line comment or an enclosing block
            # comment never reaches this branch, which is the whole point.
            module_doc = module_doc or text.startswith(_MODULE_DOC, match.start())
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
            if body is None:
                # The quote never closes.  Everything after it was scanned as if
                # it were code, so the file's structure is not known: record the
                # lexical error instead of reporting a clean parse.
                lexical_error = True
                index = length
                continue
            index = body.end()
            continue
        # A stray ``-/`` at depth 0 is not a comment boundary; step past it.
        index = match.end()
    return Decomposition(
        regions=tuple(regions),
        terminated=depth == 0 and not lexical_error,
        module_doc=module_doc,
    )


def reference_regions(text: str) -> tuple[tuple[int, int], ...]:
    """Return the comment-body regions of ``text`` by an independent algorithm.

    ``K3``'s oracle, and the reason it exists: ``K2`` compares two views that are
    both derived from :func:`decompose`'s output, so a nesting bug moves both of
    them together and ``K2`` stays green.  Only a second, structurally different
    decomposition can contradict the first.  This one is a plain
    character-by-character state machine -- slower and duller than the
    ``re.search``-driven scan, and deliberately so, because a shared idea is a
    shared blind spot.  It costs about two seconds over the whole tracked tree.
    """
    regions: list[tuple[int, int]] = []
    index = 0
    depth = 0
    start = 0
    length = len(text)
    while index < length:
        if depth > 0:
            if text.startswith("/-", index):
                depth += 1
                index += 2
            elif text.startswith("-/", index):
                depth -= 1
                if depth == 0:
                    regions.append((start, index))
                index += 2
            else:
                index += 1
            continue
        if text.startswith("--", index):
            end = text.find("\n", index + 2)
            end = length if end < 0 else end
            regions.append((index + 2, end))
            index = end
            continue
        if text.startswith("/-", index):
            depth = 1
            index += 2
            start = index
            continue
        if text[index] == '"':
            index += 1
            while index < length:
                if text[index] == "\\":
                    index += 2
                    continue
                if text[index] == '"':
                    index += 1
                    break
                index += 1
            continue
        index += 1
    return tuple(regions)


def decompose_document(text: str) -> Decomposition:
    """Return the whole of ``text`` as one prose region.

    ``docs/index.md`` and ``tex/proof-guide.tex`` are prose end to end; there is
    no code/comment distinction to get wrong, so the decomposition is total and
    ``K2`` degenerates to "every anchor is in prose" for them -- which is the
    honest statement, not a weakening.  ``module_doc`` is irrelevant for them:
    :data:`MISSING_DOC` is charged for Lean modules only.
    """
    return Decomposition(regions=((0, len(text)),), terminated=True, module_doc=True)


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

#: The English cardinals below one hundred, as single words.  The word forms
#: outnumber the numerals in this corpus almost three to one, so both spellings
#: are first-class.
_UNIT_WORDS: dict[str, int] = {
    "one": 1, "two": 2, "three": 3, "four": 4, "five": 5, "six": 6, "seven": 7,
    "eight": 8, "nine": 9, "ten": 10, "eleven": 11, "twelve": 12, "thirteen": 13,
    "fourteen": 14, "fifteen": 15, "sixteen": 16, "seventeen": 17, "eighteen": 18,
    "nineteen": 19,
}

#: The tens.  The list stopped at ``fifty`` when this checker was introduced,
#: which made every count from sixty upwards silently *accounted* instead of
#: charged -- an unadvertised bypass in the largest claim class, not a recall
#: nicety.  English cardinals are a closed class, so the vocabulary is now
#: complete rather than "as far as the corpus happened to reach".
_TEN_WORDS: dict[str, int] = {
    "twenty": 20, "thirty": 30, "forty": 40, "fifty": 50, "sixty": 60,
    "seventy": 70, "eighty": 80, "ninety": 90,
}

#: The multiplicative scales.  They compose (``two hundred``) rather than add,
#: which is why the compound resolver below is a small parser and not a sum.
_SCALE_WORDS: dict[str, int] = {"hundred": 100, "thousand": 1000}

#: Every recognized cardinal word.
WORD_NUMBERS: dict[str, int] = {**_UNIT_WORDS, **_TEN_WORDS, **_SCALE_WORDS}

#: Quantifiers that assert a population without naming its size.  They fail the
#: split-stability test exactly as a numeral does ("the remaining wrappers"
#: changes meaning the moment a sibling module is carved out), so they are
#: charged, with the word itself as the token.
VAGUE_QUANTIFIERS = frozenset(
    {"several", "many", "various", "numerous", "multiple", "both", "remaining", "few"}
)


def _alternation(words: Iterable[str]) -> str:
    """Return a regex alternation of ``words``, longest first.

    Longest-first matters: Python alternation is leftmost-*first*, so ``six``
    listed before ``sixteen`` would match the prefix of ``sixteen`` and leave a
    stray ``teen`` behind.
    """
    return "|".join(sorted(words, key=len, reverse=True))


_UNITS_ALT = _alternation(_UNIT_WORDS)
_TENS_ALT = _alternation(_TEN_WORDS)
_SCALES_ALT = _alternation(_SCALE_WORDS)

#: A cardinal below one hundred: a ten, optionally hyphenated with a unit, or a
#: bare unit.
_SMALL_CARDINAL = rf"(?:(?:{_TENS_ALT})(?:-(?:{_UNITS_ALT}))?|(?:{_UNITS_ALT}))"

#: A cardinal phrase.  A grammar rather than a free repetition of cardinal
#: words: ``three four`` is not a number and must not be read as seven.
_CARDINAL = (
    rf"(?:(?:{_SMALL_CARDINAL}\s+)?(?:{_SCALES_ALT})(?:\s+(?:and\s+)?{_SMALL_CARDINAL})?"
    rf"|{_SMALL_CARDINAL})"
)

#: A numeral, with or without thousands separators.  ``1,024`` is a count; a
#: grammar that only knew ``\d+`` read it as ``1`` at best and matched nothing
#: at worst, so the comma-grouped form is recognized explicitly.
_NUMERAL = r"(?:\d{1,3}(?:,\d{3})+|\d+)"

#: Hedges that make a count approximate without making it any less of a claim
#: about module extension.  ``about twelve wrappers`` goes stale on exactly the
#: same split that ``twelve wrappers`` does, so a hedge must never buy silence.
_HEDGE = (
    r"(?:[~≈]\s*|(?:about|approximately|roughly|around|nearly|at\s+least|at\s+most"
    r"|more\s+than|fewer\s+than|up\s+to)\s+)"
)

#: The number itself, hedges and suffixes excluded.
_QUANTITY_CORE = rf"(?:{_NUMERAL}|{_CARDINAL})"

#: A quantity as it appears in prose: an optional hedge, a numeral or cardinal
#: phrase, and an optional ``+`` ("12+ wrappers").
QUANTITY = rf"(?:{_HEDGE})?{_QUANTITY_CORE}\+?"

#: The same shape, anchored, with the parts kept apart so a token can record
#: *how* the count was hedged.
_QUANTITY_PARTS = re.compile(
    rf"\A(?P<hedge>{_HEDGE})?(?P<core>{_QUANTITY_CORE})(?P<more>\+)?\Z", re.IGNORECASE
)

#: What makes a head word unmistakably a quantity even when it cannot be
#: normalized: it starts with a digit or with a hedge.  This is the fail-closed
#: half of :func:`resolve_quantity` -- ``12-ish`` and ``about 12ish`` are claims
#: whatever the grammar makes of them.  It deliberately does *not* fire on a
#: digit appearing later in the word, because the corpus's non-claim head words
#: are section references (``§18.3-§18.4``, 52 sites) and charging those would
#: be a pure false positive.
_NUMERIC_IDIOM = re.compile(rf"\A(?:{_HEDGE}|\d)", re.IGNORECASE)

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


def cardinal_value(phrase: str) -> int | None:
    """Return the value of a cardinal ``phrase``, or ``None`` if it is not one.

    Scales multiply and everything else adds, so ``two hundred`` is 200 while
    ``twenty-four`` is 24.  A plain sum over the words -- the shape this started
    as -- reads ``two hundred`` as 102.
    """
    total = 0
    current = 0
    seen = False
    for word in re.split(r"[-\s]+", phrase.strip().lower()):
        if not word or word == "and":
            continue
        if word in _SCALE_WORDS:
            scale = _SCALE_WORDS[word]
            current = (current or 1) * scale
            if scale >= _SCALE_WORDS["thousand"]:
                total += current
                current = 0
        elif word in WORD_NUMBERS:
            current += WORD_NUMBERS[word]
        else:
            return None
        seen = True
    return total + current if seen else None


def resolve_quantity(raw: str) -> tuple[str, bool]:
    """Return ``(token, is_quantity)`` for the quantity fragment ``raw``.

    ``token`` is the normalized claim token: a decimal string for a numeral or
    cardinal phrase, ``~N``/``N+`` for a hedged or open-ended one, the
    lower-cased word for a vague quantifier, and ``?<raw>`` for a fragment that
    is unmistakably numeric but that the grammar cannot normalize.

    ``is_quantity`` is ``False`` only for a fragment with no numeric content at
    all, which is *accounted but not charged* -- a header reading ``Narrow child
    module for concrete latticeGraph specializations`` states no count, and
    inventing a charge for it would make the tool's population meaningless.
    Everything that does carry numeric content is charged, including forms the
    normalizer does not understand: an unresolvable count is a claim, and this
    is the one place where the "unparseable is charged, never skipped" rule has
    to hold for a *quantity* rather than for a file.
    """
    word = raw.strip().strip(",.;:!?)(`*").lower()
    if word in VAGUE_QUANTIFIERS:
        return word, True
    parts = _QUANTITY_PARTS.match(word)
    if parts is not None:
        core = parts.group("core")
        value = core.replace(",", "") if core[0].isdigit() else _cardinal_token(core)
        if value is not None:
            if parts.group("hedge"):
                value = f"~{value}"
            if parts.group("more"):
                value = f"{value}+"
            return value, True
    if _NUMERIC_IDIOM.match(word):
        return f"?{word}", True
    return word, False


def _cardinal_token(core: str) -> str | None:
    """Return the decimal spelling of cardinal phrase ``core``, or ``None``."""
    value = cardinal_value(core)
    return None if value is None else str(value)


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

#: ``for [the] <head quantity>`` immediately after the anchor.  The quantity
#: alternative comes first so that a multi-word count (``about 12``, ``two
#: hundred``) is captured whole; ``\S+`` is the fallback that keeps the
#: extractor total, so a non-quantity head word still produces a record.
#:
#: No ``\A``: the pattern is applied with a ``pos`` argument, which ``\A``
#: ignores (it means "start of string", not "start of the search"), and getting
#: that wrong silently turns every head quantity into an unresolved token.
#: ``re.IGNORECASE`` for the same reason the anchors carry it -- ``For The 12``
#: is the same claim, and this was the last case-sensitive link in the chain.
_HEAD_QUANTITY = re.compile(rf"\s*for\s+(?:the\s+)?({QUANTITY}(?![\w-])|\S+)", re.IGNORECASE)


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
    requires (2) to equal the subset of (1) that sits inside prose; ``K3``
    requires the decomposition itself to agree with an independent oracle.
    """
    text = source.text
    decomposition = decompose(text) if source.is_lean else decompose_document(text)
    raw = flatten(text)
    prose = flatten(apply_mask(text, decomposition.regions))
    starts = line_starts(text)
    claims: list[Claim] = []
    failures: list[str] = []

    if source.is_lean and decomposition.regions != reference_regions(text):
        failures.append(
            f"K3 {source.target}: the comment decomposition disagrees with the "
            "independent oracle"
        )
    if not decomposition.terminated:
        claims.append(
            Claim(UNTERMINATED, source.target, "-", 1, True, "comment or string never closed")
        )
    if source.is_lean and not decomposition.module_doc:
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
# it computed for itself.  That is enforced, not merely intended:
# `--check-baseline-drift` compares this file against the copy on the base
# branch and requires the diff to explain every movement -- no key may grow (B1),
# a key may only shrink where the diff edits the source it names (B2), and the
# pin must be tight against the tree (B3).  Regenerating this file therefore no
# longer launders a claim: `--check` would pass, the drift check would not.
#
# The single escape hatch is a comment line beginning DETECTOR-MIGRATION:, added
# by the same diff that changes the detector.  It waives B1/B2 for a recount
# under a corrected detector -- the 713 -> 740 shape above -- and nothing else;
# it is not a standing permission, because a line already on the base branch is
# not one the diff adds.
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
# Baseline drift against the base branch
# --------------------------------------------------------------------------

#: The one line that may authorize the pin to move in a direction no prose edit
#: explains.  It has to be *added by the diff under review* -- a marker already
#: present on the base branch is not a waiver -- and it only counts when the
#: detector itself changed in the same diff, because a detector migration that
#: does not touch the detector is not one.
MIGRATION_MARKER = "# DETECTOR-MIGRATION:"


def _git(root: Path, *args: str) -> tuple[int, str]:
    """Run ``git`` in ``root``; return ``(returncode, stdout)``."""
    result = subprocess.run(
        ["git", "-C", str(root), *args], capture_output=True, text=True, check=False
    )
    return result.returncode, result.stdout


def base_commit(root: Path, base_ref: str) -> str | None:
    """Return the merge base of ``base_ref`` and ``HEAD``, or ``None``.

    The merge base rather than the tip: a branch that has not rebased must be
    measured against the commitment that was on the base branch when it forked,
    not against one made after it.  ``None`` means the ref does not resolve at
    all, which is a failure and never a skip -- an unfetched ``origin/main`` is
    exactly how this check would quietly stop running in CI.
    """
    code, out = _git(root, "merge-base", base_ref, "HEAD")
    if code == 0 and out.strip():
        return out.strip()
    code, out = _git(root, "rev-parse", "--verify", f"{base_ref}^{{commit}}")
    return out.strip() if code == 0 and out.strip() else None


def baseline_at(root: Path, commit: str) -> tuple[Counter[tuple[str, str, str]] | None, list[str]]:
    """Return the baseline recorded at ``commit``, or ``None`` if it has none."""
    code, out = _git(root, "show", f"{commit}:{BASELINE_REPO_PATH}")
    if code != 0:
        return None, []
    return parse_baseline(out)


def changed_paths(root: Path, commit: str) -> frozenset[str]:
    """Return the repo-relative paths that differ between ``commit`` and the tree."""
    code, out = _git(root, "diff", "--name-only", commit, "--")
    if code != 0:
        return frozenset()
    return frozenset(line.strip() for line in out.splitlines() if line.strip())


def migration_waiver(root: Path, commit: str) -> tuple[str, ...]:
    """Return the migration reasons this diff adds to the baseline file.

    Empty unless the diff both adds a :data:`MIGRATION_MARKER` line *and*
    changes the detector.  The waiver is therefore never a standing permission:
    it lives in the diff, is one grep away for a reviewer, and expires the
    moment the line stops being new.
    """
    if DETECTOR_REPO_PATH not in changed_paths(root, commit):
        return ()
    code, out = _git(root, "diff", "-U0", commit, "--", BASELINE_REPO_PATH)
    if code != 0:
        return ()
    reasons = [
        line[1:].strip()
        for line in out.splitlines()
        if line.startswith("+") and line[1:].lstrip().startswith(MIGRATION_MARKER)
    ]
    return tuple(reasons)


def target_path(target: str) -> str:
    """Return the repo-relative source path a ratchet target names."""
    return target if target in DOC_TARGETS else target.replace(".", "/") + ".lean"


class Drift(NamedTuple):
    """The verdict of comparing this checkout's pin against the base branch's."""

    base: str
    had_baseline: bool
    added: tuple[tuple[tuple[str, str, str], int, int], ...]
    unexplained: tuple[tuple[tuple[str, str, str], int, int], ...]
    untight: tuple[tuple[str, str, str], ...]
    waiver: tuple[str, ...]

    @property
    def ok(self) -> bool:
        """Whether the pin moved only in ways a real repair explains."""
        if self.untight:
            return False
        return bool(self.waiver) or not (self.added or self.unexplained)


def check_drift(root: Path = REPO_ROOT, base_ref: str = "origin/main") -> Drift | None:
    """Compare this checkout's baseline against the one on ``base_ref``.

    Three rules, and between them they are what makes "the population only ever
    falls, and only by repair" load-bearing rather than aspirational.  The
    live-versus-baseline gate cannot see any of this: regenerating the pin makes
    the tree agree with itself by construction, so a PR that repairs one claim,
    writes another and re-pins passes it cleanly.

    ``B1``
        no key may be new or larger than the base branch's pin.  This is the
        net-zero swap: the repaired key disappears, the written key appears, the
        total is unchanged, and only a comparison against the *other branch's*
        file can tell the difference.

    ``B2``
        a key that shrank or vanished must have a corresponding source edit in
        this diff.  Deleting rows from the pin is otherwise a text edit like any
        other, and this file is the only place the campaign's own progress is
        recorded.

    ``B3``
        the pin must be tight against the live tree.  Slack is capacity: a
        repair left un-pinned leaves room on exactly the repaired key for a new
        claim to be written into later, silently, with no diff to review.

    ``B2`` attributes at file granularity, not at line granularity: it asks
    whether the source the key names appears in the diff, not whether the exact
    line did.  ``B3`` is what makes that enough.  With the pin required to be an
    exact function of the tree, a baseline row cannot be deleted while its claim
    is still written -- the row would be missing and the claim live, which ``B3``
    rejects -- so the only way down is for the prose to have actually gone.  What
    ``B2`` adds on top is that the disappearance has to be visible in the diff of
    the file that owned it.

    Returns ``None`` when ``base_ref`` does not resolve -- fail closed, never a
    silent pass.
    """
    base = base_commit(root, base_ref)
    if base is None:
        return None
    baseline, _errors = baseline_at(root, base)
    head, _head_errors = read_baseline(root / BASELINE_REPO_PATH)
    live = build_report(root).charged
    untight = tuple(sorted(key for key in set(head) | set(live) if head.get(key) != live.get(key)))
    if baseline is None:
        return Drift(base, False, (), (), untight, ())
    edited = changed_paths(root, base)
    added = tuple(
        sorted(
            (key, count, baseline.get(key, 0))
            for key, count in head.items()
            if count > baseline.get(key, 0)
        )
    )
    unexplained = tuple(
        sorted(
            (key, head.get(key, 0), count)
            for key, count in baseline.items()
            if head.get(key, 0) < count and target_path(key[1]) not in edited
        )
    )
    return Drift(base, True, added, unexplained, untight, migration_waiver(root, base))


def print_drift(drift: Drift | None, base_ref: str) -> bool:
    """Print the drift verdict; return whether it passes."""
    print("== Baseline drift (this checkout's pin vs the base branch's) ==")
    if drift is None:
        print(f"  FAIL: base ref {base_ref!r} does not resolve in this checkout")
        print("        (CI needs `fetch-depth: 0`, so that origin/main is present)")
        print("FAIL: the pin could not be compared against the base branch")
        return False
    print(f"  base commit {drift.base[:12]} via {base_ref}")
    ok = True
    for key in drift.untight:
        print(f"  FAIL: B3 pin not tight -- re-pin with --baseline: {key[0]} {key[1]} {key[2]}")
        ok = False
    if not drift.had_baseline:
        print("  INFO: the base commit carries no baseline file; this is its first landing, "
              "so B1/B2 have nothing to compare against")
        print("PASS: baseline drift" if ok else "FAIL: baseline drift")
        return ok
    for key, count, was in drift.added:
        print(f"  FAIL: B1 pin rose {was} -> {count}: {key[0]} {key[1]} {key[2]}")
        ok = False
    for key, count, was in drift.unexplained:
        print(f"  FAIL: B2 pin fell {was} -> {count} with no edit to {target_path(key[1])}: "
              f"{key[0]} {key[1]} {key[2]}")
        ok = False
    if drift.waiver and not ok and not drift.untight:
        print("  WAIVED: B1/B2 by a detector migration declared in this diff:")
        for reason in drift.waiver:
            print(f"      {reason}")
        ok = True
    elif drift.waiver:
        print("  INFO: a detector migration is declared in this diff:")
        for reason in drift.waiver:
            print(f"      {reason}")
    print("PASS: the pin moved only where this diff explains it"
          if ok else "FAIL: the pin moved in a way this diff does not explain")
    return ok


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
        """Whether ``K0``/``K1``/``K2``/``K3`` all held on this run."""
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
    "Caveat on the numbers below: a FALL in them is not by itself evidence that prose",
    "was repaired.  Rewriting a claim into a shape this grammar does not recognize",
    "lowers them just as a real repair does.  Review a repair on the --findings diff,",
    "never on the totals.",
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

    print("== Conservation (K0 inputs / K1 records / K2 mask / K3 decomposition oracle) ==")
    if report.sound:
        print("  PASS: every tracked target accounted for; "
              "raw anchors == records == masked anchors; regions == oracle")
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
    group.add_argument("--check-baseline-drift", action="store_true",
                       help="Compare this checkout's baseline against the base branch's.")
    group.add_argument("--self-test", action="store_true",
                       help="Run the ratchet's own test suite.")
    parser.add_argument("--base-ref", default="origin/main",
                        help="The base branch for --check-baseline-drift (default origin/main).")
    args = parser.parse_args(argv)

    if args.self_test:
        from test_header_inventory_claim_ratchet import run_suite  # noqa: PLC0415

        return run_suite()

    if args.check_baseline_drift:
        for line in CONTRACT_LINES:
            print(line)
        return 0 if print_drift(check_drift(base_ref=args.base_ref), args.base_ref) else 1

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
