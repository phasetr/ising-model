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

There *was* a third bucket, and it was the largest thing in the report: a
recognized anchor whose quantity would not parse was filed as "accounted", which
read as coverage and behaved as an exemption.  647 of the tree's 767
``now live in X`` sentences sat in it, most of them visibly quantified, because
the count was written after a long backticked list of names and the extractor's
window stopped short.  Two rules replace it:

* a **relocation is charged on its anchor alone**.  ``... now live in `X` `` is
  itself the ownership claim this tool ratchets, so whether an adjacent count
  parses may sharpen the key (``12->X`` rather than ``->X``) but may never
  decide whether there is one.
* a **quantity that fails to parse is charged**, as ``?<fragment>``, in every
  class.  The extractor's success is never a fact about the prose.

What remains is :attr:`Report.telemetry`: a recognized anchor that states no size
at all, as in ``Narrow child module for concrete latticeGraph specializations``.
It is reported apart from :attr:`Report.claims`, is never pinned and is never
compared -- a coverage note, structurally incapable of being a silent exemption
because it is not in the ledger.

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
Every run asserts five identities, and a failure of any of them **suppresses
the findings report in every output format** -- ``--check``, ``--baseline``,
``--findings`` and ``--check-baseline-drift`` alike, the last of which used to
print ``PASS`` on a tree whose ``--check`` was failing.  A run that cannot
account for its own inputs reports nothing rather than something reassuring:

``K0``
    every target the tracked-file query returned was opened and accounted for.
    A read error is a failure, never a skip, and so is a file holding one of the
    scanner's own :data:`SENTINELS`.

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
    wrong.  It shares the *lexicon* with the scanner by design -- which Lean
    constructs exist is the specification, not an implementation detail -- so a
    construct missing from both sides is a blind spot ``K3`` cannot see.  That
    happened once: neither side knew guillemet-quoted identifiers, so
    ``def «/-! fake -/» : Nat := 1`` read as a module docstring and bought the
    module an exemption from :data:`MISSING_DOC`.  The lexicon is now stated in
    one place (:data:`_SCAN_TOKEN`) and mutated one side at a time by the tests.

``K4``
    the ledger key identifies exactly one file: it inverts to the path it was
    read from, and no two scanned files share it.  ``K0``-``K3`` prove that a
    *record exists* for every input; none of them proves that its *key is
    unique*, and the difference was a working exploit.  The targets used to be
    dotted module names, and ``A/B.lean`` and ``A.B.lean`` are two tracked files
    with one dotted name: rewording the claim in one while writing the same
    sentence into the other left the pin byte-identical, with every gate green.
    The key is the path now and this law says so out loud.

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

Which tracked files, stated positively and negatively both, because a scan
boundary that is merely implied by a glob is a place claims live untouched:

**in** (:data:`SCAN_ROOTS`, filtered to :data:`SCAN_SUFFIXES`)
    ``IsingModel.lean``, ``IsingModel/**.lean``, ``README.md``, ``docs/**.md``,
    ``tex/**.tex``.

**out** (:data:`EXCLUDED_ROOTS`)
    ``test/`` (Lean fixtures, not canonical prose), ``.github/`` (CI wiring) and
    ``scripts/`` (the checkers, this file's own pin, and the fixture corpora --
    scanning them would let the tool charge its own test data).

The boundary was previously ``IsingModel/`` plus two documents named by hand,
which left the top-level umbrella and four other ``docs/`` pages unscanned; one
of them, ``docs/architecture-import-layers.md``, was already carrying a claim of
a charged class.

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
import ast
import bisect
import contextlib
import re
import shutil
import subprocess
import sys
import tempfile
import types
from collections import Counter
from collections.abc import Iterator
from pathlib import Path
from typing import Callable, Iterable, NamedTuple

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent

#: Repo-relative paths, because the drift check reads both of them out of a
#: *commit* (``git show <ref>:<path>``) as well as out of the working tree.
BASELINE_REPO_PATH = "scripts/audit/header_claim_baseline.tsv"
DETECTOR_REPO_PATH = "scripts/header_inventory_claim_ratchet.py"

BASELINE_FILE = REPO_ROOT / BASELINE_REPO_PATH

#: Where canonical prose lives, as ``git ls-files`` pathspecs.  Stated
#: positively and exhaustively, because the boundary of a scan is a decision and
#: not a side effect of whichever glob somebody first wrote: the previous list
#: named two documents by hand and silently left ``IsingModel.lean`` (the
#: top-level umbrella) and every other ``docs/`` page outside the scan, one of
#: which -- ``docs/architecture-import-layers.md`` -- was already carrying a
#: charged claim nothing measured.
SCAN_ROOTS: tuple[str, ...] = ("IsingModel.lean", "IsingModel", "README.md", "docs", "tex")

#: The suffixes scanned under :data:`SCAN_ROOTS`.  ``docs/`` also holds
#: ``_config.yml`` and a ``Gemfile``, which are configuration and not prose.
SCAN_SUFFIXES: tuple[str, ...] = (".lean", ".md", ".tex")

#: Deliberately **out** of scope, recorded here rather than left to be inferred
#: from the roots above:
#:
#: ``test/``
#:     Lean test fixtures.  Their headers are not canonical prose and the suite
#:     rewrites them freely.
#: ``.github/``
#:     workflow YAML: no Lean structure, and its prose is CI wiring.
#: ``scripts/``
#:     the checkers themselves, this file's own baseline, and the fixture
#:     corpora.  Scanning them would let the tool charge its own test data --
#:     every fixture string in ``test_header_inventory_claim_ratchet.py`` is a
#:     deliberate claim -- so the pin would grow with each new canary.
EXCLUDED_ROOTS: tuple[str, ...] = ("test/", ".github/", "scripts/")

#: The sentinel a masked-out (non-prose) character becomes.  No anchor contains
#: it, so a regex cannot match across it.
MASK = "\x00"

#: The sentinel a **paragraph break** becomes when whitespace is flattened.
#: :func:`flatten` collapses every whitespace run to one space, so a blank line
#: -- the one boundary this corpus's prose really does respect -- was
#: indistinguishable from a line wrap, and a clause window happily reached out of
#: its own paragraph into the next one to borrow a count (see :data:`_CLAUSE_SPAN`).
#: It is not whitespace, so ``\s`` cannot match it and no anchor spans it either.
PARAGRAPH = "\x01"

#: Every control character the scanner writes into the text it then matches on.
#: That they appear in no tracked file was a docstring for three rounds and is a
#: ``K0`` check now (:func:`load_sources`): a literal ``NUL`` between ``for`` and
#: a count made the count free, which is absurd as an attack and is exactly the
#: "asserted, never checked" shape three of the last six findings had.
SENTINELS: tuple[str, ...] = (MASK, PARAGRAPH)


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


#: The sequences that can change the scanner's state.  Driving the scan off
#: ``re.search`` rather than a per-character loop keeps a 1900-file pass well
#: under a second.
#:
#: ``«`` and the raw-string opener are here because Lean lets both of them carry
#: a *literal* ``/-!`` that is not a comment opener: ``def «/-! fake -/» : Nat``
#: and ``def s := r"/-! fake -/"`` are valid Lean (checked against this repo's
#: pinned toolchain) in which the three characters appear outside any comment.
#: A lexer that does not know these two forms reads them as a module docstring
#: and stops charging :data:`MISSING_DOC` -- the one class whose whole purpose is
#: to stop "delete the header instead of repairing it".
#:
#: The character literal is here for the mirror-image reason, and it fails the
#: other way: ``def c : Char := '"'`` and ``def g : Char := '«'`` are valid Lean
#: whose body is *not* the opener it looks like, so a lexer without them reads
#: the rest of the file as one unterminated string and charges the module
#: :data:`UNTERMINATED` **and** :data:`MISSING_DOC`.  Fail-closed, but a live
#: false-positive landmine: one legitimate ``Char`` literal anywhere under the
#: Lean root would turn the gate red on two keys no pin can hold.
#:
#: The lookbehind is what keeps ``h'`` and ``h''`` out: a prime is an identifier
#: character in Lean, and this corpus is full of them.
_CHAR_LITERAL = r"(?<![\w.'!?])'(?:\\.|[^\\'\n])'"

_SCAN_TOKEN = re.compile(rf"--|/-|-/|{_CHAR_LITERAL}|«|(?<![\w.'!?])r#*\"|\"")

#: A string literal body after the opening quote, honouring backslash escapes.
_STRING_BODY = re.compile(r'(?:[^"\\]|\\.)*"')

#: The closing delimiter of a Lean guillemet-quoted identifier.  Its contents are
#: opaque: Lean accepts every character except ``»`` there, comment delimiters
#: included, so nothing inside may be scanned for structure.
_GUILLEMET_CLOSE = "»"

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

    ``--`` inside a block comment, and ``/-`` inside a line comment, a string
    literal, a raw string, a guillemet-quoted identifier or a character literal,
    are inert.  Markdown and TeX have no such structure, so their whole text is
    one region (see :func:`decompose_document`).
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
        if token.startswith("'"):
            # A character literal is one opaque token, matched whole: its body
            # may be `"` or `«`, neither of which opens anything here.
            index = match.end()
            continue
        if token == "«" or token.endswith('"'):
            end = _opaque_end(text, token, match.end())
            if end is None:
                # The span never closes.  Everything after it was scanned as if
                # it were code, so the file's structure is not known: record the
                # lexical error instead of reporting a clean parse.
                lexical_error = True
                index = length
                continue
            index = end
            continue
        # A stray ``-/`` at depth 0 is not a comment boundary; step past it.
        index = match.end()
    return Decomposition(
        regions=tuple(regions),
        terminated=depth == 0 and not lexical_error,
        module_doc=module_doc,
    )


def _opaque_end(text: str, token: str, position: int) -> int | None:
    """Return the index just past the span ``token`` opened, or ``None`` if it never closes.

    The three spans whose contents are not Lean structure: a string literal
    (escapes honoured), a guillemet-quoted identifier (anything but ``»``) and a
    raw string (anything up to a closing quote carrying the opener's hash count).
    """
    if token == '"':
        body = _STRING_BODY.match(text, position)
        return None if body is None else body.end()
    if token == "«":
        close = text.find(_GUILLEMET_CLOSE, position)
        return None if close < 0 else close + len(_GUILLEMET_CLOSE)
    closer = '"' + "#" * (len(token) - 2)  # ``r"`` / ``r#"`` / ``r##"`` ...
    close = text.find(closer, position)
    return None if close < 0 else close + len(closer)


def reference_regions(text: str) -> tuple[tuple[int, int], ...]:
    """Return the comment-body regions of ``text`` by an independent algorithm.

    ``K3``'s oracle, and the reason it exists: ``K2`` compares two views that are
    both derived from :func:`decompose`'s output, so a nesting bug moves both of
    them together and ``K2`` stays green.  Only a second, structurally different
    decomposition can contradict the first.  This one is a plain
    character-by-character state machine -- slower and duller than the
    ``re.search``-driven scan, and deliberately so, because a shared idea is a
    shared blind spot.  It costs about two seconds over the whole tracked tree.

    Independent in *implementation*, not in *lexicon*: it recognizes the same
    Lean tokens :func:`decompose` does -- comments, string literals, raw strings,
    guillemet-quoted identifiers and character literals -- because agreeing on
    which constructs exist is the specification both sides are held to.  A
    construct missing from both is a blind spot no amount of algorithmic
    independence would catch, which is why the guillemet, raw-string and
    character-literal forms were each added here and there in the same edit, and
    why ``LexiconTest`` mutates one side alone.
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
        skip = _reference_opaque_end(text, index)
        if skip is not None:
            index = skip
            continue
        index += 1
    return tuple(regions)


def _reference_identifier_char(text: str, index: int) -> bool:
    """Whether ``text[index]`` continues a Lean identifier (the oracle's half).

    The character-by-character reading of the lookbehind :data:`_CHAR_LITERAL`
    and :func:`_raw_string_opener` share: a prime or a raw-string ``r`` that
    follows one of these opens nothing, because it is part of the name in front
    of it.  ``index < 0`` means "start of file", where nothing precedes.
    """
    return index >= 0 and (text[index].isalnum() or text[index] in "_.'!?")


def _reference_char_literal_end(text: str, index: int) -> int | None:
    """Return the end of the character literal at ``index``, or ``None``.

    ``'a'``, ``'\\n'``, ``'"'``, ``'«'``: one escaped or one plain character
    between primes.  Walked by hand rather than by :data:`_CHAR_LITERAL`, which
    is the whole point of the oracle.
    """
    if text[index] != "'" or _reference_identifier_char(text, index - 1):
        return None
    body = index + 1
    if body >= len(text) or text[body] == "\n":
        return None
    if text[body] == "\\":
        body += 2
    elif text[body] == "'":
        return None
    else:
        body += 1
    if body < len(text) and text[body] == "'":
        return body + 1
    return None


def _reference_opaque_end(text: str, index: int) -> int | None:
    """Return the end of the opaque span starting at ``index``, or ``None`` if none does.

    The oracle's half of :func:`_opaque_end`, written character by character and
    sharing no code with it.  A span that never closes ends at the end of the
    text; only :func:`decompose` records that as a lexical error, because regions
    are all this function reports.
    """
    length = len(text)
    literal = _reference_char_literal_end(text, index)
    if literal is not None:
        return literal
    if text[index] == "«":
        close = text.find(_GUILLEMET_CLOSE, index + 1)
        return length if close < 0 else close + 1
    raw = _raw_string_opener(text, index)
    if raw is not None:
        close = text.find(raw[1], raw[0])
        return length if close < 0 else close + len(raw[1])
    if text[index] != '"':
        return None
    position = index + 1
    while position < length:
        if text[position] == "\\":
            position += 2
            continue
        if text[position] == '"':
            return position + 1
        position += 1
    return length


def _raw_string_opener(text: str, index: int) -> tuple[int, str] | None:
    """Return ``(body start, closing delimiter)`` if a raw string opens at ``index``.

    ``r"..."``, ``r#"..."#``, ``r##"..."##``: the hash count of the closer has to
    match the opener's, which is the whole reason a raw string can hold a bare
    ``"``.  ``r`` preceded by an identifier character is part of that identifier
    and opens nothing.
    """
    if text[index] != "r" or _reference_identifier_char(text, index - 1):
        return None
    hashes = 0
    while index + 1 + hashes < len(text) and text[index + 1 + hashes] == "#":
        hashes += 1
    position = index + 1 + hashes
    if position >= len(text) or text[position] != '"':
        return None
    return position + 1, '"' + "#" * hashes


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

    A run holding a **blank line** becomes :data:`PARAGRAPH` rather than a space.
    A line wrap and a paragraph break were the same character after flattening,
    so a clause window could not tell "the rest of this sentence" from "the next
    paragraph", and two live keys were pinned with a count borrowed across the
    gap: ``The corresponding susceptibility wrapper now lives in `X` `` -- one
    wrapper -- was keyed ``2->X`` from the *previous* paragraph's ``for the two
    ... wrappers``.  Like :data:`MASK`, it is not whitespace, so an anchor cannot
    span it either; measured on this tree, no anchor did.
    """
    chars: list[str] = []
    offsets: list[int] = []
    for run in _RUN.finditer(text):
        if text[run.start()].isspace():
            chars.append(PARAGRAPH if run.group(0).count("\n") > 1 else " ")
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
    "zero": 0, "one": 1, "two": 2, "three": 3, "four": 4, "five": 5, "six": 6,
    "seven": 7, "eight": 8, "nine": 9, "ten": 10, "eleven": 11, "twelve": 12,
    "thirteen": 13, "fourteen": 14, "fifteen": 15, "sixteen": 16, "seventeen": 17,
    "eighteen": 18, "nineteen": 19,
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

#: Multipliers that scale the value in front of them without closing a group:
#: ``two hundred`` is 200 and ``twelve hundred`` is 1200.  ``dozen`` is one of
#: them rather than a word for twelve, because ``two dozen`` is 24.
_MULTIPLIER_WORDS: dict[str, int] = {"hundred": 100, "dozen": 12}

#: Scales that *close* a place-value group: everything accumulated so far is
#: multiplied by them and banked, so ``one hundred thousand`` is 100000 and the
#: next group starts empty (``one thousand two hundred`` is 1200).
_GROUP_WORDS: dict[str, int] = {"thousand": 1000, "million": 1000000, "billion": 10 ** 9}

#: The multiplicative scales.  They compose (``two hundred``) rather than add,
#: which is why the compound resolver below is a small parser and not a sum.
_SCALE_WORDS: dict[str, int] = {**_MULTIPLIER_WORDS, **_GROUP_WORDS}

#: The indefinite article, which is a cardinal in front of a scale: ``a dozen``
#: and ``a hundred`` are counts, and reading them as prose was one of the
#: measured bypasses.
_ARTICLE_WORDS = frozenset({"a", "an"})

#: Every recognized cardinal word.
WORD_NUMBERS: dict[str, int] = {**_UNIT_WORDS, **_TEN_WORDS, **_SCALE_WORDS}

#: Quantifiers that assert a population without naming its size.  They fail the
#: split-stability test exactly as a numeral does ("the remaining wrappers"
#: changes meaning the moment a sibling module is carved out), so they are
#: charged, with the word itself as the token.
VAGUE_QUANTIFIERS = frozenset(
    {"several", "many", "various", "numerous", "multiple", "both", "remaining", "few",
     "couple", "handful"}
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

#: One place-value group: an optional multiplicand (a small cardinal, or the
#: article of ``a dozen``) and the scale it multiplies.
_SCALE_GROUP = rf"(?:(?:{_SMALL_CARDINAL}|an?)\s+)?(?:{_SCALES_ALT})"

#: A cardinal phrase.  A grammar rather than a free repetition of cardinal
#: words: ``three four`` is not a number and must not be read as seven.
#:
#: Scale groups repeat, because English place value does: ``one thousand two
#: hundred`` is two groups and ``one hundred thousand`` is one group closed by a
#: second scale.  A grammar that admitted only one group stopped after the first
#: small tail, and the *prefix* it had matched was then normalized -- ``one
#: thousand two hundred`` read as 1002 and ``one hundred thousand`` as 100.  A
#: truncated parse is worse than no parse: the claim is charged under a token
#: that names a different number.
_CARDINAL = (
    rf"(?:{_SCALE_GROUP}(?:\s+(?:and\s+)?(?:{_SCALE_GROUP}|{_SMALL_CARDINAL}))*"
    rf"|{_SMALL_CARDINAL})"
)

#: A numeral, with or without thousands separators.  ``1,024`` is a count; a
#: grammar that only knew ``\d+`` read it as ``1`` at best and matched nothing
#: at worst, so the comma-grouped form is recognized explicitly.
_NUMERAL = r"(?:\d{1,3}(?:,\d{3})+|\d+)"

#: Hedges that make a count approximate without making it any less of a claim
#: about module extension.  ``about twelve wrappers`` goes stale on exactly the
#: same split that ``twelve wrappers`` does, so a hedge must never buy silence.
#:
#: The list is closed by the same argument the cardinals are: these are the
#: English ways of putting a number at arm's length, and leaving any of them out
#: is an unadvertised bypass rather than a recall nicety.  ``for a total of 12``,
#: ``for some 12``, ``for circa 12`` and ``for no fewer than 12`` were all
#: silently *accounted* while ``for 12`` was charged, because the head-quantity
#: pattern falls back to a single token and an unlisted hedge is what that token
#: turns out to be.
#:
#: Every hedge here normalizes its count to ``~N``, so the list may only hold
#: words for which that is *true*: ``half a dozen`` would be charged ``~12``, a
#: number the prose does not state, which is why ``half`` is a
#: :data:`RANGE_MARKERS` word instead.
HEDGE_PHRASES: tuple[str, ...] = (
    "about", "approximately", "roughly", "around", "nearly", "circa", "some",
    "over", "under", "at least", "at most", "no fewer than", "no more than",
    "no less than", "more than", "fewer than", "less than", "up to",
    "a total of", "close to", "upwards of", "exactly", "precisely", "just", "only",
)

#: Words that mark a numeric claim the normalizer must **not** fold into one
#: integer: a range, a sign or a fraction.  They are numeric evidence -- ``for
#: between 10 and 12 wrappers`` is as much an inventory claim as ``for 12
#: wrappers`` -- so they reach the fail-closed ``?<phrase>`` token, and they are
#: kept out of :data:`HEDGE_PHRASES` precisely so that they cannot be normalized
#: to a specific number nobody wrote.
RANGE_MARKERS: tuple[str, ...] = ("between", "minus", "plus", "negative", "half")


def _phrase_alternation(phrases: Iterable[str]) -> str:
    """Return a longest-first regex alternation of ``phrases``, spaces relaxed.

    The corpus is matched on whitespace-flattened text, but a phrase written
    with a plain space here still has to survive :func:`flatten`'s single-space
    normalization *and* stay readable in the tables above, so the substitution
    happens once, here.
    """
    relaxed = (re.escape(phrase).replace("\\ ", r"\s+") for phrase in phrases)
    return "|".join(sorted(relaxed, key=len, reverse=True))


_HEDGE = rf"(?:[~≈]\s*|(?:{_phrase_alternation(HEDGE_PHRASES)})\s+)"

#: The same vocabulary as a word set, derived from the same tuple rather than
#: written out again.  Two spellings of one closed class is how the head
#: extractor and :func:`resolve_quantity` came to disagree about what a hedge is
#: in the first place.
HEDGE_WORDS = frozenset(word for phrase in HEDGE_PHRASES for word in phrase.split())

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

#: What makes a quantity fragment unmistakably a claim even when it cannot be
#: normalized: it *starts* with a digit, a hedge, a range marker or a vague
#: quantifier.  This is the fail-closed half of :func:`resolve_quantity` --
#: ``12-ish``, ``about 12ish``, ``between 10 and 12`` and ``half a dozen`` are
#: claims whatever the grammar makes of them.
#:
#: Two deliberate non-members, both measured on this corpus rather than guessed:
#:
#: * a digit appearing *later* in the fragment.  The corpus's non-claim head
#:   words are section references (``§18.3-§18.4``, 52 sites), so "contains a
#:   digit anywhere" is a pure false positive.  :func:`quantity_fragment` is what
#:   makes the leading-position rule reachable: it hands over the whole quantity
#:   phrase rather than its first whitespace-delimited token, and it stops at a
#:   citation token, so a ``§`` reference never enters a fragment at all.
#: * a cardinal *word* followed by a hyphen.  ``two-sided``, ``three-part`` and
#:   ``four-point`` are adjectives in this corpus, not counts, so ``twelve-odd``
#:   stays uncharged as the price of not charging them.
_NUMERIC_IDIOM = re.compile(
    rf"\A(?:{_HEDGE}"
    rf"|(?:{_phrase_alternation(RANGE_MARKERS)}|{_alternation(VAGUE_QUANTIFIERS)})(?:\s|\Z)"
    rf"|[-+]?\d)",
    re.IGNORECASE,
)

#: A token that cites a location rather than counting anything.  ``§18.3``,
#: ``#4501`` and ``PR#12`` carry digits and are not quantities, and this repo's
#: prose is full of them.
_CITATION_TOKEN = re.compile(r"[§#]")

#: A token that opens a quantity: a signed digit anywhere at its front.
_DIGIT_INITIAL = re.compile(r"\A[-+]?\d")

#: Words that may appear *inside* a quantity phrase without being quantities
#: themselves (``no fewer than 12``, ``between 10 and 12``, ``a total of 12``).
#: A phrase may never *end* on one, so they cannot extend a fragment into the
#: prose that follows it.
_QUANTITY_CONNECTIVES = frozenset({"and", "or", "to", "of", "the", "than"})

#: The determiners a quantity may hide behind, shared by the head extractor and
#: by the relocation subject.  They were two different lists: ``RELOCATION``
#: accepted ``the|these|its|all`` while ``NARROW_CHILD`` accepted only ``the``,
#: so ``All 13 foo wrappers now live in `X` `` was charged and ``Narrow child
#: module for all 13 foo wrappers`` was not -- the same lexical class, two
#: verdicts, in one file.
DETERMINERS: tuple[str, ...] = (
    "each of the", "the", "these", "those", "this", "that", "its", "their", "our",
    "all", "same",
)

#: Zero or more determiners in front of the quantity (``the same 12``).
_DETERMINER_PREFIX = rf"(?:(?:{_phrase_alternation(DETERMINERS)})\s+)*"

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

#: How far a claim may reach between its quantity and its noun, in characters.
#:
#: A measured number, not a guess, and it was 70 -- which cost recall the review
#: quantified: this repository's house style puts a backticked list of names
#: between the count and the noun it counts (``The 10 Λ-level h-symmetry,
#: odd-vanish at h=0, J_zero, and tanh-power lower-bound wrappers``), so the
#: shortest real claims fitted and the typical ones did not.  At 200, on the
#: tracked tree, ``RELOCATION`` resolves 273 more subjects and every other class
#: is unchanged; a 25-site sample of them was read one by one and every one was a
#: real claim of exactly the pinned shape.
#:
#: The cost of the widening was also measured, and it is why :data:`PARAGRAPH`
#: exists: 3 of the 408 resolved spans reached across a **blank line** into the
#: paragraph above to borrow a count, and all three were wrong.  A length cap
#: cannot express "one paragraph"; the boundary has to be a character the window
#: may not cross.
_CLAUSE_SPAN = 200


#: One character a claim clause may contain.  What ends a clause: a sentence
#: break, a table-cell boundary, a comment delimiter, a masked region and -- since
#: the paragraph sentinel exists -- a blank line.  Without the first four the
#: window reaches from ``its two arguments.`` in one doc comment into the word
#: ``lemma`` of the declaration underneath it; without the last it reaches into
#: the next paragraph and borrows its count.  ``\n`` is redundant on flattened
#: text and kept so the class is safe against a caller that has not flattened.
_CLAUSE_CHAR = rf"(?:(?!\.\s|;|\||-/|/-)[^{MASK}{PARAGRAPH}\n])"


def _window(limit: int = _CLAUSE_SPAN, *, lazy: bool = True) -> str:
    """Return a run of at most ``limit`` characters inside one clause.

    ``lazy`` is what tells a *gap* (a quantity reaching for its noun, which must
    stop at the first candidate) from a *span* (a head clause, which runs to the
    end of the clause and is then parsed).  Both obey :data:`_CLAUSE_CHAR` and
    both are bounded by the same measured :data:`_CLAUSE_SPAN`: the head clause
    used to carry a bare ``{0,120}`` of its own, a number nothing measured, next
    to a docstring arguing at length that such caps must be.
    """
    return rf"{_CLAUSE_CHAR}{{0,{limit}}}" + ("?" if lazy else "")


_WINDOW = _window()


def cardinal_value(phrase: str) -> int | None:
    """Return the value of a cardinal ``phrase``, or ``None`` if it is not one.

    Place value, not a sum: a multiplier scales what stands in front of it
    (``two hundred`` is 200, ``twelve hundred`` is 1200, ``two dozen`` is 24) and
    a group word banks it (``one hundred thousand`` is 100000) so that the next
    group starts from zero (``one thousand two hundred`` is 1200).  A plain sum
    over the words -- the shape this started as -- reads ``two hundred`` as 102;
    a version that banked on every scale read ``one thousand two hundred`` as
    1002 and ``one hundred thousand`` as 100.
    """
    total = 0
    current = 0
    seen = False
    for word in re.split(r"[-\s]+", phrase.strip().lower()):
        if not word or word == "and":
            continue
        if word in _ARTICLE_WORDS:
            current += 1
        elif word in _MULTIPLIER_WORDS:
            current = (current or 1) * _MULTIPLIER_WORDS[word]
        elif word in _GROUP_WORDS:
            total += (current or 1) * _GROUP_WORDS[word]
            current = 0
        elif word in WORD_NUMBERS:
            current += WORD_NUMBERS[word]
        else:
            return None
        seen = True
    return total + current if seen else None


def _quantity_word(token: str) -> bool:
    """Whether ``token`` can be part of a quantity phrase.

    A signed numeral, a cardinal word, an article (``a dozen``), a hedge word, a
    range marker or a vague quantifier -- but never a citation, because
    ``§18.3-§18.4`` and ``#4501`` carry digits and count nothing.
    """
    word = token.strip(",.;:!?)(`*").lower()
    if not word or _CITATION_TOKEN.search(word):
        return False
    if _DIGIT_INITIAL.match(word):
        return True
    return (
        word in HEDGE_WORDS
        or word in RANGE_MARKERS
        or word in WORD_NUMBERS
        or word in _ARTICLE_WORDS
        or word in VAGUE_QUANTIFIERS
    )


def quantity_fragment(rest: str) -> str:
    """Return the leading quantity phrase of ``rest``, or ``''`` if it has none.

    The head extractor's second stage, and the reason the fail-closed rule in
    :func:`resolve_quantity` is reachable at all.  Its predecessor captured a
    single whitespace-delimited token, so ``about 12ish`` arrived as ``about``
    -- resolved to "not a quantity", *accounted*, free -- and the module
    docstring's own worked example of a fail-closed charge was itself uncharged.
    ``about 1.5k``, ``between 10 and 12``, ``minus twelve`` and ``half a dozen``
    were free for the same reason.

    Maximal munch over :func:`_quantity_word`, with connectives allowed only
    *between* quantity words: the phrase can neither start nor end on one, so it
    cannot reach past the count into the noun phrase that follows it.
    """
    taken: list[str] = []
    for token in rest.split():
        connective = bool(taken) and token.strip(",.;:!?)(`*").lower() in _QUANTITY_CONNECTIVES
        if not (_quantity_word(token) or connective):
            break
        taken.append(token)
    while taken and not _quantity_word(taken[-1]):
        taken.pop()
    return " ".join(taken)


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
    words = word.split()
    vague = [part for part in words if part in VAGUE_QUANTIFIERS]
    if vague and all(
        part in VAGUE_QUANTIFIERS or part in _ARTICLE_WORDS or part in _QUANTITY_CONNECTIVES
        for part in words
    ):
        # ``a few``, ``a couple of``: an article and a connective around a vague
        # quantifier state exactly what the bare word does.
        return vague[0], True
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
    """One extracted record: the ratchet key plus where it was found.

    Which *ledger* it lands in is not a field of it.  Every record in
    :attr:`Report.claims` is charged, and the handful that are not are
    :attr:`Report.telemetry` -- a separate, explicitly non-authoritative list.
    A ``charged`` flag on the record itself is what let the largest population in
    the corpus sit inside the authoritative ledger marked "recognized, free".
    """

    kind: str
    target: str
    token: str
    line: int
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

    ``charged`` is ``False`` only where the shape carries no inventory size at
    all, which is a fact about the *prose* and never about the extractor's
    success.  Exactly one of the five classes can return it
    (:func:`_extract_narrow_child`, the only ``return`` in this file with a
    ``False`` in that position); a quantity that fails to parse never does.
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

#: ``for <determiners> <head>`` immediately after the anchor.  The determiners
#: are :data:`DETERMINERS` -- the same list the relocation subject uses, because
#: they are the same lexical class and two lists meant ``for all 12 wrappers``
#: was free while ``All 12 wrappers now live in `X` `` was charged.
#:
#: No ``\A``: the pattern is applied with a ``pos`` argument, which ``\A``
#: ignores (it means "start of string", not "start of the search"), and getting
#: that wrong silently turns every head quantity into an unresolved token.
#: ``re.IGNORECASE`` for the same reason the anchors carry it -- ``For The 12``
#: is the same claim, and this was the last case-sensitive link in the chain.
#:
#: ``head`` runs to the end of the clause rather than to the end of the first
#: word; :func:`head_quantity` is what decides how much of it is the count.  It
#: is :func:`_window` like every other clause run, so it stops at a sentence
#: break, a table-cell boundary, a comment delimiter, a masked region or a
#: paragraph break, and it cannot reach out of the sentence it belongs to.
_HEAD_CLAUSE = re.compile(
    rf"\s*for\s+{_DETERMINER_PREFIX}(?P<head>{_window(lazy=False)})",
    re.IGNORECASE,
)

#: A clean count at the very front of the head clause.  The trailing lookahead
#: excludes ``.`` and ``,`` as well as word characters and ``-``: without them
#: ``1.5k`` matched the ``1`` and was charged under the token ``1``, a wrong
#: number rather than an unresolved one.  Excluded, the whole fragment falls to
#: :func:`quantity_fragment` and the fail-closed rule in
#: :func:`resolve_quantity` charges it as ``?1.5k``.
_HEAD_QUANTITY = re.compile(rf"({QUANTITY})(?![\w.,-])", re.IGNORECASE)


def head_quantity(head: str) -> str:
    """Return the fragment of head clause ``head`` that states its count.

    Three stages, narrowest first: a clean quantity at the front, else the
    maximal quantity phrase, else the first word -- which is what keeps the
    extractor total, so a purely descriptive head still produces a record.

    All three read the **front** of the clause.  A count that sits behind a
    modifier is :func:`clause_quantities`' job, and it is a separate function
    because it answers a weaker question: *this clause states a size somewhere*,
    rather than *this clause opens with a count of its noun*.
    """
    clean = _HEAD_QUANTITY.match(head)
    if clean is not None:
        return clean.group(1)
    fragment = quantity_fragment(head)
    if fragment:
        return fragment
    words = head.split()
    return words[0] if words else ""


#: The words after which a number cites a location instead of counting anything.
#: ``Step 241 interior wrappers`` and ``PR 1861 wrappers`` state no inventory
#: size, and this repository's prose is full of both.  A closed list of citation
#: nouns is the cheap half of the guard; the other half is lexical
#: (:data:`_GOVERNED_QUANTITY`'s left context, which refuses ``§``, ``#`` and the
#: relation symbols, so ``J = 0 wrappers`` is an expression rather than a count).
CITATION_WORDS = frozenset(
    {
        "step", "steps", "pr", "prs", "issue", "issues", "section", "sections",
        "chapter", "chapters", "part", "parts", "phase", "phases", "lemma", "lemmas",
        "theorem", "theorems", "proposition", "propositions", "corollary", "corollaries",
        "remark", "remarks", "equation", "equations", "figure", "figures", "table",
        "tables", "page", "pages", "item", "items", "note", "notes", "exercise",
        "exercises", "version", "versions",
    }
)

#: An inline code span: backticks in Lean and Markdown prose, ``\texttt``/``\path``
#: in the TeX guide.
_CODE_SPAN = re.compile(r"`[^`]*`|\\(?:texttt|path)\{[^}]*\}")


def blank_code(text: str) -> str:
    """Return ``text`` with the *inside* of every inline code span blanked out.

    Length-preserving, and the delimiters stay, so the result is still the same
    clause with the same offsets -- only the identifiers and expressions inside
    it are gone.

    A number inside backticks belongs to Lean, not to English: measured on this
    tree, a whole-clause quantity scan without this charges four more headers,
    and all four are expressions -- ``mayerPartialSum 0 ≤ polymerFreeEnergy`` as
    the count 0, ``vdPolymerFamilies_sum - 1`` as the count 1.  That is the exact
    "recall bought with false charges" the head-position rule was defending
    against, which is why the replacement for it has to be lexical.
    """
    return _CODE_SPAN.sub(
        lambda span: span.group(0)[0] + " " * (len(span.group(0)) - 2) + span.group(0)[-1],
        text,
    )


#: Where a token begins: the start of the clause, or the first character after a
#: whitespace run.  :func:`quantity_fragment` reads whitespace-delimited tokens,
#: so these are the only positions a quantity phrase can start at.
_TOKEN_START = re.compile(r"(?:\A|(?<=\s))\S")

#: An inventory noun the quantity just read governs: it has to follow within the
#: same clause window, exactly as the possessive and predicate classes require.
_GOVERNED_NOUN = re.compile(rf"\A\s+{_WINDOW}{INVENTORY_NOUN}\b", re.IGNORECASE)


#: Token endings after which a number is an operand rather than a count.
#: ``regularity-at-J=0`` is one token and :func:`quantity_fragment` never opens
#: on it, but ``J = 0`` is the same expression with spaces in it -- and this
#: corpus writes both (``Narrow child module for the susceptibilityInfinite
#: J = 0 closed form ... wrappers``).
_OPERATOR_ENDINGS: tuple[str, ...] = ("=", "<", ">", "≤", "≥", "≠", "+", "*", "/", "^", "·", "×")


def _cites_rather_than_counts(clause: str, start: int) -> bool:
    """Whether the token in front of ``start`` makes the number after it not a count."""
    before = clause[:start].rstrip()
    if not before or not before.split():
        return False
    previous = before.rsplit(maxsplit=1)[-1]
    if previous.endswith(_OPERATOR_ENDINGS):
        return True
    return previous.strip("(`*,;:[]").lower() in CITATION_WORDS


def clause_quantities(clause: str) -> tuple[str, ...]:
    """Return the resolved tokens of every count in ``clause`` that governs a noun.

    Deduplicated and in the order they are written.  This is what closes round
    4's H1: the head extractor's three stages all read position 0, so a single
    adjective moved the number out of reach and ``Narrow child module for the
    following 17 wrappers`` produced no key at all -- not a coarse one, none --
    while ``for all 17 wrappers`` was charged.  Widening the *determiner* list
    (twice) never touched that, because the rule was positional and English puts
    whatever it likes between a determiner and a number.

    R3.1 is the standard it has to meet: a count-like extraction failure is
    charged, never filed as telemetry.  So the question here is deliberately the
    weak one -- does this clause state a size at all? -- and the answer is
    charged under a ``?`` token, because a count that is not in head position is
    a size the sentence states without the extractor knowing which noun it
    counts.

    It reads the clause with the *same* two functions the head extractor uses
    -- :func:`quantity_fragment` for what a quantity phrase is and
    :func:`resolve_quantity` for whether it is one -- at every token position
    instead of only the first.  Two notions of "quantity", one per position,
    is how ``for about 1.5k wrappers`` came to be charged and ``for the concrete
    about 1.5k wrappers`` free.  What is *not* shared is the requirement that
    the phrase govern an inventory noun (:data:`_GOVERNED_NOUN`): in head
    position the ``for`` clause supplies that, and away from it a number without
    a noun to count is prose.
    """
    text = blank_code(clause)
    found: list[str] = []
    consumed = 0
    for start in (match.start() for match in _TOKEN_START.finditer(text)):
        # A phrase is read once: ``twelve hundred`` opens at both of its words
        # and ``about 1.5k`` at both of its, so without this the clause reports
        # 1200 *and* 100 and calls itself ambiguous.
        if start < consumed or _cites_rather_than_counts(text, start):
            continue
        fragment = quantity_fragment(text[start:])
        if not fragment:
            continue
        token, is_quantity = resolve_quantity(fragment)
        if is_quantity and _GOVERNED_NOUN.match(text[start + len(fragment):]) is not None:
            found.append(token)
            consumed = start + len(fragment)
    return tuple(dict.fromkeys(found))


def _extract_narrow_child(flat: str, match: re.Match[str]) -> tuple[str, bool, str]:
    """Extract the size of ``Narrow child module for [the] N ...``.

    Two questions, in order, and the second one exists because the first is
    positional.  A count at the **front** of the head clause names the module's
    own size and is charged as itself (``12``).  Failing that, a count anywhere
    in the clause that governs an inventory noun is charged under a ``?`` token
    (``?17``): the sentence states a size, and the extractor is not claiming to
    know which noun it belongs to.  The ``?`` keeps the two apart in the ledger
    while keeping the key sharp -- editing the number is still a new key.

    The earlier rule was "head position only", on the argument that a later
    numeral belongs to a section number or a cited identifier and that the
    parenthetical and predicate classes pick up counts stated elsewhere.  Both
    halves were measured false.  ``for the following 17 wrappers`` is not a
    citation and produced *no key at all*; and where another class does also
    charge the number (``... wrappers (9 theorems)``), filing this record as
    telemetry still states something false about this prose -- telemetry means
    "states no size", and that header states one.  What keeps the false charges
    out is lexical instead of positional: code spans are blanked
    (:func:`blank_code`), and citation words and relation symbols are refused
    (:data:`CITATION_WORDS`, :data:`_GOVERNED_QUANTITY`).

    This is the one class that can decline to charge, and what it declines on is
    a header that states no size at all (``Narrow child module for concrete
    `latticeGraph` specializations``).  That record is **telemetry**, not a
    verdict: it is reported apart from :attr:`Report.claims` and never pinned,
    so no quantity that fails to parse can land in it -- an unresolvable count
    is charged (``?<fragment>``), a missing ``for`` clause is charged, and only
    the absence of numeric content at all is telemetry.
    """
    clause = _HEAD_CLAUSE.match(flat, match.end())
    if clause is None:
        return "-", True, "no `for` clause after the anchor"
    head = clause.group("head")
    token, is_quantity = resolve_quantity(head_quantity(head))
    if is_quantity:
        return token, True, ""
    governed = clause_quantities(head)
    if governed:
        # ``?`` once, whatever the parts already carry: ``resolve_quantity``
        # marks an unnormalizable fragment with one of its own.
        marked = "/".join(governed)
        note = ("count behind a modifier, not in head position" if len(governed) == 1
                else f"{len(governed)} counts in one clause")
        return (marked if marked.startswith("?") else f"?{marked}"), True, note
    return "-", False, f"no quantity (head {token!r})"


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
    rf"\s+{_DETERMINER_PREFIX}({QUANTITY})\s+{_WINDOW}({INVENTORY_NOUN})\b",
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

#: One written reference: a backticked module or file name, or a
#: ``\texttt{...}`` / ``\path{...}`` one in the TeX guide.  ``\path`` is how the
#: guide writes most of its file names, and without it 53 of its relocations
#: shared the one ``->?`` key.
_REFERENCE = r"(?:`([^`]+)`|\\(?:texttt|path)\{([^}]*)\})"

#: The destination as written just after ``now live in``.  No ``\A`` -- see
#: :data:`_HEAD_CLAUSE` for why that would silently erase every destination.
_DESTINATION = re.compile(rf"[\s(]*{_REFERENCE}")

#: The rest of a destination that was **wrapped**: a second reference separated
#: from the first by whitespace and nothing else.  This repository's headers
#: break a long module name across two spans at a dot::
#:
#:     ... now live in
#:     `IsingModel.AmbientLattice.SpecialCases.`
#:     `SusceptibilityPointwiseRegularityAtDifferentiableAt`.
#:
#: and a single-span destination read that as
#: ``IsingModel.AmbientLattice.SpecialCases.`` -- a namespace, not a module.  Four
#: pinned rows were in that state, and the review verified the consequence:
#: rewriting the *second* half to name a completely different module left the pin
#: byte-identical and both gates green, so for those four sentences the fact the
#: class exists to pin was not pinned at all.
#:
#: Joining is the fail-closed direction and that is why it is unconditional
#: rather than restricted to a first span ending in a dot.  A truncated
#: destination silently pins less than the claim says; a joined one pins a key
#: that changes when either half changes.  Measured on this tree: exactly four
#: relocations are followed by an adjacent second span, and all four are these
#: wraps.
_WRAPPED_TAIL = re.compile(rf"\s+{_REFERENCE}")


def destination(flat: str, position: int) -> str:
    """Return the destination written at ``position``, wrapped name and all."""
    head = _DESTINATION.match(flat, position)
    if head is None:
        return "?"
    parts = [(head.group(1) or head.group(2) or "").strip()]
    end = head.end()
    while (tail := _WRAPPED_TAIL.match(flat, end)) is not None:
        parts.append((tail.group(1) or tail.group(2) or "").strip())
        end = tail.end()
    return "".join(parts) or "?"

#: The *subject* of a relocation claim: a :data:`DETERMINERS` word + a quantity
#: + an inventory noun, optionally followed by a connective clause, running right
#: up to ``now live in``.
#:
#: What this decides is only how *sharp* the key is -- the anchor is charged
#: either way (see :func:`_extract_relocation`) -- so its false positives cost a
#: wrong number in a token and its false negatives cost a coarse one.  Each part
#: was still added against a measured false positive rather than on suspicion.
#: A free backwards search for "some quantity earlier in the paragraph" bound 468
#: of this tree's 767 relocation sentences to a number, mostly borrowed from an
#: adjacent bullet of the same ``## Moved:`` block.  Requiring the inventory noun
#: removes ``(under `0 ≤ β`, `0 ≤ J`) now live in``.  Requiring the determiner
#: removes ``Step 241 interior `ContinuousAt` wrappers) now live in`` and the
#: ``PR #1861`` / ``Issue #4501`` references, without an ever-growing list of
#: number prefixes to exclude.  The connective tail is what keeps the archetype
#: ``the three ... wrappers were split out again in PR #2354 and now live in X``
#: (docs/index.md:1393, the F4 site) resolved.
#:
#: Split into head and tail so the *nearest* subject wins: ``re.search`` is
#: leftmost-first, which would bind ``now live in`` to the first determiner in
#: the window rather than to the noun phrase actually in front of it.
#:
#: The head carries the same trailing lookahead :data:`_HEAD_QUANTITY` does, for the same
#: reason: with a bare ``\b``, ``The zero-boundary linear bounds ... now live in
#: X`` bound the subject to the cardinal ``zero`` and pinned the claim under the
#: token ``0`` -- a number the sentence does not state.  A cardinal glued to a
#: following word is an adjective in this corpus (``zero-boundary``,
#: ``two-sided``, ``three-part``), never a count.
_SUBJECT_HEAD = re.compile(
    rf"(?:^|(?<=[^\w`]))(?:(?:{_phrase_alternation(DETERMINERS)})\s+)+({QUANTITY})(?![\w.,-])",
    re.IGNORECASE,
)
_SUBJECT_TAIL = re.compile(
    rf"\s*{_WINDOW}{INVENTORY_NOUN}\b{_window()}\Z",
    re.IGNORECASE,
)


#: How far back a relocation's subject may start.  It has to hold a determiner,
#: a count, a ``_CLAUSE_SPAN`` run to the inventory noun and a second one to the
#: anchor, so it is twice the clause span plus room for the noun phrase itself.
_SUBJECT_LOOKBACK = 2 * _CLAUSE_SPAN + 64


def relocation_subject(window: str) -> re.Match[str] | None:
    """Return the nearest quantified subject ending at ``window``'s end."""
    nearest: re.Match[str] | None = None
    for head in _SUBJECT_HEAD.finditer(window):
        if _SUBJECT_TAIL.match(window, head.end()) is not None:
            nearest = head
    return nearest


def _extract_relocation(flat: str, match: re.Match[str]) -> tuple[str, bool, str]:
    """Extract ``The 13 ... wrappers now live in `X` `` -- a claim about *another* module.

    **Every anchor is charged**, quantified or not, and the token records the
    destination whether or not a count resolves.  ``... now live in `X` `` *is*
    the ownership assertion this tool ratchets: it goes stale on exactly the
    split that a counted version does, and where it points is the fact being
    claimed.  Making the charge conditional on parsing an adjacent quantity made
    the quantity extractor the thing that decided exemption, which is how 647 of
    this tree's 767 relocation sentences -- the single largest recognized
    population in the corpus, most of them visibly quantified -- sat in a bucket
    that was reported as "recognized" and cost nothing.

    Resolution now only sharpens the key: ``12->X`` is a tighter pin than
    ``->X``, because editing the 12 is then a new key, but ``->X`` is already a
    pin on the sentence's existence.
    """
    target = destination(flat, match.end())
    subject = relocation_subject(flat[max(0, match.start() - _SUBJECT_LOOKBACK):match.start()])
    if subject is None:
        return f"->{target}", True, "ownership claim, no quantified subject"
    token, is_quantity = resolve_quantity(subject.group(1))
    if not is_quantity:
        return f"?->{target}", True, "unresolved quantity"
    return f"{token}->{target}", True, ""


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
    """One scanned input: its ledger key, its path, its text and its kind.

    ``target`` **is** ``path``.  They are two fields rather than one so that the
    ledger's identity has a name of its own, and so that ``K4``
    (:func:`key_failures`) has something to assert rather than a tautology
    spread across the call sites: the moment somebody derives ``target`` from
    ``path`` again -- which is how a dotted module name became a key that two
    files could share -- the law fires on the constructed inputs the suite
    feeds it.
    """

    target: str
    path: str
    text: str
    is_lean: bool


class SourceReport(NamedTuple):
    """The findings and conservation ledger of one source.

    ``claims`` is the authoritative ledger and every row in it is charged;
    ``telemetry`` is the coverage report and no row in it is ever pinned.  They
    are two fields rather than one flagged list because a single list with a
    ``charged`` column is a place for a charge to be quietly filed as free.
    """

    source: Source
    claims: tuple[Claim, ...]
    telemetry: tuple[Claim, ...]
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

    ``K1`` counts records across **both** ledgers, so routing a row to
    ``telemetry`` is not a way to lose it: the law is that every anchor produces
    exactly one record somewhere, and where it goes is a separate question.
    """
    text = source.text
    decomposition = decompose(text) if source.is_lean else decompose_document(text)
    raw = flatten(text)
    prose = flatten(apply_mask(text, decomposition.regions))
    starts = line_starts(text)
    claims: list[Claim] = []
    telemetry: list[Claim] = []
    failures: list[str] = []

    if source.is_lean and decomposition.regions != reference_regions(text):
        failures.append(
            f"K3 {source.target}: the comment decomposition disagrees with the "
            "independent oracle"
        )
    if not decomposition.terminated:
        claims.append(
            Claim(UNTERMINATED, source.target, "-", 1, "comment or string never closed")
        )
    if source.is_lean and not decomposition.module_doc:
        claims.append(
            Claim(MISSING_DOC, source.target, "-", 1, "no `/-!` module docstring to inspect")
        )

    for claim_class in CLAIM_CLASSES:
        raw_matches = list(claim_class.anchor.finditer(raw.text))
        prose_matches = list(claim_class.anchor.finditer(prose.text))
        before = len(claims) + len(telemetry)
        inside = 0
        for match in raw_matches:
            begin = raw.origin(match.start())
            finish = raw.origin(max(match.end() - 1, match.start()))
            in_prose = any(start <= begin and finish < end for start, end in decomposition.regions)
            line = line_of(starts, begin)
            if in_prose:
                inside += 1
                token, charged, note = claim_class.extract(raw.text, match)
                record = Claim(claim_class.name, source.target, token, line, note)
                (claims if charged else telemetry).append(record)
            else:
                claims.append(
                    Claim(
                        NON_PROSE,
                        source.target,
                        claim_class.name,
                        line,
                        "anchor outside any comment body",
                    )
                )
        # Counted from the records that were actually appended, never from the
        # loop's own bookkeeping: an early `continue` -- the shape a "skip the
        # tokens I cannot resolve" edit takes -- has to be what this number
        # misses, otherwise K1 would only ever confirm its own arithmetic.
        produced = len(claims) + len(telemetry) - before
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
    return SourceReport(
        source=source,
        claims=tuple(claims),
        telemetry=tuple(telemetry),
        conservation=tuple(failures),
    )


# --------------------------------------------------------------------------
# The tracked target set
# --------------------------------------------------------------------------


def tracked_paths(root: Path = REPO_ROOT) -> tuple[str, ...]:
    """Return the repo-relative paths of every target, from ``git ls-files``.

    The VCS index -- not the filesystem -- is the source of truth for which
    files exist: a scanner that walks the tree reads build artefacts, editor
    backups and ignored scratch copies, and this repository has been bitten by
    exactly that.

    :data:`SCAN_ROOTS` filtered to :data:`SCAN_SUFFIXES`, minus
    :data:`EXCLUDED_ROOTS`.  The exclusion is redundant against those roots and
    is applied anyway: it is the statement that ``test/``, ``.github/`` and
    ``scripts/`` are out of scope *on purpose*, so widening the roots later
    cannot drag the tool's own fixtures into the population by accident.
    """
    result = subprocess.run(
        ["git", "-C", str(root), "ls-files", "-z", "--", *SCAN_ROOTS],
        capture_output=True,
        text=True,
        check=True,
    )
    paths = [entry for entry in result.stdout.split("\0") if entry]
    return tuple(
        sorted(
            path
            for path in paths
            if path.endswith(SCAN_SUFFIXES) and not path.startswith(EXCLUDED_ROOTS)
        )
    )


def display_name(path: str) -> str:
    """Return the dotted Lean module name of ``path``, **for display only**.

    Never an identity.  ``path.replace("/", ".")`` is not injective:
    ``IsingModel/AmbientLattice/Analyticity.lean`` and
    ``IsingModel/AmbientLattice.Analyticity.lean`` are two distinct tracked files
    with one dotted name, and a ledger keyed on it cannot tell them apart.  The
    review built that into a working laundering channel: reword the pinned claim
    in the first file into a shape the grammar does not recognize, write the same
    sentence into the second, and the pin is byte-identical -- one file's vacated
    capacity paid for the other's new claim, with ``--check`` and the drift check
    both green.  The same collision broke ``B2``, whose "is this key's file in
    the diff?" question resolved to the wrong file.

    The ledger is keyed by :attr:`Source.path` now, and ``K4`` asserts that.
    This function survives because a dotted name is what a Lean reader wants to
    see next to a finding, and a display string that is never a key cannot
    collide with anything.
    """
    return path[: -len(".lean")].replace("/", ".") if path.endswith(".lean") else path


def load_sources(root: Path = REPO_ROOT, paths: Iterable[str] | None = None) -> tuple[
    tuple[Source, ...], tuple[str, ...]
]:
    """Read every target, returning ``(sources, K0 failures)``.

    A path that cannot be read is a ``K0`` failure, never a skip -- and
    "unreadable" includes *undecodable*.  A tracked file holding a byte that is
    not UTF-8 used to raise ``UnicodeDecodeError`` out of here: the run still
    failed closed, by traceback, but ``K0``'s contract is that a read error
    arrives through the finding channel rather than as a stack trace, and a
    crash reports nothing about the other 1900 targets.

    A file holding one of the :data:`SENTINELS` is a ``K0`` failure too.  Those
    characters are what a masked-out region and a paragraph break *become*, and
    the claim that they appear in no source was a docstring nobody checked: a
    literal ``NUL`` written between ``for`` and a count made the count free.

    ``K4`` -- the ledger key really identifies a file -- is asserted here rather
    than believed, because the property it states is exactly the one the previous
    keying silently lacked (see :func:`display_name`).
    """
    wanted = tuple(paths) if paths is not None else tracked_paths(root)
    sources: list[Source] = []
    failures: list[str] = []
    for path in wanted:
        try:
            text = (root / path).read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError) as error:
            failures.append(f"K0 {path}: tracked but unreadable ({error})")
            continue
        if any(sentinel in text for sentinel in SENTINELS):
            failures.append(
                f"K0 {path}: holds a scanner sentinel control character, so the mask and "
                "the flattener cannot be trusted on it"
            )
            continue
        sources.append(
            Source(target=path, path=path, text=text, is_lean=path.endswith(".lean"))
        )
    if len(sources) + len(failures) != len(wanted):
        failures.append(
            f"K0: {len(wanted)} tracked target(s) but {len(sources)} read "
            f"and {len(failures)} failed"
        )
    failures.extend(key_failures(sources))
    return tuple(sources), tuple(failures)


def key_failures(sources: Iterable[Source]) -> list[str]:
    """Return the ``K4`` failures of a loaded source set: a key must name one file.

    Two properties, both of which the dotted-name keying lacked and neither of
    which any test could have caught by looking at today's corpus:

    * every target **inverts** to the path it was read from
      (:func:`target_path`), so a ledger row can be attributed to a file;
    * no two scanned files produce the **same** target, so a claim removed from
      one cannot be paid for by a claim written into the other.

    Fail closed: a collision suppresses the findings report exactly as ``K0``
    does, because a ledger whose keys are ambiguous is worse than no ledger.
    """
    failures: list[str] = []
    seen: dict[str, str] = {}
    for source in sources:
        if target_path(source.target) != source.path:
            failures.append(
                f"K4 {source.path}: its ledger key {source.target!r} does not invert to it"
            )
        first = seen.setdefault(source.target, source.path)
        if first != source.path:
            failures.append(
                f"K4 {source.target}: two tracked files share one ledger key "
                f"({first}, {source.path})"
            )
    return failures


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
# Every movement of this file that NO PROSE EDIT explains is on the record here,
# with its arithmetic.  All of them are detector corrections -- the tool was
# miscounting a population that was always there -- and in none of them was prose
# written or a claim repaired.  A repair campaign must never raise this file, and
# any future movement of this kind needs a public entry of exactly this shape.
#
#   713 -> 740   `NARROW_CHILD`'s anchor gained the `re.IGNORECASE` flag every
#                other anchor already carried; 27 lowercase occurrences became
#                visible to a detector that had been blind to them.
#   740 -> 1391  the `accounted` bucket was retired.  `RELOCATION` charges on its
#                anchor now, because "now lives in X" is itself the ownership
#                claim (+648, of which 647 were recognized and free); the scan
#                took in `IsingModel.lean`, `README.md` and the rest of `docs/`
#                (+2); and the clause window went from 70 to 200 characters (+1),
#                which also resolved 274 relocation subjects that had been pinned
#                only by their destination.
#  1391 -> 1390  a clause window may no longer cross a blank line.  At 200
#                characters three spans on this tree reached into the paragraph
#                above to borrow a count, and all three were wrong: two
#                RELOCATION subjects lose a number their sentence never stated
#                (`2->X` -> `->X`, merging into the coarse key already there) and
#                one PREDICATE_COUNT anchor -- a heading ending in the word
#                "bundles", counted from the next paragraph -- stops matching.
#  1390 -> 1402  a `NARROW_CHILD` count is read anywhere in its head clause and
#                not only at position 0, so one adjective no longer hides it
#                (`for the following 17 wrappers` produced no key at all).  12
#                headers that were reported as stating no size do state one; they
#                are charged `?N`, the `?` recording that the extractor does not
#                claim to know which noun the number counts.
#
# Multiset keyed (class, target, token): a key that is absent here, or present
# with a smaller count than the tree now holds, fails the gate.  One fix
# therefore cannot pay for one regression -- there is no scalar to offset.
#
# `target` is a repo-relative PATH and not the dotted module name it used to be.
# The dotted spelling is not injective -- `A/B.lean` and `A.B.lean` are two
# tracked files with one dotted name -- so a row could not be attributed to a
# file: rewording the claim in one of them while writing the same sentence into
# the other left this file byte-identical, with every gate green.  The re-key
# moved no charge (1391 before and after); it moved every row's second field.
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
# A recount under a corrected detector -- the 713 -> 740 shape above -- is the
# one movement no prose edit explains that can still be legitimate.  Declaring it
# takes a whole line of this file, added by the same diff, reading exactly
# `# DETECTOR-MIGRATION: <reason>`.  The declaration is a precondition and not an
# authorization: what it buys is computed, not granted.  BOTH detectors are run
# on a checkout of the BASE COMMIT and compared THERE, on prose that already
# existed.  Prose the diff writes is not in that tree, so widening the grammar
# and writing a claim in the newly recognized shape cannot pay for itself; and a
# key whose file this diff edits earns nothing at all.  A detector edit that
# changes no logic (comments, docstrings) buys nothing.
#
# The comparison relaxes B1 and B2 both, because a recall fix moves the pin in
# both directions at once: this token records a count as well as a destination,
# so teaching the grammar one more noun turns `->X` into `11->X` -- one row added
# and one removed for a sentence nobody edited.  Requiring a prose edit for that
# removal demanded an edit with nothing to write, and making it (to satisfy B2)
# forfeited the allowance that covered the addition; there was no third staging,
# so the grammar this file pins could not be corrected once pinned.  A row the
# new detector stops charging on the base tree is therefore explained -- but only
# inside a (class, target) group that gains at least as much as it loses, so
# "narrow the detector, drop rows, declare" remains a B2 failure.  B3 (the pin
# must be tight against the tree) is never waived by any of it.
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

#: The trailer that *declares* a detector migration.  Declaring is a
#: precondition, never an authorization: what a declaration can buy is computed
#: by :func:`migration_budgets`, key by key.  Four things must hold together
#: (:func:`check_drift`), and each exists because the hatch as previously
#: written was satisfied without it:
#:
#: 1. the trailer is *added by this diff* to the pinned file, as a whole line
#:    (:data:`_MIGRATION_LINE`) -- not a marker already on the base branch, and
#:    not a marker buried in a longer comment;
#: 2. the detector's **logic** changed (:func:`detector_logic_changed`) -- an AST
#:    comparison, so appending ``# cosmetic`` to the detector buys nothing;
#: 3. the movement is one the two detectors disagree about **on the base
#:    commit's own tree**.  Prose this diff writes is not in that tree, so no
#:    claim the diff adds can be paid for by widening the grammar that
#:    recognizes it.  A key the new detector gains there relaxes ``B1``; a key
#:    it loses there relaxes ``B2``, and only inside a ``(class, target)`` group
#:    that does not shrink (:func:`migration_delta`);
#: 4. the key's source file is not one this diff edits at all.
#:
#: Two measured exploits this replaces.  Two new inventory claims +
#: ``--baseline`` + one comment line in the pinned file + one comment line in the
#: detector made ``--check-baseline-drift`` print ``PASS``, because the waiver
#: was granted on the *path* of the detector and applied to every ``B1``/``B2``
#: failure in the run.  Then, with the waiver replaced by a recount taken on the
#: *head* tree: add ``aggregates`` to the predicate anchor, write ``This module
#: aggregates seventeen lemmas`` in the same diff, declare -- and the claim paid
#: for itself, because the base detector could not see the new prose either.
MIGRATION_MARKER = "# DETECTOR-MIGRATION:"

#: The declaration's whole grammar: the marker, one space, a non-empty reason,
#: and nothing else on the line.
_MIGRATION_LINE = re.compile(rf"\A{re.escape(MIGRATION_MARKER)} (?P<reason>\S.*)\Z")


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
    """Return the repo-relative paths that differ between ``commit`` and the tree.

    ``--no-renames`` is load-bearing.  With rename detection on, ``git diff
    --name-only`` prints a rename as its *destination* only, so the old path is
    invisible -- and this repository's dominant workflow is exactly module splits
    and ``git mv``.  A claim deleted from ``A.lean`` in the same commit that
    renames it to ``B.lean`` then looked to ``B2`` like a baseline row deleted
    with no edit to the file that owned it, i.e. a legitimate repair was rejected
    and the only way past it was the migration hatch.  Renames are therefore
    reported as delete + add, which is what ``B2`` needs to attribute a row.
    """
    code, out = _git(root, "diff", "--no-renames", "--name-only", commit, "--")
    if code != 0:
        return frozenset()
    return frozenset(line.strip() for line in out.splitlines() if line.strip())


def migration_declarations(root: Path, commit: str) -> tuple[str, ...]:
    """Return the migration reasons this diff *adds* to the baseline file.

    The line has to be the whole line -- :data:`_MIGRATION_LINE`, marker, one
    space, a non-empty reason -- and it has to be added by this diff, so a marker
    already on the base branch is not a standing permission.  Declaring is
    necessary and nowhere near sufficient: what a declaration buys is bounded by
    :func:`detector_recount`, which measures the effect of the detector change
    instead of believing the sentence.
    """
    code, out = _git(root, "diff", "--no-renames", "-U0", commit, "--", BASELINE_REPO_PATH)
    if code != 0:
        return ()
    reasons = []
    for line in out.splitlines():
        if not line.startswith("+") or line.startswith("+++"):
            continue
        declaration = _MIGRATION_LINE.match(line[1:])
        if declaration is not None:
            reasons.append(declaration.group("reason").strip())
    return tuple(reasons)


def _logic_fingerprint(text: str) -> str | None:
    """Return a normalized fingerprint of Python ``text``, or ``None`` if unparseable.

    The abstract syntax tree with docstrings removed and positions discarded:
    comments never reach it, reflowing a line does not change it, and rewriting a
    docstring does not either.  What does change it is an edit to the code that
    decides what gets charged -- a pattern, a table, a branch -- which is the only
    kind of edit that can make a recount legitimate.
    """
    try:
        tree = ast.parse(text)
    except SyntaxError:
        return None
    for node in ast.walk(tree):
        if not isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        first = node.body[0] if node.body else None
        if (
            isinstance(first, ast.Expr)
            and isinstance(first.value, ast.Constant)
            and isinstance(first.value.value, str)
        ):
            node.body = node.body[1:] or [ast.Pass()]
    return ast.dump(tree)


def detector_logic_changed(root: Path, commit: str) -> bool:
    """Whether the detector's *logic* differs between ``commit`` and this tree.

    Comment-only and docstring-only edits do not count, which is the point: the
    hatch as first written asked only whether the detector *file* appeared in the
    diff, so appending ``# cosmetic`` to it bought a waiver.
    """
    code, before = _git(root, "show", f"{commit}:{DETECTOR_REPO_PATH}")
    if code != 0:
        return False
    try:
        after = (root / DETECTOR_REPO_PATH).read_text(encoding="utf-8")
    except OSError:
        return False
    base_fingerprint = _logic_fingerprint(before)
    head_fingerprint = _logic_fingerprint(after)
    if base_fingerprint is None or head_fingerprint is None:
        return False
    return base_fingerprint != head_fingerprint


@contextlib.contextmanager
def base_worktree(root: Path, commit: str) -> Iterator[Path | None]:
    """Yield a checkout of ``commit``, or ``None`` if one cannot be made.

    A linked ``git worktree``, not an archive: the scan's target set comes from
    ``git ls-files``, so the base tree has to *be* a repository rather than a
    directory of files.  Removed on the way out, including after an exception,
    so a failed run leaves no registration behind.
    """
    parent = tempfile.mkdtemp(prefix="claim-ratchet-base-")
    tree = Path(parent) / "tree"
    code, _out = _git(root, "worktree", "add", "--detach", "--quiet", str(tree), commit)
    try:
        yield tree if code == 0 else None
    finally:
        if code == 0:
            _git(root, "worktree", "remove", "--force", str(tree))
        shutil.rmtree(parent, ignore_errors=True)
        _git(root, "worktree", "prune")


def detector_charges(root: Path, commit: str, tree: Path) -> Counter[tuple[str, str, str]] | None:
    """Return what the detector *at* ``commit`` charges on ``tree``.

    ``None`` -- which means no allowance at all -- when the base detector cannot
    be obtained, executed, or trusted (an unsound run of it says nothing).

    It really does execute the base commit's copy of this file, and only when a
    migration is declared.  That code is this repository's own, already reviewed
    and already what CI runs on ``main``; the alternative -- believing the
    declaration -- is what the total waiver did.
    """
    code, text = _git(root, "show", f"{commit}:{DETECTOR_REPO_PATH}")
    if code != 0:
        return None
    module = types.ModuleType("header_inventory_claim_ratchet_base")
    module.__dict__["__file__"] = str(root / DETECTOR_REPO_PATH)
    try:
        exec(compile(text, f"<{commit[:12]}:{DETECTOR_REPO_PATH}>", "exec"), module.__dict__)  # noqa: S102
        report = module.build_report(tree)
        if not report.sound:
            return None
        return Counter(report.charged)
    except Exception:  # noqa: BLE001 -- any failure of a foreign build is "no allowance"
        return None


def own_charges(tree: Path) -> Counter[tuple[str, str, str]] | None:
    """Return what *this* detector charges on ``tree``, or ``None`` if unsound."""
    try:
        report = build_report(tree)
    except (OSError, subprocess.SubprocessError):
        return None
    return Counter(report.charged) if report.sound else None


def target_path(target: str) -> str:
    """Return the repo-relative source path a ratchet target names.

    The identity, and deliberately so: the ledger is keyed by the path itself,
    because every derived name this could invert is a place two files collapse
    into one key.  It stays a named function because ``B2`` and the migration
    budgets ask "which file does this key name?" of rows read out of a *file*
    rather than out of a scan, and because ``K4`` asserts the round trip rather
    than assuming it.
    """
    return target


class Drift(NamedTuple):
    """The verdict of comparing this checkout's pin against the base branch's."""

    base: str
    had_baseline: bool
    added: tuple[tuple[tuple[str, str, str], int, int], ...]
    unexplained: tuple[tuple[tuple[str, str, str], int, int], ...]
    untight: tuple[tuple[str, str, str], ...]
    unsound: tuple[str, ...]
    baseline_errors: tuple[str, ...]
    migration: tuple[str, ...]

    @property
    def ok(self) -> bool:
        """Whether the pin moved only in ways this diff explains.

        One policy, evaluated once: a declared migration is already accounted for
        in :attr:`added` and :attr:`unexplained` (it *narrows* what counts as a
        rise and what counts as an unexplained fall, key by key), so there is no
        second, permissive rule here for :func:`print_drift` to duplicate and
        drift away from.
        """
        return not (
            self.unsound or self.baseline_errors or self.untight
            or self.added or self.unexplained
        )


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
    the file that owned it, *or* in a measured recount
    (:func:`migration_budgets`): a row that vanishes because the **detector**
    stopped producing that key on the base commit's own tree was not repaired by
    anybody, so demanding a prose edit for it is demanding an edit that has
    nothing to write.

    A key carried into a *renamed* module is a new key by the ratchet's own
    definition and fails ``B1``.  What repairs it depends on the class, and the
    difference is worth stating because the obvious move only works for one of
    them: a ``NARROW_CHILD`` count can be dropped in place (``for the 12 foo
    wrappers`` -> ``for the foo wrappers`` states no size, so it produces no key
    at all), while a ``RELOCATION`` cannot -- ``The three wrappers now live in
    `X` `` -> ``The wrappers now live in `X` `` re-keys ``3->X`` to ``->X``,
    which is a new key and a ``B1`` failure, because the ownership claim is
    exactly what that class charges.  The repair there is to delete the
    relocation sentence, which is what the campaign is for.

    All three run only on a **sound** run of a **parseable** pair of pins.  A
    conservation failure or a malformed baseline suppresses the comparison here
    exactly as it suppresses the findings report in every other output format --
    this mode used to report ``PASS`` on a tree whose ``--check`` was failing.

    Returns ``None`` when ``base_ref`` does not resolve -- fail closed, never a
    silent pass.
    """
    base = base_commit(root, base_ref)
    if base is None:
        return None
    baseline, base_errors = baseline_at(root, base)
    head, head_errors = read_baseline(root / BASELINE_REPO_PATH)
    report = build_report(root)
    errors = tuple(
        [f"the base branch's pin: {message}" for message in base_errors]
        + [f"this checkout's pin: {message}" for message in head_errors]
    )
    if not report.sound or errors:
        return Drift(base, baseline is not None, (), (), (), report.conservation, errors, ())
    live = report.charged
    untight = tuple(sorted(key for key in set(head) | set(live) if head.get(key) != live.get(key)))
    if baseline is None:
        return Drift(base, False, (), (), untight, (), (), ())
    edited = changed_paths(root, base)
    migration = migration_budgets(root, base, live)
    added = tuple(
        sorted(
            (key, count, baseline.get(key, 0))
            for key, count in head.items()
            if count > baseline.get(key, 0) + migration.allowance.get(key, 0)
        )
    )
    unexplained = tuple(
        sorted(
            (key, head.get(key, 0), count)
            for key, count in baseline.items()
            if head.get(key, 0) < count
            and target_path(key[1]) not in edited
            and count - head.get(key, 0) > migration.relief.get(key, 0)
        )
    )
    return Drift(base, True, added, unexplained, untight, (), (), migration.narrative)


class Migration(NamedTuple):
    """What a declared detector migration buys -- computed, never granted.

    Two per-key budgets rather than one, because a detector change moves the pin
    in two directions at once and only one of them used to be payable:

    ``allowance``
        keys this detector charges on the base commit's tree that the base
        detector did not.  It relaxes ``B1``.

    ``relief``
        keys the base detector charged there that this one no longer does.  It
        relaxes ``B2``, and only within a ``(class, target)`` group the change
        does not shrink (see :func:`migration_delta`).

    ``narrative``
        what to print, including the arithmetic both budgets came from.
    """

    allowance: Counter[tuple[str, str, str]]
    relief: Counter[tuple[str, str, str]]
    narrative: tuple[str, ...]


def migration_delta(
    before: Counter[tuple[str, str, str]],
    after: Counter[tuple[str, str, str]],
    edited: frozenset[str],
) -> tuple[Counter[tuple[str, str, str]], Counter[tuple[str, str, str]]]:
    """Split a base-tree detector delta into a ``B1`` allowance and a ``B2`` relief.

    Both arguments are measured on the **same** tree -- the base commit's -- so
    every difference between them is a fact about the detector and never about
    the prose.  ``edited`` zeroes both budgets for any key whose source this diff
    touches, so a migration must be landed in a diff that leaves the scanned
    corpus alone.

    The relief exists because ``B1`` and ``B2`` were otherwise **mutually
    exclusive** for the modal detector improvement in this design.  A recall fix
    -- the detector recognizes prose that was always there -- does not only add
    rows: where the newly recognized part is a *sharpener* of an existing key it
    also removes one, because ``RELOCATION``'s token is ``<count>-><destination>``
    with the count optional.  Teaching the grammar one more inventory noun turns
    ``->X`` into ``11->X``: an addition ``B1`` covers and a removal ``B2`` did
    not, and the only apparent escape -- also touching the files ``B2`` names --
    zeroes the allowance and turns the additions back into ``B1`` failures.  Both
    stagings failed; there was no third.  Since 303 of the 692 pinned
    ``RELOCATION`` keys are still the unresolved ``->X`` shape, that was not a
    corner case but the next change, and a pin nobody can correct is a pin that
    freezes its own token grammar.

    What the relief must **not** become is a channel for narrowing the detector
    to launder rows off the pin.  The guard is per ``(class, target)`` group: a
    removal is relieved only where the same group gains at least as much as it
    loses, i.e. where the change re-keys rather than reduces.  Equivalently --
    the two statements are the same arithmetic -- the relief a group may draw can
    never exceed what that group's additions cost, so the population per file and
    class is non-decreasing across a migration.  A change that genuinely stops
    recognizing something still fails ``B2`` and still needs a reviewed decision.
    """
    keys = set(before) | set(after)
    gained = Counter(
        {key: after[key] - before.get(key, 0) for key in keys if after.get(key, 0)
         > before.get(key, 0)}
    )
    lost = Counter(
        {key: before[key] - after.get(key, 0) for key in keys if before.get(key, 0)
         > after.get(key, 0)}
    )
    gained_by_group: Counter[tuple[str, str]] = Counter()
    lost_by_group: Counter[tuple[str, str]] = Counter()
    for key, count in gained.items():
        gained_by_group[key[:2]] += count
    for key, count in lost.items():
        lost_by_group[key[:2]] += count
    allowance = Counter(
        {key: count for key, count in gained.items() if target_path(key[1]) not in edited}
    )
    relief = Counter(
        {
            key: count for key, count in lost.items()
            if target_path(key[1]) not in edited
            and lost_by_group[key[:2]] <= gained_by_group[key[:2]]
        }
    )
    return allowance, relief


def migration_budgets(
    root: Path, commit: str, live: Counter[tuple[str, str, str]]
) -> Migration:
    """Return the :class:`Migration` budgets for a declared detector migration.

    Both budgets are pure functions of *the detector delta applied to prose that
    already existed*: both detectors are run on a checkout of the **base
    commit**, and the delta is taken there.  Prose the diff writes is not in that
    tree at all, so it can never earn anything -- which is the property the
    version before this one lacked.

    That version ran both detectors on the **head** tree, and reasoned that a
    new claim is "visible to both detectors, so it cancels".  It does not cancel
    when the diff widens the grammar and writes prose in the newly recognized
    shape at the same time: adding ``aggregates`` to the predicate anchor *and*
    writing ``This module aggregates seventeen lemmas`` gave base 740, head 741,
    allowance 1 -- the new claim paid for itself.  That is the whole shape a
    migration hatch has to refuse, because a genuine grammar-widening PR that
    also edits headers is this repository's own normal workflow.

    Two rules, and the distinction they draw is the point:

    * the detector got smarter about **existing** prose -- the same characters
      were in the base tree and only the new detector sees them -- which is a
      legitimate recount and is what these budgets cover;
    * the diff added **new** prose that the new logic covers, which is a claim
      somebody wrote and is charged like any other.

    On top of that, no key whose source file this diff touches earns anything
    (``target_path(key[1]) in changed_paths``).  Belt and braces: the base-tree
    measurement already excludes new prose, and this excludes edited prose too,
    so a migration must be declared in a diff that leaves the scanned corpus
    alone.  That is a real constraint on how a migration is landed, and it is
    the constraint the ``713 -> 740`` migration already met.

    Empty unless a declaration was added by this diff *and* the detector's logic
    really changed *and* the base tree can be materialized and both detectors
    run soundly on it.  ``B3`` (the pin must be tight against the live tree) is
    never waived by any of this, so no detector edit can buy slack in the pin.
    """
    reasons = migration_declarations(root, commit)
    if not reasons:
        return Migration(Counter(), Counter(), ())
    declared = tuple(f"declared: {reason}" for reason in reasons)
    if not detector_logic_changed(root, commit):
        return Migration(Counter(), Counter(), declared + (
            "no allowance: the detector's logic is unchanged since the base commit "
            "(a comment- or docstring-only edit is not a migration)",
        ))
    with base_worktree(root, commit) as tree:
        if tree is None:
            return Migration(Counter(), Counter(), declared + (
                "no allowance: the base commit's tree could not be checked out, so the "
                "detector delta cannot be measured on prose that predates this diff",
            ))
        before = detector_charges(root, commit, tree)
        after = own_charges(tree)
    if before is None or after is None:
        return Migration(Counter(), Counter(), declared + (
            "no allowance: one of the two detectors did not produce a sound run on the "
            "base commit's tree",
        ))
    allowance, relief = migration_delta(before, after, changed_paths(root, commit))
    return Migration(allowance, relief, declared + (
        f"allowance: on the base commit's own tree the base detector charges "
        f"{sum(before.values())} and this one charges {sum(after.values())}; "
        f"{sum(allowance.values())} charge(s) over {len(allowance)} key(s) in files this diff "
        f"does not touch are attributable to the detector change, and only those "
        f"(this tree charges {sum(live.values())})",
        f"relief: {sum(relief.values())} charge(s) over {len(relief)} key(s) that the base "
        f"detector charged there and this one no longer does, in groups the change re-keys "
        f"rather than shrinks; those rows may leave the pin without a prose edit",
    ))


def print_drift(drift: Drift | None, base_ref: str) -> bool:
    """Print the drift verdict; return :attr:`Drift.ok`.

    Reporting only: the verdict is :attr:`Drift.ok` and is not recomputed here.
    It used to be, with a permissive branch of its own, so the property the tests
    asserted and the policy production applied were two implementations of one
    rule that nothing checked for agreement.
    """
    print("== Baseline drift (this checkout's pin vs the base branch's) ==")
    if drift is None:
        print(f"  FAIL: base ref {base_ref!r} does not resolve in this checkout")
        print("        (CI needs `fetch-depth: 0`, so that origin/main is present)")
        print("FAIL: the pin could not be compared against the base branch")
        return False
    print(f"  base commit {drift.base[:12]} via {base_ref}")
    for failure in drift.unsound:
        print(f"  FAIL: conservation broken: {failure}")
    for message in drift.baseline_errors:
        print(f"  FAIL: malformed baseline: {message}")
    if drift.unsound or drift.baseline_errors:
        print("  (the drift comparison is suppressed: a run that cannot account for its own "
              "inputs reports nothing rather than something reassuring)")
        print("FAIL: the pin could not be compared against the base branch")
        return False
    for key in drift.untight:
        print(f"  FAIL: B3 pin not tight -- re-pin with --baseline: {key[0]} {key[1]} {key[2]}")
    for key, count, was in drift.added:
        print(f"  FAIL: B1 pin rose {was} -> {count}: {key[0]} {key[1]} {key[2]}")
    for key, count, was in drift.unexplained:
        print(f"  FAIL: B2 pin fell {was} -> {count} with no edit to {target_path(key[1])} "
              f"and no recount to explain it: {key[0]} {key[1]} {key[2]}")
    for note in drift.migration:
        print(f"  INFO: detector migration -- {note}")
    if not drift.had_baseline:
        print("  INFO: the base commit carries no baseline file; this is its first landing, "
              "so B1/B2 have nothing to compare against")
    print("PASS: the pin moved only where this diff explains it"
          if drift.ok else "FAIL: the pin moved in a way this diff does not explain")
    return drift.ok


# --------------------------------------------------------------------------
# The run
# --------------------------------------------------------------------------


class Report(NamedTuple):
    """The verdict of one ratchet run.

    ``claims`` is the ledger the ratchet is computed from and every row in it is
    charged.  ``telemetry`` is a coverage report -- recognized anchors that state
    no inventory size -- and it is deliberately **not** part of the population:
    it is never pinned, never compared, and never a reason to pass or fail.  It
    used to live inside ``claims`` behind a ``charged=False`` flag, which is how
    647 relocation claims came to be reported as recognized and cost nothing.
    """

    sources: tuple[Source, ...]
    claims: tuple[Claim, ...]
    telemetry: tuple[Claim, ...]
    conservation: tuple[str, ...]

    @property
    def charged(self) -> Counter[tuple[str, str, str]]:
        """The charged-claim multiset, i.e. the ratchet population."""
        return Counter(claim.key for claim in self.claims)

    @property
    def sound(self) -> bool:
        """Whether ``K0``/``K1``/``K2``/``K3`` all held on this run."""
        return not self.conservation


def build_report(root: Path = REPO_ROOT, paths: Iterable[str] | None = None) -> Report:
    """Scan every tracked target and return the run's verdict."""
    sources, failures = load_sources(root, paths)
    claims: list[Claim] = []
    telemetry: list[Claim] = []
    conservation = list(failures)
    for source in sources:
        scanned = scan_source(source)
        claims.extend(scanned.claims)
        telemetry.extend(scanned.telemetry)
        conservation.extend(scanned.conservation)
    return Report(
        sources=sources,
        claims=tuple(claims),
        telemetry=tuple(telemetry),
        conservation=tuple(conservation),
    )


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

    print("== Conservation (K0 inputs / K1 records / K2 mask / K3 oracle / K4 key identity) ==")
    if report.sound:
        print("  PASS: every tracked target accounted for; "
              "raw anchors == records == masked anchors; regions == oracle; "
              "one key names one file")
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
        tracked = sum(1 for claim in report.telemetry if claim.kind == claim_class.name)
        print(f"  {claim_class.name} [{claim_class.referent}]: {charged} charged"
              f"{f' (+{tracked} telemetry)' if tracked else ''} -- {claim_class.summary}")
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


TELEMETRY_LINES = (
    "TELEMETRY (NON-AUTHORITATIVE): the rows below are recognized anchors that state",
    "no inventory size -- a purpose-only `Narrow child module for ...` header.  They",
    "are NOT part of the population, are never pinned, and no verdict is computed from",
    "them.  They are printed so that the detector's coverage stays visible, and they",
    "are kept out of the ledger above because a `charged=False` row inside a ledger is",
    "somewhere for a real charge to be filed as free.",
)


def format_findings(report: Report) -> str:
    """Render every finding as TSV (suppressed unless the run is sound).

    Two tables, not one column: the ledger first, then the telemetry under its
    own banner and its own header row.

    ``module`` is :func:`display_name` -- the dotted spelling a Lean reader
    wants, carried as a column of its own and never as the key.  A lossy display
    string that doubles as an identity is what let two files share one ledger
    row, so it is emitted beside ``target`` rather than instead of it.
    """
    def order(claim: Claim) -> tuple[str, int, str, str]:
        """Sort key: by target, then by where in it the record was found."""
        return (claim.target, claim.line, claim.kind, claim.token)

    def row(claim: Claim) -> str:
        """Render one record: key first, display name second."""
        return (
            f"{claim.kind}\t{claim.target}\t{display_name(claim.target)}\t"
            f"{claim.token}\t{claim.line}\t{claim.note}"
        )

    lines = ["# " + line for line in CONTRACT_LINES]
    lines.append("class\ttarget\tmodule\ttoken\tline\tnote")
    lines.extend(row(claim) for claim in sorted(report.claims, key=order))
    lines.append("")
    lines.extend("# " + line for line in TELEMETRY_LINES)
    lines.append("telemetry-class\ttarget\tmodule\ttoken\tline\tnote")
    lines.extend(row(claim) for claim in sorted(report.telemetry, key=order))
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
