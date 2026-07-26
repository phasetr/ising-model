#!/usr/bin/env python3
"""Tests for ``scripts/citation_audit.py``.

Run directly (``python3 scripts/test_citation_audit.py``) or through the tool's
own ``--self-test`` flag.

Why this suite is shaped the way it is
--------------------------------------
The checker's whole value is that it refuses to exonerate a citation it has not
positively resolved. A test that only asserts "the current tree passes" would
stay green through exactly the edit that destroys that value -- a regex relaxed
to silence a false positive, a suffix test loosened to ``endswith``, a tag
consulted "just this once", the resolution set widened from git to the
filesystem. Those four are not hypothetical: they are the four recurrences that
sank the previous attempt (PR #4714).

So every check is tested in two directions, the idiom of
``scripts/test_audit_gate.py``:

1. **Fixture direction** -- a hand-built document plus a hand-built tracked set,
   with a known verdict, so the check is pinned against material independent of
   this repository's current state.
2. **Mutation direction** (:class:`MutationTest`) -- ``citation_audit.py``'s
   source is re-loaded with one surgical weakening applied and the mutant is
   required to *miss* what the real checker catches. Each mutation is the edit a
   developer would plausibly make, and :func:`load_mutated` raises when its
   target no longer matches exactly once, so a mutation cannot quietly become
   vacuous after the code moves.

The fixture/mutation pairs cover the known ways a ``.lean`` citation scan has
silently missed something, or has silently exonerated something: brace
shorthand, verbatim source line wraps, bare prose tokens, archive-tag
exoneration, basename-only citations, multiple suffix matches, ``\\_`` escapes,
the coverage audit itself, resolution against untracked or benchmark copies, the
anti-vacuity floors, self-reference detection, the multiset ratchet, path text
glued to a match (``../X/Y.lean``, ``X/Y.lean.bak``), an indented tree entry
joined onto the heading above it, a census published from a provably incomplete
run, a baseline rewritten from a partial target set, a baseline rewritten
upwards, and a document remediated by deleting the citing prose.

Three kinds of pin, and what each is allowed to depend on
--------------------------------------------------------
An earlier version of this suite pinned the per-class census of the **live**
documents against the committed baseline. The intent was to notice a silent
change in the *extractor* -- the one change the ratchet cannot see, because a
relaxed resolution rule clears findings and so looks exactly like remediation --
but the input was wrong: with mutable documents that assertion also says the
documents did not change, so it failed on every remediation commit. It has been
replaced by pins that keep the intent and drop the accidental document freeze:

1. **live, remediation-invariant** (:class:`RealTreePinTest`): identities that
   hold whatever the documents say -- the classes partition the citations, the
   rows aggregate to the classes, ``matched + acknowledged == raw``.
2. **frozen corpus** (:class:`FrozenCorpusTest`): the extractor's verdict on
   ``scripts/audit/citation_corpus/``, a committed document pair with a committed
   resolution set and a committed expected census. It moves iff the extractor
   moves, and never when a live document is edited.
3. **committed constants** (:class:`RealTreePinTest` again): the floors and the
   deletion budget, expressed against the committed census rather than the live
   run, so that "the floor is not zero" stays checked while the check itself
   stops drifting with the documents.

One class of test is here because the capability it guarded was **deleted**.
The checker used to honour a ``citation-audit:`` comment directive, and three
successive rounds of tests pinned one more spelling in which a *quotation* of
that syntax armed a real exemption. The directive channel is gone (see the
tool's "Why there is no exemption channel"), so those tests were not deleted
with it but inverted: :class:`NoExemptionChannelTest` keeps every one of those
documents -- the earnest spellings and the quoted ones alike -- and requires
each to receive the ordinary verdict. A corpus of directive-shaped text that
provably does nothing is what detects the channel growing back.

Cost: fixtures build throwaway git repositories (the resolution set really is
``git ls-files``, so stubbing it away would test the wrong thing), plus one
shared pass over the two live targets, cached in :func:`live_report`.

Note on this file's own text: ``audit_gate.py`` V4 scans ``scripts/`` for
Japanese, and this suite needs non-ASCII samples, so they are built with
``chr()`` rather than written literally -- the same rule
``test_audit_gate.py`` states in its docstring.
"""

from __future__ import annotations

import io
import subprocess
import sys
import tempfile
import types
import unittest
from collections import Counter
from contextlib import contextmanager, redirect_stdout
from pathlib import Path
from typing import Dict, Iterator, List, Optional, Sequence

sys.path.insert(0, str(Path(__file__).resolve().parent))

import citation_audit as ca  # noqa: E402  (path bootstrap first)

CITATION_AUDIT_PATH = Path(ca.__file__).resolve()

# Non-ASCII samples, built from codepoints (see the module docstring).
LEFT_GUILLEMET = chr(0x00AB)  # U+00AB
RIGHT_GUILLEMET = chr(0x00BB)  # U+00BB

_LIVE: Optional[ca.Report] = None


def live_report() -> ca.Report:
    """Return one audit of the real targets, computed at most once."""
    global _LIVE
    if _LIVE is None:
        _LIVE = ca.audit()
    return _LIVE


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


@contextmanager
def patched(module: types.ModuleType, **attrs: object) -> Iterator[None]:
    """Temporarily set module attributes, restoring the originals afterwards."""
    saved = {name: getattr(module, name) for name in attrs}
    for name, value in attrs.items():
        setattr(module, name, value)
    try:
        yield
    finally:
        for name, value in saved.items():
            setattr(module, name, value)


def _run_git(root: Path, *args: str) -> None:
    """Run a git command in ``root``, failing loudly."""
    subprocess.run(["git", *args], cwd=str(root), check=True, capture_output=True)


def _staged_paths(root: Path) -> List[str]:
    """Return the paths in ``root``'s index, sorted."""
    out = subprocess.run(
        ["git", "ls-files", "-z"],
        cwd=str(root),
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    return sorted(path for path in out.split("\0") if path)


@contextmanager
def fixture(
    documents: Dict[str, str],
    tracked: Sequence[str] = (),
    untracked: Sequence[str] = (),
    tags: Optional[Dict[str, Sequence[str]]] = None,
    module: Optional[types.ModuleType] = None,
    commit: bool = False,
    **overrides: object,
) -> Iterator[Path]:
    """Build a throwaway repository and point the checker at it.

    ``documents`` maps a repository-relative path to its text; ``tracked`` lists
    ``.lean`` paths that are staged (and therefore resolvable); ``untracked``
    lists ``.lean`` paths written to disk but never staged, which is how "the
    filesystem is not the resolution set" is tested; ``tags`` maps a tag name to
    the ``.lean`` paths that exist *only* in that tag. ``commit`` commits the
    staged files, which is what the baseline-update tests need: the copy an
    update is judged against is the one in a *commit*, so without one there is
    nothing to judge against.

    Staging uses ``git add -f`` with the paths named explicitly, and the
    resulting index is compared against them: a developer's global ignore file
    must not be able to silently drop a fixture path and leave the test
    asserting nothing (measured -- a global ``.gitignore`` entry for
    ``.self-local`` did exactly that to the contamination fixtures below), and a
    fixture whose resolution set is not the one it asked for must fail *as a
    fixture*. Review observed one run in which a two-file fixture behaved as if
    only one file were tracked and the verdicts changed accordingly; it has not
    reproduced (960 stress builds under parallel load), so the remedy here is
    not a fix but a tripwire: whatever caused it, the next occurrence names
    itself instead of quietly changing a verdict.

    ``MIN_TRACKED_LEAN`` is lowered to 1 for the duration: these fixtures pin the
    *decision logic* with a handful of files, and the real floor is a separate
    claim about the repository, asserted against the real tree in
    :class:`RealTreePinTest`.
    """
    target = module if module is not None else ca
    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        _run_git(root, "init", "-q")
        if tags:
            for tag, paths in tags.items():
                for name in paths:
                    path = root / name
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text("-- archived\n", encoding="utf-8")
                _run_git(root, "add", "-A", "-f", "--", *paths)
                _run_git(
                    root,
                    "-c",
                    "user.email=test@example.com",
                    "-c",
                    "user.name=test",
                    "commit",
                    "-q",
                    "-m",
                    "archived",
                )
                _run_git(root, "tag", tag)
                for name in paths:
                    (root / name).unlink()
                _run_git(root, "add", "-A", "-f", "--", *paths)
        for name, text in documents.items():
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding="utf-8")
        for name in tracked:
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("-- stub\n", encoding="utf-8")
        wanted = sorted(set(documents) | set(tracked))
        if wanted:
            _run_git(root, "add", "-f", "--", *wanted)
        staged = _staged_paths(root)
        if staged != wanted:
            raise AssertionError(
                f"fixture staged {staged}, expected {wanted}: the resolution set is not "
                "the one this test asked for, so its verdicts would be meaningless"
            )
        if commit:
            _run_git(
                root,
                "-c",
                "user.email=test@example.com",
                "-c",
                "user.name=test",
                "commit",
                "-q",
                "-m",
                "fixture",
            )
        for name in untracked:
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("-- untracked\n", encoding="utf-8")
        settings: Dict[str, object] = {"REPO_ROOT": root, "MIN_TRACKED_LEAN": 1}
        settings.update(overrides)
        with patched(target, **settings):
            yield root


def classes(report: ca.Report, target: str) -> Dict[str, int]:
    """Return the non-zero class census of one target."""
    return {name: count for name, count in report.counts[target].items() if count}


def tokens_of(report: ca.Report, cls: str) -> List[str]:
    """Return the tokens reported under ``cls`` (findings and advisories)."""
    return [
        finding.token
        for finding in list(report.findings) + list(report.selfrefs)
        if finding.cls == cls
    ]


def load_mutated(*substitutions: Sequence[str]) -> types.ModuleType:
    """Return ``citation_audit`` re-imported with textual weakenings applied.

    Each substitution must match exactly once; one that stops matching means the
    code it targeted moved and the mutation test using it has become vacuous, so
    this raises instead of silently applying nothing. ``__file__`` keeps pointing
    at the real script, so ``REPO_ROOT`` resolves exactly as in production.
    """
    source = CITATION_AUDIT_PATH.read_text(encoding="utf-8")
    for old, new in substitutions:
        count = source.count(old)
        if count != 1:
            raise AssertionError(f"mutation target matched {count} times, expected 1: {old!r}")
        source = source.replace(old, new)
    module = types.ModuleType("citation_audit_mutant")
    module.__file__ = str(CITATION_AUDIT_PATH)
    exec(compile(source, str(CITATION_AUDIT_PATH), "exec"), module.__dict__)  # noqa: S102
    return module


def run_main(module: types.ModuleType, *argv: str) -> Sequence[object]:
    """Run ``module.main(argv)``; return ``(exit code, stdout)``."""
    buffer = io.StringIO()
    with redirect_stdout(buffer):
        code = module.main(list(argv))
    return (code, buffer.getvalue())


# ---------------------------------------------------------------------------
# The frozen corpus (see FrozenCorpusTest)
# ---------------------------------------------------------------------------

CORPUS_DIR = CITATION_AUDIT_PATH.parent / "audit" / "citation_corpus"

# The order matters: the census lines are rendered in visited order, and the
# expectation is compared line by line.
CORPUS_TARGETS = ("tex/guide.tex", "docs/notes.md")


def corpus_documents() -> Dict[str, str]:
    """Return the frozen corpus documents, keyed by their in-fixture path."""
    return {
        "tex/guide.tex": (CORPUS_DIR / "guide.tex").read_text(encoding="utf-8"),
        "docs/notes.md": (CORPUS_DIR / "notes.md").read_text(encoding="utf-8"),
    }


def corpus_tracked() -> List[str]:
    """Return the frozen resolution set the corpus is judged against."""
    return [
        line.strip()
        for line in (CORPUS_DIR / "tracked.txt").read_text(encoding="utf-8").split("\n")
        if line.strip() and not line.startswith("#")
    ]


def corpus_report(module: Optional[types.ModuleType] = None) -> ca.Report:
    """Audit the frozen corpus in a throwaway repository built from it."""
    target = module if module is not None else ca
    with fixture(corpus_documents(), tracked=corpus_tracked(), module=target):
        return target.audit(list(CORPUS_TARGETS))


def baseline_body(text: str) -> List[str]:
    """Return a baseline's machine-readable lines, dropping free-text comments.

    The prose header explains the file to a reader and is allowed to be reworded
    without invalidating an expectation; ``#tracked``, ``#census``, ``#!`` and the
    rows are the content, and they are compared exactly.
    """
    return [
        line
        for line in text.split("\n")
        if line.strip()
        and (not line.startswith("#") or line.startswith(("#tracked", "#census", "#!")))
    ]


def make_baseline(
    tracked: int,
    census: Sequence[Sequence[object]],
    rows: Sequence[Sequence[object]],
) -> str:
    """Render a baseline file by hand, for tests that need a *committed* one.

    Written out rather than produced by ``--update-baseline`` so that what a
    refusal is judged against is visible in the test that asserts the refusal.
    """
    lines = ["# hand-built fixture baseline", f"#tracked\t{tracked}"]
    for target, citations, raw, classes in census:
        lines.append(f"#census\t{target}\t{citations}\t{raw}\t{classes}")
    lines.append("class\ttarget\ttoken\tcount\tfirst_line")
    for cls, target, token, count in rows:
        lines.append(f"{cls}\t{target}\t{token}\t{count}\t1")
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# Primitives
# ---------------------------------------------------------------------------


class PrimitiveTest(unittest.TestCase):
    """The pure helpers every verdict is built from."""

    def test_suffix_map_is_component_aligned(self) -> None:
        """``Ball/Real.lean`` must not be answered by ``.../SmallBall/Real.lean``."""
        table = ca.suffix_map(["X/Y/SmallBall/Real.lean"])
        self.assertEqual(table.get("Ball/Real.lean", set()), set())
        self.assertEqual(len(table["SmallBall/Real.lean"]), 1)

    def test_expand_splits_brace_shorthand(self) -> None:
        """``Dir/{A, B}.lean`` is two citations, not one."""
        self.assertEqual(ca.expand("Dir/{A, B}.lean"), ["Dir/A.lean", "Dir/B.lean"])

    def test_expand_splits_leading_brace_group(self) -> None:
        """The brace group may sit anywhere in the token."""
        self.assertEqual(ca.expand("{A,B}/C.lean"), ["A/C.lean", "B/C.lean"])

    def test_expand_keeps_unbalanced_braces_for_the_malformed_verdict(self) -> None:
        """Stripping stray braces would invent a filename; the token is kept as is."""
        self.assertEqual(ca.expand("Dir/{A.lean"), ["Dir/{A.lean"])
        self.assertIsNone(ca.normalise("Dir/{A.lean"))

    def test_normalise_rejects_what_cannot_mean_a_repository_path(self) -> None:
        """A token that cannot mean a repository path is ``MALFORMED``.

        These are unit assertions on the predicate; that the *extractor* really
        hands it these spellings -- rather than truncating them into something
        that resolves -- is what :class:`GluedTokenTest` pins, because a branch
        the pipeline cannot reach is not a guard.
        """
        self.assertIsNone(ca.normalise("../A.lean"))
        self.assertIsNone(ca.normalise("/A.lean"))
        self.assertIsNone(ca.normalise("~/A.lean"))
        self.assertIsNone(ca.normalise("A/B.lean.bak"))
        self.assertIsNone(ca.normalise("A/B.leanx"))
        self.assertIsNone(ca.normalise("A//B.lean"))
        self.assertEqual(ca.normalise("A/B.lean"), "A/B.lean")

    def test_glued_text_widens_a_match_to_what_was_written(self) -> None:
        """The match is only evidence when nothing path-like touches it."""
        for text, expected in (
            ("see ../X/Y.lean here", "../X/Y.lean"),
            ("see X/Y.lean.bak here", "X/Y.lean.bak"),
            ("see X/Y.lean here", "X/Y.lean"),
        ):
            match = ca.TOKEN.search(text)
            assert match is not None
            self.assertEqual(ca.glued_text(text, match.start(), match.end()), expected)

    def test_unescape_preserves_the_lean_occurrence_count(self) -> None:
        """The coverage arithmetic depends on this: escapes never add or remove a hit."""
        for sample in (r"Foo/Bar\_Baz.lean", r"Dir/\{A, B\}.lean", r"a\%b.lean", "x.lean"):
            self.assertEqual(ca.unescape(sample).count(".lean"), sample.count(".lean"))

    def test_non_citation_list_is_an_enumeration_not_a_wildcard(self) -> None:
        """A bare ``.lean`` is acknowledged only after an enumerated delimiter.

        If ``NON_CITATION`` matched at every position the coverage audit would
        acknowledge every uncovered variant and stop being a guard at all.
        """
        self.assertEqual(ca.acknowledge_non_citations("see *.lean files", []), 1)
        self.assertEqual(ca.acknowledge_non_citations("the .lean extension", []), 1)
        self.assertEqual(
            ca.acknowledge_non_citations(LEFT_GUILLEMET + "Foo" + RIGHT_GUILLEMET + ".lean", []),
            0,
        )


# ---------------------------------------------------------------------------
# 1 - brace shorthand
# ---------------------------------------------------------------------------


BRACE_TEX = "\\texttt{Dir/\\{A, B\\}.lean} is the pair.\n"


class BraceShorthandTest(unittest.TestCase):
    """``Dir/{A, B}.lean`` is two citations and each is resolved separately."""

    def test_each_alternative_is_charged(self) -> None:
        """``Dir/B.lean`` is missing even though ``Dir/A.lean`` resolves."""
        with fixture({"tex/g.tex": BRACE_TEX}, tracked=["IsingModel/Dir/A.lean"]):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(classes(report, "tex/g.tex"), {"RESOLVED": 1, "MISSING": 1})
        self.assertEqual(tokens_of(report, ca.MISSING), ["Dir/B.lean"])
        self.assertEqual(report.coverage, [])


# ---------------------------------------------------------------------------
# 2 - verbatim source-line wrap
# ---------------------------------------------------------------------------


WRAP_TEX = (
    "\\begin{Verbatim}\n"
    "Branches/LocalCoverPatch/Vitali/Ball/\n"
    "Bridge.lean\n"
    "\\end{Verbatim}\n"
)

TREE_TEX = (
    "\\begin{Verbatim}\n"
    "+-- Inequalities/\n"
    "    GKS.lean                  GKS-I, GKS-II\n"
    "\\end{Verbatim}\n"
)

INDENTED_PREFIX_TEX = (
    "\\begin{Verbatim}\n"
    "    Inequalities/\n"
    "GKS.lean                  GKS-I, GKS-II\n"
    "\\end{Verbatim}\n"
)

# The same wrapped path in each environment of the verbatim family. Recognising
# the family is now purely an extraction concern -- it is what lets the two
# source lines be read as the one path the document wrote -- so this is where
# the enumeration earns its place.
WRAP_IN_VERBATIM_FAMILY_TEX = {
    name: (
        "\\begin{%s}\n" % name
        + "Branches/LocalCoverPatch/Vitali/Ball/\n"
        + "Bridge.lean\n"
        + "\\end{%s}\n" % name
    )
    for name in ("Verbatim", "verbatim", "lstlisting", "alltt")
}


class VerbatimWrapTest(unittest.TestCase):
    """A path split across two source lines is one citation, and it is charged."""

    def test_joined_path_is_charged_as_written(self) -> None:
        """The document names a full path; the full path is what must resolve."""
        with fixture({"tex/g.tex": WRAP_TEX}, tracked=["IsingModel/Other/Bridge.lean"]):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(
            tokens_of(report, ca.MISSING),
            ["Branches/LocalCoverPatch/Vitali/Ball/Bridge.lean"],
        )
        self.assertEqual(report.coverage, [])

    def test_the_whole_verbatim_family_is_tokenised_alike(self) -> None:
        """An unlisted environment would tokenise its block differently.

        This is the enumeration's remaining job. It used to be justified by the
        exemption channel (an unrecognised block let a quoted directive act);
        with the channel deleted the reason is extraction alone -- inside a
        recognised environment the two source lines are read as one path, and
        outside one the continuation is charged as a bare basename instead.
        """
        for name, text in sorted(WRAP_IN_VERBATIM_FAMILY_TEX.items()):
            with self.subTest(environment=name):
                with fixture({"tex/g.tex": text}, tracked=["IsingModel/Other/Bridge.lean"]):
                    report = ca.audit(["tex/g.tex"])
                self.assertEqual(
                    tokens_of(report, ca.MISSING),
                    ["Branches/LocalCoverPatch/Vitali/Ball/Bridge.lean"],
                )
                self.assertEqual(report.coverage, [])

    def test_ascii_tree_indentation_is_never_joined(self) -> None:
        """Rebuilding a directory from tree layout would be the banned inference.

        The header ``+-- Inequalities/`` and the indented entry below it must
        stay two separate things, so the entry is charged ``BASENAME_ONLY``
        rather than silently resolved as ``Inequalities/GKS.lean``.
        """
        with fixture({"tex/g.tex": TREE_TEX}, tracked=["IsingModel/Inequalities/GKS.lean"]):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(classes(report, "tex/g.tex"), {"BASENAME_ONLY": 1})
        self.assertEqual(tokens_of(report, ca.BASENAME_ONLY), ["GKS.lean"])

    def test_an_indented_heading_is_not_a_wrapped_source_line(self) -> None:
        """The other direction of the same rule, and the one that was open.

        ``+-- Inequalities/`` is refused because of the ``+--``; an *indented*
        heading with a column-0 entry under it has neither marker, so only the
        indentation distinguishes a tree from a wrapped path. Joining them would
        resolve ``GKS.lean`` as ``Inequalities/GKS.lean`` -- a directory taken
        from layout, exactly what ``test_ascii_tree_indentation_is_never_joined``
        forbids in the mirror-image case.
        """
        with fixture(
            {"tex/g.tex": INDENTED_PREFIX_TEX}, tracked=["IsingModel/Inequalities/GKS.lean"]
        ):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(classes(report, "tex/g.tex"), {"BASENAME_ONLY": 1})
        self.assertEqual(tokens_of(report, ca.BASENAME_ONLY), ["GKS.lean"])
        self.assertEqual(report.coverage, [])


# ---------------------------------------------------------------------------
# 3 - bare prose token
# ---------------------------------------------------------------------------


BARE_TEX = "The proof used to live in Foo/Gone.lean before the split.\n"


class BareTokenTest(unittest.TestCase):
    """A citation written without any macro is still a citation."""

    def test_bare_prose_citation_is_charged(self) -> None:
        """No ``\\texttt`` wrapper, same verdict."""
        with fixture({"tex/g.tex": BARE_TEX}, tracked=["IsingModel/Foo/Here.lean"]):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(tokens_of(report, ca.MISSING), ["Foo/Gone.lean"])
        self.assertEqual(report.coverage, [])


# ---------------------------------------------------------------------------
# 4 - archive tags and directive-shaped text (there is no exemption channel)
# ---------------------------------------------------------------------------


ARCHIVED_TEX = "\\texttt{Peierls/RayExitAnchor.lean} was the old route.\n"

# The documents below are every spelling in which a ``citation-audit:``
# exemption was once written, and every spelling in which one could be quoted.
# Telling those two apart is what the deleted mechanism had to do, and what it
# got wrong three times running; with no exemption channel left they are one
# thing -- text -- and each must receive the verdict its citation would have
# received had the line not been there at all.
DIRECTIVE_TEX = (
    "% citation-audit: archived archive/stub\n"
    "\\texttt{Peierls/RayExitAnchor.lean} was the old route.\n"
)

DIRECTIVE_WRONG_TEX = (
    "% citation-audit: archived archive/stub\n"
    "\\texttt{Peierls/NeverExisted.lean} was the old route.\n"
)

PREFIX_TEX = (
    "% citation-audit: prefix IsingModel/Inequalities/\n"
    "\\begin{Verbatim}\n"
    "GKS.lean                  GKS-I, GKS-II\n"
    "\\end{Verbatim}\n"
)

# The directive spelling quoted in running prose, the way documentation about
# this tool would be transcribed into the guide, in each document syntax.
DIRECTIVE_QUOTED_TEX = (
    "Prefix such a block with % citation-audit: prefix IsingModel/Inequalities/ to exempt it.\n"
    "\\texttt{GKS.lean} is one of the entries.\n"
)

DIRECTIVE_MD = (
    "<!-- citation-audit: prefix IsingModel/Inequalities/ -->\n"
    "`GKS.lean` holds GKS-I and GKS-II.\n"
)

DIRECTIVE_QUOTED_MD = (
    "Write <!-- citation-audit: prefix IsingModel/Inequalities/ --> above the block.\n"
    "`GKS.lean` holds GKS-I and GKS-II.\n"
)

# The same, quoted inside a sample block rather than issued as an instruction.
DIRECTIVE_IN_VERBATIM_TEX = (
    "\\begin{Verbatim}\n"
    "% citation-audit: prefix IsingModel/Inequalities/\n"
    "GKS.lean                  GKS-I, GKS-II\n"
    "\\end{Verbatim}\n"
)

# The same sample, printed with a verbatim environment other than fancyvrb's
# ``Verbatim``. Each of these armed the quoted directive for real until the
# environment family was enumerated -- round two of the three that ended in the
# channel being deleted.
DIRECTIVE_IN_OTHER_VERBATIM_TEX = {
    "verbatim": (
        "\\begin{verbatim}\n"
        "% citation-audit: prefix IsingModel/Inequalities/\n"
        "GKS.lean                  GKS-I, GKS-II\n"
        "\\end{verbatim}\n"
    ),
    "lstlisting": (
        "\\begin{lstlisting}[language=Lean]\n"
        "% citation-audit: prefix IsingModel/Inequalities/\n"
        "GKS.lean                  GKS-I, GKS-II\n"
        "\\end{lstlisting}\n"
    ),
    "alltt": (
        "\\begin{alltt}\n"
        "% citation-audit: prefix IsingModel/Inequalities/\n"
        "GKS.lean                  GKS-I, GKS-II\n"
        "\\end{alltt}\n"
    ),
}

# The markdown counterpart: the syntax shown in an indented code block, which is
# a rendered sample and not a comment. It armed the directive for real while the
# comment pattern accepted leading whitespace.
DIRECTIVE_INDENTED_MD = (
    "The exemption is written like this:\n"
    "\n"
    "    <!-- citation-audit: prefix IsingModel/Inequalities/ -->\n"
    "    `GKS.lean` holds GKS-I and GKS-II.\n"
)

# The same text at a shallower indent, where markdown renderers disagree about
# whether it is a comment or content. It armed the directive too, and is refused
# now on the fail-closed side: an author who means it un-indents to column 0.
DIRECTIVE_INDENTED_SHALLOW_MD = (
    "- The exemption is written like this:\n"
    "\n"
    "  <!-- citation-audit: prefix IsingModel/Inequalities/ -->\n"
    "  `GKS.lean` holds GKS-I and GKS-II.\n"
)

# A directive whose block has since been deleted, leaving it pointing at
# whatever citation happens to come next.
DIRECTIVE_ORPHANED_TEX = (
    "% citation-audit: archived archive/stub\n"
    "The block this directive annotated was deleted in a later edit.\n"
    "\n"
    "\\texttt{Peierls/RayExitAnchor.lean} is cited here for an unrelated reason.\n"
)

# A directive separated from its citation by blank lines only.
DIRECTIVE_BLANK_LINE_TEX = (
    "% citation-audit: archived archive/stub\n"
    "\n"
    "\\texttt{Peierls/RayExitAnchor.lean} was the old route.\n"
)

STUB_TAG = {"archive/stub": ["Peierls/RayExitAnchor.lean"]}

# The corpus: ``(name, target, document, fixture kwargs, required verdict)``.
# Every entry contains directive-shaped text, and every entry's verdict is the
# one the citation gets on its own merits -- ``MISSING`` for a path only an
# archive tag has, ``BASENAME_ONLY`` for a bare basename. The earnest spellings
# (column-0 tex comment, column-0 markdown comment, a prefix written above a
# block) sit in the same table as the quoted ones on purpose: after the deletion
# there is nothing to distinguish them by.
#
# Every case keeps a tracked ``.lean`` file that has nothing to do with the
# citation, so the resolution set is never empty: a verdict read off a vacuous
# run would be worth nothing.
TAGGED = {"tags": STUB_TAG, "tracked": ["IsingModel/Other/Thing.lean"]}
GKS = {"tracked": ["IsingModel/Inequalities/GKS.lean"]}

INERT_DIRECTIVE_CASES = (
    ("tex comment, archived", "tex/g.tex", DIRECTIVE_TEX, TAGGED, {"MISSING": 1}),
    (
        "tex comment, archived, path absent from the tag",
        "tex/g.tex",
        DIRECTIVE_WRONG_TEX,
        TAGGED,
        {"MISSING": 1},
    ),
    (
        "tex comment, unknown tag",
        "tex/g.tex",
        DIRECTIVE_TEX,
        {"tracked": ["IsingModel/Other/Thing.lean"]},
        {"MISSING": 1},
    ),
    (
        "tex comment, misspelled kind",
        "tex/g.tex",
        DIRECTIVE_TEX.replace("archived", "arcived"),
        TAGGED,
        {"MISSING": 1},
    ),
    (
        "tex comment, separated by a blank line",
        "tex/g.tex",
        DIRECTIVE_BLANK_LINE_TEX,
        TAGGED,
        {"MISSING": 1},
    ),
    (
        "tex comment, subject block deleted",
        "tex/g.tex",
        DIRECTIVE_ORPHANED_TEX,
        TAGGED,
        {"MISSING": 1},
    ),
    ("tex comment, prefix above a Verbatim block", "tex/g.tex", PREFIX_TEX, GKS,
     {"BASENAME_ONLY": 1}),
    ("markdown comment at column 0", "docs/g.md", DIRECTIVE_MD, GKS, {"BASENAME_ONLY": 1}),
    ("quoted mid-sentence (tex)", "tex/g.tex", DIRECTIVE_QUOTED_TEX, GKS,
     {"BASENAME_ONLY": 1}),
    ("quoted mid-sentence (markdown)", "docs/g.md", DIRECTIVE_QUOTED_MD, GKS,
     {"BASENAME_ONLY": 1}),
    ("printed inside a Verbatim block", "tex/g.tex", DIRECTIVE_IN_VERBATIM_TEX, GKS,
     {"BASENAME_ONLY": 1}),
) + tuple(
    (f"printed inside a {name} block", "tex/g.tex", text, GKS, {"BASENAME_ONLY": 1})
    for name, text in sorted(DIRECTIVE_IN_OTHER_VERBATIM_TEX.items())
) + (
    ("printed in an indented markdown block", "docs/g.md", DIRECTIVE_INDENTED_MD, GKS,
     {"BASENAME_ONLY": 1}),
    ("printed at a shallow markdown indent", "docs/g.md", DIRECTIVE_INDENTED_SHALLOW_MD, GKS,
     {"BASENAME_ONLY": 1}),
)


class NoExemptionChannelTest(unittest.TestCase):
    """Nothing written in a document can stop a citation being charged.

    This replaces the suite that pinned the ``citation-audit:`` directive's
    behaviour. That mechanism was deleted after the same defect -- a *quotation*
    of the syntax arming a real exemption -- recurred three times and each fix
    was one more enumerated spelling, with a live directive population of zero
    throughout. What is pinned now is the property that survives the deletion
    and does not depend on any enumeration: every one of those documents, the
    earnest and the quoted alike, gets the ordinary verdict.
    """

    def test_a_path_only_an_archive_tag_has_does_not_resolve(self) -> None:
        """Measured: unconditional tag resolution exonerates 276 of 280 no-match
        citations, so no tag is consulted at all."""
        with fixture({"tex/g.tex": ARCHIVED_TEX}, tags=STUB_TAG):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(classes(report, "tex/g.tex"), {"MISSING": 1})

    def test_every_directive_spelling_is_inert(self) -> None:
        """The whole corpus, earnest and quoted, receives the ordinary verdict."""
        for name, target, text, kwargs, expected in INERT_DIRECTIVE_CASES:
            with self.subTest(case=name):
                with fixture({target: text}, **kwargs):  # type: ignore[arg-type]
                    report = ca.audit([target])
                self.assertEqual(classes(report, target), expected)
                self.assertEqual(len(report.findings), sum(expected.values()))
                self.assertEqual(report.coverage, [])
                self.assertEqual(report.hard, [])

    def test_the_corpus_covers_both_syntaxes_and_both_verdicts(self) -> None:
        """A corpus that drifted to one shape would pin much less than it looks.

        The sweep above is only as strong as its spread: without this, deleting
        every markdown case (or every case whose citation is charged
        ``MISSING``) would leave a green, much weaker test.
        """
        targets = {target for _, target, _, _, _ in INERT_DIRECTIVE_CASES}
        verdicts = {
            name for _, _, _, _, expected in INERT_DIRECTIVE_CASES for name in expected
        }
        self.assertEqual(targets, {"tex/g.tex", "docs/g.md"})
        self.assertEqual(verdicts, {"MISSING", "BASENAME_ONLY"})
        self.assertGreaterEqual(len(INERT_DIRECTIVE_CASES), 14)
        for _, _, text, _, _ in INERT_DIRECTIVE_CASES:
            self.assertIn("citation-audit:", text)

    def test_the_module_carries_no_exemption_machinery(self) -> None:
        """Structural, not behavioural: the capability must be absent, not unused.

        A dormant directive parser would be one edit away from being armed
        again, and the argument for deleting the channel was precisely that its
        correctness needed an adjudication a text scan cannot make.
        """
        for name in (
            "DIRECTIVE",
            "DIRECTIVE_KINDS",
            "Directive",
            "parse_directive",
            "RESOLVED_BY_DIRECTIVE",
            "tag_lean_files",
            "TEX_COMMENT",
            "MD_COMMENT",
            "MD_FENCE",
        ):
            self.assertFalse(hasattr(ca, name), f"{name} is still there")
        self.assertNotIn("directive", ca.Citation._fields)
        self.assertFalse(hasattr(ca.Resolver, "tag_matches"))
        # No git history query of any kind: the tracked working set is the only
        # resolution source, as ``ResolutionSetTest`` asserts from the other side.
        self.assertNotIn("ls-tree", CITATION_AUDIT_PATH.read_text(encoding="utf-8"))


# ---------------------------------------------------------------------------
# 5/6 - basename-only and ambiguous
# ---------------------------------------------------------------------------


BASENAME_TEX = "\\texttt{Bar.lean} holds it.\n"
AMBIGUOUS_TEX = "\\texttt{Basic.lean} and \\texttt{Sub/Basic.lean}.\n"


class SuffixVerdictTest(unittest.TestCase):
    """One match is not enough; a unique match without a directory is not enough."""

    def test_unique_match_without_a_directory_is_basename_only(self) -> None:
        """A bare basename is evidence of a name, not of a path."""
        with fixture({"tex/g.tex": BASENAME_TEX}, tracked=["IsingModel/Foo/Bar.lean"]):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(classes(report, "tex/g.tex"), {"BASENAME_ONLY": 1})

    def test_several_matches_are_ambiguous_at_every_depth(self) -> None:
        """Both a bare and a multi-component ambiguous citation are charged."""
        with fixture(
            {"tex/g.tex": AMBIGUOUS_TEX},
            tracked=["IsingModel/A/Sub/Basic.lean", "IsingModel/B/Sub/Basic.lean"],
        ):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(classes(report, "tex/g.tex"), {"AMBIGUOUS": 2})
        self.assertEqual(sorted(tokens_of(report, ca.AMBIGUOUS)), ["Basic.lean", "Sub/Basic.lean"])


# ---------------------------------------------------------------------------
# 6b - path text glued to a match
# ---------------------------------------------------------------------------


GLUED_TEX = (
    "Absolute \\texttt{/X/Y.lean} and relative \\texttt{./X/Y.lean},\n"
    "traversal \\texttt{../X/Y.lean} and home \\texttt{~/X/Y.lean},\n"
    "backup \\texttt{X/Y.lean.bak} and typo \\texttt{X/Y.leanx}.\n"
    "The delimited spelling is \\texttt{X/Y.lean}.\n"
)

GLUED_SPELLINGS = [
    "../X/Y.lean",
    "./X/Y.lean",
    "/X/Y.lean",
    "X/Y.lean.bak",
    "X/Y.leanx",
    "~/X/Y.lean",
]


class GluedTokenTest(unittest.TestCase):
    """A match that touches path text is charged as written, never truncated.

    ``TOKEN`` has no boundary on either side, so on every spelling below it
    matches the substring ``X/Y.lean`` -- a path the document did not write, and
    one that resolves. Six citations of files this repository does not have would
    have been reported as clean, which is the fail-open shape this whole tool
    exists to refuse.
    """

    def test_glued_spellings_are_malformed_not_resolved(self) -> None:
        """Every glued spelling is a finding, and the delimited one still resolves."""
        with fixture({"tex/g.tex": GLUED_TEX}, tracked=["IsingModel/X/Y.lean"]):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(classes(report, "tex/g.tex"), {"RESOLVED": 1, "MALFORMED": 6})
        self.assertEqual(sorted(tokens_of(report, ca.MALFORMED)), GLUED_SPELLINGS)
        self.assertEqual(report.coverage, [])

    def test_the_glued_run_is_reported_verbatim(self) -> None:
        """The finding names what the document says, so it can be found and fixed."""
        with fixture({"tex/g.tex": GLUED_TEX}, tracked=["IsingModel/X/Y.lean"]):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(len(report.findings), 6)
        for finding in report.findings:
            self.assertEqual(finding.cls, ca.MALFORMED)
            self.assertIn("+glued", finding.variant)
        self.assertNotIn("X/Y.lean", tokens_of(report, ca.MALFORMED))


# ---------------------------------------------------------------------------
# 7 - escapes
# ---------------------------------------------------------------------------


ESCAPE_TEX = "\\texttt{Foo/Bar\\_Baz.lean} is the file.\n"


class EscapeTest(unittest.TestCase):
    """LaTeX escapes are undone before the token is looked up."""

    def test_escaped_underscore_resolves(self) -> None:
        """Otherwise every underscored filename would be a false ``MISSING``."""
        with fixture({"tex/g.tex": ESCAPE_TEX}, tracked=["IsingModel/Foo/Bar_Baz.lean"]):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(classes(report, "tex/g.tex"), {"RESOLVED": 1})


# ---------------------------------------------------------------------------
# 8 - the coverage audit itself
# ---------------------------------------------------------------------------


UNCOVERED_TEX = LEFT_GUILLEMET + "Foo" + RIGHT_GUILLEMET + ".lean is unreachable.\n"


class CoverageAuditTest(unittest.TestCase):
    """The keystone: an occurrence the tokeniser cannot form a token from fails the run."""

    def test_unaccounted_occurrence_fails_the_run(self) -> None:
        """This is the guard that turns a silent miss into a loud failure."""
        with fixture({"tex/g.tex": UNCOVERED_TEX}, tracked=["IsingModel/A.lean"]):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(len(report.coverage), 2)  # the line, and the file totals
        self.assertIn("raw=1 captured=0", report.coverage[0])
        self.assertFalse(report.ok_structurally)

    def test_coverage_failure_suppresses_the_findings_report_in_every_format(self) -> None:
        """Publishing a census from a provably incomplete extractor is the artefact.

        Parameterised over every format on purpose: ``tsv`` is the one this
        module calls "the count-of-record", so a census suppressed in the human
        report but printed unmarked as TSV is the artefact surviving in exactly
        the form that gets quoted as a number.
        """
        for fmt in ("text", "tsv", "json"):
            with self.subTest(format=fmt):
                with fixture(
                    {"tex/g.tex": UNCOVERED_TEX + BARE_TEX}, tracked=["IsingModel/A.lean"]
                ):
                    code, out = run_main(ca, "--targets", "tex/g.tex", "--format", fmt)
                self.assertEqual(code, 1)
                self.assertIn("COVERAGE", out)
                self.assertNotIn("Foo/Gone.lean", out)
                self.assertNotIn("MISSING", out)
                if fmt == "text":
                    self.assertIn("NOT reported", out)

    def test_a_hard_failure_suppresses_the_census_in_every_format(self) -> None:
        """The same rule for the other kind of untrustworthy run.

        A contaminated resolution set makes the verdicts meaningless in a
        different way from an incomplete extractor, and a census published
        beside it would be quoted just as readily.
        """
        for fmt in ("text", "tsv", "json"):
            with self.subTest(format=fmt):
                with fixture(
                    {"tex/g.tex": BARE_TEX},
                    tracked=[".self-local/benchmarks/IsingModel/Foo/Gone.lean"],
                ):
                    code, out = run_main(ca, "--targets", "tex/g.tex", "--format", fmt)
                self.assertEqual(code, 1)
                self.assertIn("CONTAMINATED", out)
                self.assertNotIn("RESOLVED", out)

    def test_file_totals_are_checked_as_well_as_lines(self) -> None:
        """Per-line equality alone would miss an attribution bug that cancels."""
        with fixture({"tex/g.tex": BARE_TEX}, tracked=["IsingModel/Foo/Gone.lean"]):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(report.coverage, [])
        self.assertEqual(report.raw_occurrences["tex/g.tex"], 1)

    def test_verbatim_delimiter_lines_are_scanned(self) -> None:
        """A citation in ``\\begin{Verbatim}[label=...]`` must not escape the audit."""
        text = "\\begin{Verbatim}[label=Foo/Gone.lean]\nplain\n\\end{Verbatim}\n"
        with fixture({"tex/g.tex": text}, tracked=["IsingModel/A.lean"]):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(report.coverage, [])
        self.assertEqual(tokens_of(report, ca.MISSING), ["Foo/Gone.lean"])


# ---------------------------------------------------------------------------
# 9 - the resolution set
# ---------------------------------------------------------------------------


class ResolutionSetTest(unittest.TestCase):
    """Only git-tracked files may answer a citation."""

    def test_untracked_file_on_disk_does_not_resolve(self) -> None:
        """Measured: 112,420 ``.lean`` files on disk against 2,018 tracked."""
        with fixture(
            {"tex/g.tex": BARE_TEX},
            tracked=["IsingModel/A.lean"],
            untracked=["IsingModel/Foo/Gone.lean"],
        ):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(tokens_of(report, ca.MISSING), ["Foo/Gone.lean"])

    def test_resolution_outside_the_owned_prefixes_is_a_hard_failure(self) -> None:
        """A benchmark copy of a deleted file must never quietly answer a citation."""
        with fixture(
            {"tex/g.tex": BARE_TEX},
            tracked=[".self-local/benchmarks/IsingModel/Foo/Gone.lean"],
        ):
            report = ca.audit(["tex/g.tex"])
        self.assertTrue(any(item.startswith("CONTAMINATED") for item in report.hard))
        self.assertFalse(report.ok_structurally)

    def test_the_real_resolution_set_is_the_tracked_one(self) -> None:
        """No ``.lake/`` mathlib copy and no ``.self-local/`` scratch may leak in."""
        tracked = ca.tracked_lean_files()
        self.assertGreaterEqual(len(tracked), ca.MIN_TRACKED_LEAN)
        self.assertEqual([path for path in tracked if path.startswith(".lake/")], [])
        self.assertEqual([path for path in tracked if path.startswith(".self-local/")], [])

    def test_the_script_never_enumerates_the_filesystem(self) -> None:
        """The resolution path must have no way to see an untracked file."""
        source = CITATION_AUDIT_PATH.read_text(encoding="utf-8")
        for forbidden in ("os.walk", "iterdir", "rglob", "glob("):
            self.assertNotIn(forbidden, source)


# ---------------------------------------------------------------------------
# 10 - anti-vacuity guards
# ---------------------------------------------------------------------------


class VacuityTest(unittest.TestCase):
    """A run that checked nothing must never report a pass."""

    def test_missing_target_is_a_hard_failure(self) -> None:
        """"The file is not there" is not a reason to skip it."""
        with fixture({"tex/g.tex": BARE_TEX}):
            report = ca.audit(["tex/absent.tex"])
        self.assertTrue(any(item.startswith("TARGET") for item in report.hard))
        self.assertFalse(report.ok_structurally)

    def test_untracked_target_is_a_hard_failure(self) -> None:
        """An untracked document is not the published one."""
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            _run_git(root, "init", "-q")
            (root / "tex").mkdir()
            (root / "tex" / "g.tex").write_text(BARE_TEX, encoding="utf-8")
            with patched(ca, REPO_ROOT=root, MIN_TRACKED_LEAN=0):
                report = ca.audit(["tex/g.tex"])
        self.assertTrue(any("not tracked" in item for item in report.hard))

    def test_empty_target_list_is_a_hard_failure(self) -> None:
        """Emptying ``TARGETS`` is the cheapest possible way to make the tool pass."""
        with fixture({"tex/g.tex": BARE_TEX}):
            report = ca.audit([])
        self.assertTrue(any(item.startswith("VACUOUS") for item in report.hard))
        self.assertFalse(report.ok_structurally)

    def test_citation_floor_is_enforced(self) -> None:
        """A tokeniser that stopped matching would otherwise look perfect."""
        with fixture(
            {"tex/g.tex": BARE_TEX},
            tracked=["IsingModel/A.lean"],
            MIN_CITATIONS={"tex/g.tex": 50},
        ):
            report = ca.audit(["tex/g.tex"])
        self.assertTrue(any(item.startswith("VACUOUS") for item in report.hard))

    def test_tracked_floor_is_enforced(self) -> None:
        """An empty resolution set would make every citation "missing" and the
        report meaningless in the other direction."""
        with fixture(
            {"tex/g.tex": BARE_TEX},
            tracked=["IsingModel/A.lean"],
            MIN_TRACKED_LEAN=500,
        ):
            report = ca.audit(["tex/g.tex"])
        self.assertTrue(any("MIN_TRACKED_LEAN" in item for item in report.hard))


# ---------------------------------------------------------------------------
# 11 - self-reference
# ---------------------------------------------------------------------------


SELFREF_TEX = (
    "The result now lives in \\texttt{A/X.lean},\n"
    "and it is re-exported for backward compatibility by\n"
    "the old \\texttt{X.lean} shim.\n"
    "\n"
    "Unrelated paragraph citing \\texttt{A/X.lean} once more.\n"
)


class SelfReferenceTest(unittest.TestCase):
    """"Moved to F and re-exported by the old F" is a vacuous sentence."""

    def test_repeated_citation_with_a_cue_is_reported(self) -> None:
        """The pair is suffix-related and a cue sits between the two mentions."""
        with fixture({"tex/g.tex": SELFREF_TEX}, tracked=["IsingModel/A/X.lean"]):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(len(report.selfrefs), 1)
        self.assertEqual(report.selfrefs[0].token, "A/X.lean >> X.lean")

    def test_self_reference_is_advisory_and_does_not_gate(self) -> None:
        """Cue matching can only under-detect, so it charges but never blocks."""
        with fixture({"tex/g.tex": SELFREF_TEX}, tracked=["IsingModel/A/X.lean"]):
            code, out = run_main(ca, "--targets", "tex/g.tex", "--strict")
        self.assertIn("SELFREF", out)
        self.assertEqual(code, 1)  # BASENAME_ONLY X.lean is what fails, not SELFREF
        self.assertNotIn("UNRESOLVED SELFREF", out)

    def test_a_paragraph_is_one_finding_not_one_per_pair(self) -> None:
        """A paragraph citing one file many times is one self-reference.

        Counting pairs instead would report 4,084 advisories for
        ``docs/index.md`` alone, which is a report nobody reads.
        """
        text = "cited \\texttt{A/X.lean}\nre-exported\n" * 4
        with fixture({"tex/g.tex": text}, tracked=["IsingModel/A/X.lean"]):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(len(report.selfrefs), 1)

    def test_a_cue_on_a_citation_line_is_not_between_the_citations(self) -> None:
        """Documented under-detection: the cue must sit on a line of its own.

        Adjacent citations with the cue on one of their own lines are missed.
        The rule charges only what it can see between the two mentions, which is
        an under-detection and therefore allowed; it is recorded here so the
        limitation is a pinned fact rather than a surprise.
        """
        text = "now lives in \\texttt{A/X.lean} and is\nre-exported as \\texttt{X.lean}.\n"
        with fixture({"tex/g.tex": text}, tracked=["IsingModel/A/X.lean"]):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(report.selfrefs, [])


# ---------------------------------------------------------------------------
# 12 - the ratchet
# ---------------------------------------------------------------------------


class RatchetTest(unittest.TestCase):
    """Progress is measured per finding, never on totals."""

    def test_one_fix_does_not_pay_for_one_regression(self) -> None:
        """Totals are equal here; the multiset comparison still fails."""
        baseline = Counter({(ca.MISSING, "t", "A.lean"): 2})
        current = Counter({(ca.MISSING, "t", "A.lean"): 1, (ca.MISSING, "t", "B.lean"): 1})
        regressions, cleared = ca.ratchet(current, baseline)
        self.assertEqual(len(regressions), 1)
        self.assertIn("B.lean", regressions[0])
        self.assertEqual(cleared, 1)

    def test_a_strict_decrease_passes(self) -> None:
        """Remediation shrinks the baseline monotonically."""
        baseline = Counter({(ca.MISSING, "t", "A.lean"): 2})
        current = Counter({(ca.MISSING, "t", "A.lean"): 1})
        regressions, cleared = ca.ratchet(current, baseline)
        self.assertEqual((regressions, cleared), ([], 1))

    def test_line_numbers_are_payload_not_key(self) -> None:
        """Otherwise every unrelated edit would rewrite the whole baseline."""
        rows = ca.aggregate(
            [
                ca.Finding(ca.MISSING, "t", "A.lean", 900, "macro"),
                ca.Finding(ca.MISSING, "t", "A.lean", 12, "macro"),
            ]
        )
        self.assertEqual(rows, [ca.Row(ca.MISSING, "t", "A.lean", 2, 12)])

    def test_baseline_round_trip(self) -> None:
        """What is written is what is read back."""
        with fixture(
            {"tex/g.tex": BARE_TEX},
            tracked=["IsingModel/A.lean"],
            TARGETS=("tex/g.tex",),
            MIN_CITATIONS={"tex/g.tex": 1},
        ) as root:
            code, _ = run_main(
                ca, "--targets", "tex/g.tex", "--update-baseline", "audit/base.tsv"
            )
            self.assertEqual(code, 0)
            multiset, census, tracked = ca.read_baseline(root / "audit" / "base.tsv")
        self.assertEqual(multiset[(ca.MISSING, "tex/g.tex", "Foo/Gone.lean")], 1)
        self.assertEqual(census["tex/g.tex"]["MISSING"], 1)
        self.assertEqual(tracked, 1)

    def test_baseline_is_not_written_from_an_untrustworthy_run(self) -> None:
        """A coverage failure must not be allowed to become the new normal."""
        with fixture(
            {"tex/g.tex": UNCOVERED_TEX},
            tracked=["IsingModel/A.lean"],
            TARGETS=("tex/g.tex",),
            MIN_CITATIONS={"tex/g.tex": 1},
        ) as root:
            code, out = run_main(
                ca, "--targets", "tex/g.tex", "--update-baseline", "audit/base.tsv"
            )
            # Inside the fixture: the temporary tree is gone once it exits, so
            # this assertion would hold for the wrong reason outside it.
            self.assertFalse((root / "audit" / "base.tsv").exists())
        self.assertEqual(code, 1)
        self.assertIn("refusing to write a baseline", out)

    def test_baseline_is_not_written_from_a_partial_target_set(self) -> None:
        """``--targets`` plus ``--update-baseline`` must not shrink the record.

        The file is rendered from one run, so a run that opened one of the two
        targets would drop every row of the other -- the recorded debt falls, no
        citation was fixed, and the ratchet afterwards has nothing to compare the
        dropped rows against. Structurally the partial run is perfectly sound,
        which is why the refusal has to be its own check.
        """
        with fixture(
            {"tex/a.tex": BARE_TEX, "tex/b.tex": BASENAME_TEX},
            tracked=["IsingModel/Foo/Bar.lean"],
            TARGETS=("tex/a.tex", "tex/b.tex"),
            MIN_CITATIONS={"tex/a.tex": 1, "tex/b.tex": 1},
        ) as root:
            code, out = run_main(
                ca, "--targets", "tex/a.tex", "--update-baseline", "audit/base.tsv"
            )
            self.assertFalse((root / "audit" / "base.tsv").exists())
        self.assertEqual(code, 1)
        self.assertIn("refusing to write a baseline", out)
        self.assertIn("tex/b.tex", out)

    def test_missing_baseline_is_a_hard_failure(self) -> None:
        """No baseline means no ratchet, which must not read as "no regressions"."""
        with fixture({"tex/g.tex": BARE_TEX}, tracked=["IsingModel/A.lean"]):
            code, out = run_main(ca, "--targets", "tex/g.tex", "--baseline", "audit/none.tsv")
        self.assertEqual(code, 1)
        self.assertIn("BASELINE", out)


# ---------------------------------------------------------------------------
# 13 - the frozen corpus (the extractor pin)
# ---------------------------------------------------------------------------


class FrozenCorpusTest(unittest.TestCase):
    """What the census equality pin was trying to say, said about frozen inputs.

    ``scripts/audit/citation_corpus/`` holds one document per syntax, a frozen
    resolution set, and the census they must produce. Both halves are frozen
    because a verdict is a claim about a document *and* about the set it is
    resolved against; leaving either to follow the real tree would put the pin
    back on live data, which is the defect this replaces.

    The distinction that matters: this expectation moves **iff the extractor
    moves**. Editing ``tex/proof-guide.tex`` cannot touch it, so remediation
    never has to update it -- and a relaxed resolution rule (the one change the
    ratchet cannot see, because clearing findings is what remediation looks
    like) shows up here as a diff nobody can mistake for progress.
    """

    def test_the_corpus_census_is_exactly_what_is_committed(self) -> None:
        """Byte-for-byte, on the machine-readable half of the expectation."""
        report = corpus_report()
        self.assertEqual(report.coverage, [])
        self.assertEqual(report.hard, [])
        expected = (CORPUS_DIR / "expected.tsv").read_text(encoding="utf-8")
        self.assertEqual(
            baseline_body(ca.render_baseline(report)),
            baseline_body(expected),
            "the extractor's verdict on the frozen corpus changed",
        )

    def test_the_corpus_exercises_every_class(self) -> None:
        """A corpus that lost a class would pin much less than it looks.

        Without this, deleting the one ambiguous citation (or the one malformed
        spelling) from the corpus would leave a green, much weaker test, and the
        expectation file would happily be regenerated around the hole.
        """
        report = corpus_report()
        seen = {
            name
            for target in CORPUS_TARGETS
            for name in ca.ALL_CLASSES
            if report.counts[target][name]
        }
        self.assertEqual(seen, set(ca.ALL_CLASSES))
        for target in CORPUS_TARGETS:
            self.assertGreater(report.counts[target][ca.RESOLVED], 0, target)

    def test_the_corpus_exercises_every_extraction_variant(self) -> None:
        """The other axis: how a citation is written, not how it is classified."""
        report = corpus_report()
        variants = {
            finding.variant for finding in list(report.findings) + list(report.selfrefs)
        }
        for fragment in ("macro", "bare", "verbatim", "+brace", "+glued"):
            self.assertTrue(
                any(fragment in variant for variant in variants), f"no {fragment} variant"
            )
        tex = corpus_documents()["tex/guide.tex"]
        for construct in ("\\texttt{", "\\path{", "\\begin{Verbatim}", "\\_", "*.lean"):
            self.assertIn(construct, tex)
        accounting = report.accounting["tex/guide.tex"]
        # Brace shorthand adds citations, ``NON_CITATION`` spellings subtract
        # them: both directions of the accounting are live in the corpus.
        self.assertGreater(report.citations["tex/guide.tex"], accounting["matched"])
        for target in CORPUS_TARGETS:
            self.assertGreater(report.accounting[target]["acknowledged"], 0, target)

    def test_the_corpus_resolution_set_is_frozen_and_owned(self) -> None:
        """The tracked half of the fixture, pinned like the documents."""
        tracked = corpus_tracked()
        self.assertEqual(len(tracked), 8)
        self.assertEqual(len(set(tracked)), len(tracked))
        for path in tracked:
            self.assertTrue(path.startswith(ca.ALLOWED_TRACKED_PREFIXES), path)

    def test_the_corpus_is_not_audited_by_the_live_run(self) -> None:
        """It is fixture material: a document, not a document under audit."""
        self.assertEqual(
            [target for target in ca.TARGETS if "citation_corpus" in target], []
        )
        self.assertEqual(live_report().visited, list(ca.TARGETS))


# ---------------------------------------------------------------------------
# 14 - updating the baseline, and the deletion budget
# ---------------------------------------------------------------------------


def missing_citations_tex(count: int) -> str:
    """Return a document citing ``count`` distinct files that do not exist."""
    return "".join(
        "Citation \\texttt{Corpus/Missing%02d.lean} here.\n" % index for index in range(count)
    )


def missing_rows(count: int) -> List[Sequence[object]]:
    """Return the baseline rows :func:`missing_citations_tex` produces."""
    return [
        (ca.MISSING, "tex/g.tex", "Corpus/Missing%02d.lean" % index, 1) for index in range(count)
    ]


BASE_CENSUS_40 = (("tex/g.tex", 40, 40, "MISSING=40"),)


class BaselineUpdateTest(unittest.TestCase):
    """``--update-baseline`` may lower the recorded debt, never raise it.

    Rewriting the rows from the current run is the one operation that retires a
    finding without fixing a citation, which is why the previous version -- it
    printed ``+N`` and wrote anyway -- was the tool's own laundering hatch. The
    refusals below are what make the written file provably per-key ``<=`` the
    committed one.
    """

    def _fixture(self, document: str, committed: str, commit: bool = True):
        """Build a repository holding a document and a *committed* baseline."""
        return fixture(
            {"tex/g.tex": document, "audit/base.tsv": committed},
            tracked=["IsingModel/Corpus/Present.lean"],
            commit=commit,
            TARGETS=("tex/g.tex",),
            MIN_CITATIONS={"tex/g.tex": 1},
        )

    def test_a_shrinking_update_is_written(self) -> None:
        """The required act of a remediation commit, and it must stay possible."""
        committed = make_baseline(1, BASE_CENSUS_40, missing_rows(40))
        with self._fixture(missing_citations_tex(30), committed) as root:
            code, out = run_main(
                ca, "--targets", "tex/g.tex", "--update-baseline", "audit/base.tsv"
            )
            written = (root / "audit" / "base.tsv").read_text(encoding="utf-8")
        self.assertEqual(code, 0, out)
        self.assertIn("delta: +0 finding(s), -10 finding(s)", out)
        self.assertIn("citations 40 -> 30 (-10)", out)
        rows, census, _ = ca.parse_baseline(written)
        self.assertEqual(len(rows), 30)
        self.assertEqual(census["tex/g.tex"]["citations"], 30)

    def test_a_growing_update_is_refused(self) -> None:
        """One new key is one unfixed finding turned into an allowance."""
        committed = make_baseline(1, BASE_CENSUS_40, missing_rows(39))
        with self._fixture(missing_citations_tex(40), committed) as root:
            code, out = run_main(
                ca, "--targets", "tex/g.tex", "--update-baseline", "audit/base.tsv"
            )
            after = (root / "audit" / "base.tsv").read_text(encoding="utf-8")
        self.assertEqual(code, 1)
        self.assertIn("GROWN MISSING tex/g.tex Corpus/Missing39.lean", out)
        self.assertIn("refusing to write a baseline that grows", out)
        self.assertEqual(after, committed)

    def test_the_reference_is_the_committed_copy_not_the_working_file(self) -> None:
        """Otherwise a branch ratchets against its own earlier write.

        The working file here already carries the grown row -- exactly the state
        one unrefused write would leave behind -- and the refusal must still
        fire, because what review compares against is the commit.
        """
        committed = make_baseline(1, BASE_CENSUS_40, missing_rows(39))
        grown = make_baseline(1, BASE_CENSUS_40, missing_rows(40))
        with self._fixture(missing_citations_tex(40), committed) as root:
            (root / "audit" / "base.tsv").write_text(grown, encoding="utf-8")
            code, out = run_main(
                ca, "--targets", "tex/g.tex", "--update-baseline", "audit/base.tsv"
            )
        self.assertEqual(code, 1)
        self.assertIn("refusing to write a baseline that grows", out)

    def test_a_creation_is_allowed_and_says_so(self) -> None:
        """No commit has the file, so there is no allowance to launder yet."""
        with self._fixture(missing_citations_tex(3), "", commit=False) as root:
            code, out = run_main(
                ca, "--targets", "tex/g.tex", "--update-baseline", "audit/new.tsv"
            )
            self.assertTrue((root / "audit" / "new.tsv").is_file())
        self.assertEqual(code, 0, out)
        self.assertIn("no committed copy", out)

    def test_an_update_past_the_deletion_budget_is_refused(self) -> None:
        """Deleting the citing text is not remediation, and it is not a refresh."""
        committed = make_baseline(1, BASE_CENSUS_40, missing_rows(40))
        with self._fixture(missing_citations_tex(5), committed) as root:
            code, out = run_main(
                ca, "--targets", "tex/g.tex", "--update-baseline", "audit/base.tsv"
            )
            after = (root / "audit" / "base.tsv").read_text(encoding="utf-8")
        self.assertEqual(code, 1)
        self.assertIn("ERODED tex/g.tex", out)
        self.assertIn("refusing to write a baseline that records a deletion", out)
        self.assertEqual(after, committed)


class DeletionBudgetTest(unittest.TestCase):
    """R11: the one place content loss is charged.

    The ratchet cannot see a deletion -- removing the sentence that carries a
    dangling citation clears the finding exactly as fixing it does -- and the
    floors are a cliff hundreds of citations away. Without this the cheapest way
    to a green run is to delete the prose.
    """

    def _run(
        self, citations: int, committed_citations: int, rows: Optional[int] = None
    ) -> Sequence[object]:
        """Audit a document of ``citations`` against a census of that many.

        ``rows`` is the row count of the committed baseline, which is separate
        on purpose: this class is about the census, so the rows are kept wide
        enough that the ratchet has nothing to say and the exit code is R11's.
        """
        recorded_rows = committed_citations if rows is None else rows
        committed = make_baseline(
            1,
            (
                (
                    "tex/g.tex",
                    committed_citations,
                    committed_citations,
                    "MISSING=%d" % committed_citations,
                ),
            ),
            missing_rows(recorded_rows),
        )
        with fixture(
            {"tex/g.tex": missing_citations_tex(citations), "audit/base.tsv": committed},
            tracked=["IsingModel/Corpus/Present.lean"],
            MIN_CITATIONS={"tex/g.tex": 1},
        ):
            return run_main(ca, "--targets", "tex/g.tex", "--baseline", "audit/base.tsv")

    def test_a_drop_within_the_budget_passes(self) -> None:
        """Remediation is allowed to delete a stale citation."""
        code, out = self._run(80, 100)
        self.assertEqual(code, 0, out)
        self.assertIn("citations 100 -> 80 (-20); deletion budget 25", out)
        self.assertIn("citation audit: PASS", out)

    def test_a_drop_past_the_budget_is_a_hard_failure(self) -> None:
        """And, being hard, it suppresses the census like any untrustworthy run."""
        code, out = self._run(60, 100)
        self.assertEqual(code, 1)
        self.assertIn("ERODED tex/g.tex", out)
        self.assertIn("per-run budget 25", out)
        self.assertIn("NOT reported", out)
        self.assertIn("citation audit: FAIL", out)

    def test_a_missing_census_line_for_a_target_with_rows_is_charged(self) -> None:
        """Deleting the census line would disarm the budget while looking tidy."""
        committed = make_baseline(1, (), missing_rows(40))
        with fixture(
            {"tex/g.tex": missing_citations_tex(40), "audit/base.tsv": committed},
            tracked=["IsingModel/Corpus/Present.lean"],
            MIN_CITATIONS={"tex/g.tex": 1},
        ):
            code, out = run_main(
                ca, "--targets", "tex/g.tex", "--baseline", "audit/base.tsv"
            )
        self.assertEqual(code, 1)
        self.assertIn("no #census line", out)

    def test_growth_in_citations_is_never_charged(self) -> None:
        """The budget is about loss; a document that grows is not suspect."""
        code, out = self._run(140, 100, rows=140)
        self.assertEqual(code, 0, out)
        self.assertNotIn("ERODED", out)


# ---------------------------------------------------------------------------
# Mutation direction
# ---------------------------------------------------------------------------


class MutationTest(unittest.TestCase):
    """Each weakening a developer might plausibly make must break a test above.

    Every case pairs with the fixture test of the same number in the module
    docstring: the mutant is required to *miss* what the real checker catches,
    which is what proves the fixture is not passing vacuously.
    """

    def audit_with(
        self, mutant: types.ModuleType, documents: Dict[str, str], **kwargs: object
    ) -> ca.Report:
        """Run ``mutant.audit`` over a fixture built for the mutant module."""
        with fixture(documents, module=mutant, **kwargs):  # type: ignore[arg-type]
            return mutant.audit(list(documents))

    # 1 - brace shorthand
    def test_expansion_dropped_misses_the_second_alternative(self) -> None:
        """Treating ``Dir/{A, B}.lean`` as one token hides ``Dir/B.lean``."""
        mutant = load_mutated(("    match = BRACE.match(token)", "    match = None"))
        report = self.audit_with(
            mutant, {"tex/g.tex": BRACE_TEX}, tracked=["IsingModel/Dir/A.lean"]
        )
        self.assertNotIn("Dir/B.lean", tokens_of(report, mutant.MISSING))

    # 1b - the brace alternative in the token regex
    def test_token_regex_without_braces_fails_coverage(self) -> None:
        """Dropping the brace alternative makes the occurrence uncountable, loudly."""
        mutant = load_mutated(
            (
                r'TOKEN = re.compile(r"[A-Za-z0-9_][A-Za-z0-9_.+/-]*(?:\{[^}]*\}[A-Za-z0-9_.+/-]*)?\.lean")',
                r'TOKEN = re.compile(r"[A-Za-z0-9_][A-Za-z0-9_.+/-]*\.lean")',
            )
        )
        report = self.audit_with(
            mutant, {"tex/g.tex": BRACE_TEX}, tracked=["IsingModel/Dir/A.lean"]
        )
        self.assertTrue(report.coverage)

    # 2 - verbatim wrap
    def test_without_the_wrap_join_the_full_path_is_never_charged(self) -> None:
        """The document's actual claim (a full path) stops being checked."""
        mutant = load_mutated(
            ("            if continues and pending_wrap is not None:", "            if False:")
        )
        report = self.audit_with(
            mutant, {"tex/g.tex": WRAP_TEX}, tracked=["IsingModel/Other/Bridge.lean"]
        )
        self.assertNotIn(
            "Branches/LocalCoverPatch/Vitali/Ball/Bridge.lean", tokens_of(report, mutant.MISSING)
        )

    # 3 - bare residue
    def test_dropping_the_residue_scan_misses_bare_tokens_and_fails_coverage(self) -> None:
        """Both halves matter: the miss happens, and the guard catches it anyway."""
        mutant = load_mutated(
            ('    units.append(("bare", "".join(masked)))', '    units.append(("bare", ""))')
        )
        report = self.audit_with(
            mutant, {"tex/g.tex": BARE_TEX}, tracked=["IsingModel/Foo/Here.lean"]
        )
        self.assertEqual(tokens_of(report, mutant.MISSING), [])
        self.assertTrue(report.coverage)

    # 4 - archive tags
    def test_re_added_tag_resolution_exonerates_a_deleted_file(self) -> None:
        """The mechanism measured at 276/280 fail-open, rebuilt and caught.

        The mutant is the deleted capability written back from scratch, which is
        the honest form of this mutation now: there is no switch left to flip,
        so what has to be shown is that adding one is detected.
        """
        mutant = load_mutated(
            (
                "    hits = resolver.matches(token)\n"
                "    if len(hits) == 0:\n"
                "        return (MISSING, None)",
                "    hits = resolver.matches(token)\n"
                "    if len(hits) == 0:\n"
                "        archived = suffix_map(\n"
                "            path\n"
                "            for path in _git(\n"
                "                ['ls-tree', '-r', '--name-only', '-z', 'archive/stub']\n"
                "            ).split(chr(0))\n"
                "            if path.endswith('.lean')\n"
                "        )\n"
                "        if archived.get(token):\n"
                "            return (RESOLVED, None)\n"
                "        return (MISSING, None)",
            )
        )
        report = self.audit_with(
            mutant,
            {"tex/g.tex": ARCHIVED_TEX},
            tags=STUB_TAG,
            tracked=["IsingModel/Other/Thing.lean"],
        )
        self.assertEqual(report.findings, [])

    # 4b - the exemption channel as a whole
    def test_a_re_added_exemption_channel_silences_the_whole_corpus(self) -> None:
        """The pairing for :class:`NoExemptionChannelTest`.

        The mutant re-adds the deleted capability in its most permissive form --
        a ``citation-audit:`` line anywhere in the five lines above a citation
        clears it -- and is required to silence *every* document in the corpus,
        the quoted spellings included. That is what makes the sweep's fourteen
        assertions non-vacuous: each of them is charging something that a
        plausible reintroduction would stop charging.
        """
        mutant = load_mutated(
            (
                "            verdict, resolved_path = classify(citation, resolver)",
                "            verdict, resolved_path = classify(citation, resolver)\n"
                "            if verdict in FINDING_CLASSES and any(\n"
                "                'citation-audit:' in item\n"
                "                for item in text.split(chr(10))[\n"
                "                    max(0, citation.line - 6):citation.line\n"
                "                ]\n"
                "            ):\n"
                "                verdict, resolved_path = (RESOLVED, None)",
            )
        )
        for name, target, text, kwargs, _ in INERT_DIRECTIVE_CASES:
            with self.subTest(case=name):
                report = self.audit_with(mutant, {target: text}, **kwargs)
                self.assertEqual(report.findings, [])

    def test_recognising_only_fancyvrb_changes_how_another_block_is_read(self) -> None:
        """Narrowing the family back to ``Verbatim`` loses the wrapped path.

        The hole this mutation used to open was an exemption; with the channel
        deleted what it costs is extraction, and the loss is still silent: the
        document's actual claim (a full path) stops being checked and a bare
        basename is charged in its place.
        """
        for name in ("verbatim", "lstlisting", "alltt"):
            with self.subTest(environment=name):
                mutant = load_mutated(
                    (
                        '    r"(?:B|L|S|Save)?(?:verbatim|verbatimtab|semiverbatim|alltt'
                        '|lstlisting|listing|minted)\\*?",\n    re.IGNORECASE,\n',
                        '    r"Verbatim",\n',
                    )
                )
                report = self.audit_with(
                    mutant,
                    {"tex/g.tex": WRAP_IN_VERBATIM_FAMILY_TEX[name]},
                    tracked=["IsingModel/Other/Bridge.lean"],
                )
                self.assertNotIn(
                    "Branches/LocalCoverPatch/Vitali/Ball/Bridge.lean",
                    tokens_of(report, mutant.MISSING),
                )
                self.assertEqual(tokens_of(report, mutant.BASENAME_ONLY), ["Bridge.lean"])

    # 5 - basename-only
    def test_accepting_bare_basenames_exonerates_them(self) -> None:
        """A basename is not a path; accepting it silently resolves 767 citations."""
        mutant = load_mutated(
            (
                '    if "/" not in token:\n        return (BASENAME_ONLY, None)',
                "    if False:\n        return (BASENAME_ONLY, None)",
            )
        )
        report = self.audit_with(
            mutant, {"tex/g.tex": BASENAME_TEX}, tracked=["IsingModel/Foo/Bar.lean"]
        )
        self.assertEqual(report.findings, [])

    # 6 - ambiguity
    def test_first_match_wins_exonerates_ambiguous_citations(self) -> None:
        """"At least one match" is the classic shape of this bug."""
        mutant = load_mutated(
            (
                "    if len(hits) >= 2:\n        return (AMBIGUOUS, None)",
                "    if False:\n        return (AMBIGUOUS, None)",
            ),
            (
                '    if "/" not in token:\n        return (BASENAME_ONLY, None)',
                "    if False:\n        return (BASENAME_ONLY, None)",
            ),
        )
        report = self.audit_with(
            mutant,
            {"tex/g.tex": AMBIGUOUS_TEX},
            tracked=["IsingModel/A/Sub/Basic.lean", "IsingModel/B/Sub/Basic.lean"],
        )
        self.assertEqual(report.findings, [])

    # 6b - glued path text
    def test_without_the_widening_every_glued_spelling_resolves(self) -> None:
        """The truncation exonerates six citations of files that do not exist."""
        mutant = load_mutated(
            (
                "    left, right = start, end\n"
                "    while left > 0 and text[left - 1] in TOKEN_EDGE_CHARS:\n"
                "        left -= 1\n"
                "    while right < len(text) and text[right] in TOKEN_EDGE_CHARS:\n"
                "        right += 1\n"
                "    return text[left:right]",
                "    return text[start:end]",
            )
        )
        report = self.audit_with(
            mutant, {"tex/g.tex": GLUED_TEX}, tracked=["IsingModel/X/Y.lean"]
        )
        self.assertEqual(report.findings, [])
        self.assertEqual(report.counts["tex/g.tex"][mutant.RESOLVED], 7)

    # 2b - the indented tree heading
    def test_stripping_the_wrap_prefix_rebuilds_a_path_from_indentation(self) -> None:
        """``strip`` instead of ``rstrip`` joins a tree heading to its entry."""
        mutant = load_mutated(
            (
                "            candidate = scan_text.rstrip()",
                "            candidate = scan_text.strip()",
            )
        )
        report = self.audit_with(
            mutant,
            {"tex/g.tex": INDENTED_PREFIX_TEX},
            tracked=["IsingModel/Inequalities/GKS.lean"],
        )
        self.assertEqual(report.findings, [])
        self.assertEqual(report.counts["tex/g.tex"][mutant.RESOLVED], 1)

    # 7 - escapes
    def test_dropping_unescape_invents_a_false_finding(self) -> None:
        """Proves the unescape step is exercised rather than incidental."""
        mutant = load_mutated((r'text.replace("\\_", "_")', r'text.replace("\\_", "\\_")'))
        report = self.audit_with(
            mutant, {"tex/g.tex": ESCAPE_TEX}, tracked=["IsingModel/Foo/Bar_Baz.lean"]
        )
        self.assertEqual(report.counts["tex/g.tex"][mutant.RESOLVED], 0)

    # 8 - the coverage audit
    def test_disabling_the_coverage_comparison_passes_an_uncovered_variant(self) -> None:
        """This is the mutation the whole design exists to make impossible to miss.

        Both levels have to go: the per-line comparison and the per-file totals.
        That is the point of having two.
        """
        mutant = load_mutated(
            ("            if captured != raw:", "            if False:"),
            ("    if captured_total != raw_total:", "    if False:"),
        )
        report = self.audit_with(
            mutant,
            {"tex/g.tex": UNCOVERED_TEX + BARE_TEX},
            tracked=["IsingModel/A.lean"],
        )
        # The mutant loses one of the two occurrences and still calls itself a
        # trustworthy run -- the exact artefact ("N dangling, all clean") that
        # this guard exists to make impossible.
        self.assertEqual(report.coverage, [])
        self.assertTrue(report.ok_structurally)
        self.assertEqual(report.raw_occurrences["tex/g.tex"], 2)
        self.assertEqual(report.citations["tex/g.tex"], 1)

    # 8b - suppression of the count-of-record
    def test_an_ungated_tsv_publishes_a_census_from_an_incomplete_run(self) -> None:
        """The suppression has to live where the numbers get quoted from."""
        mutant = load_mutated(
            (
                "    if not report.ok_structurally:\n        lines.append(\"#\")",
                "    if False:\n        lines.append(\"#\")",
            )
        )
        with fixture(
            {"tex/g.tex": UNCOVERED_TEX + BARE_TEX},
            tracked=["IsingModel/A.lean"],
            module=mutant,
        ):
            _, out = run_main(mutant, "--targets", "tex/g.tex", "--format", "tsv")
        self.assertIn("#census", out)
        self.assertIn("Foo/Gone.lean", out)

    def test_an_ungated_text_report_publishes_a_census_beside_a_hard_failure(self) -> None:
        """The human report must refuse for the same reason the TSV does."""
        mutant = load_mutated(
            (
                '    if report.ok_structurally:\n        out.append("")',
                '    if True:\n        out.append("")',
            )
        )
        with fixture(
            {"tex/g.tex": BARE_TEX},
            tracked=[".self-local/benchmarks/IsingModel/Foo/Gone.lean"],
            module=mutant,
        ):
            _, out = run_main(mutant, "--targets", "tex/g.tex")
        self.assertIn("RESOLVED=1", out)

    def test_the_file_total_backstops_the_per_line_comparison(self) -> None:
        """Removing only the per-line check still fails the run."""
        mutant = load_mutated(("            if captured != raw:", "            if False:"))
        report = self.audit_with(
            mutant, {"tex/g.tex": UNCOVERED_TEX}, tracked=["IsingModel/A.lean"]
        )
        self.assertTrue(report.coverage)
        self.assertFalse(report.ok_structurally)

    # 9 - resolution set
    def test_walking_the_filesystem_exonerates_untracked_copies(self) -> None:
        """Measured: a walk sees 112,420 ``.lean`` files, the index 2,018."""
        mutant = load_mutated(
            (
                '    out = _git(["ls-files", "-z", "--", "*.lean"])\n'
                "    return sorted(path for path in out.split(\"\\0\") if path)",
                "    import os\n"
                "    found = []\n"
                "    for base, _dirs, names in os.walk(str(REPO_ROOT)):\n"
                "        if '.git' in base:\n            continue\n"
                "        for name in names:\n"
                "            if name.endswith('.lean'):\n"
                "                found.append(\n"
                "                    os.path.relpath(os.path.join(base, name), str(REPO_ROOT)))\n"
                "    return sorted(found)",
            )
        )
        report = self.audit_with(
            mutant,
            {"tex/g.tex": BARE_TEX},
            tracked=["IsingModel/A.lean"],
            untracked=["IsingModel/Foo/Gone.lean"],
        )
        self.assertEqual(tokens_of(report, mutant.MISSING), [])

    def test_dropping_the_prefix_assertion_accepts_a_benchmark_copy(self) -> None:
        """R10 is what keeps a tracked copy of the tree from widening the set."""
        mutant = load_mutated(
            (
                "            if resolved_path is not None and not resolved_path.startswith(\n"
                "                ALLOWED_TRACKED_PREFIXES\n            ):",
                "            if False:",
            )
        )
        report = self.audit_with(
            mutant,
            {"tex/g.tex": BARE_TEX},
            tracked=[".self-local/benchmarks/IsingModel/Foo/Gone.lean"],
        )
        self.assertEqual(report.hard, [])

    # 10 - vacuity
    def test_disabling_the_citation_floor_passes_an_empty_scan(self) -> None:
        """Lowering a floor is the cheapest way to disarm the tool."""
        mutant = load_mutated(("        if len(citations) < floor:", "        if False:"))
        report = self.audit_with(
            mutant,
            {"tex/g.tex": BARE_TEX},
            tracked=["IsingModel/A.lean"],
            MIN_CITATIONS={"tex/g.tex": 50},
        )
        self.assertEqual(report.hard, [])

    def test_disabling_the_empty_target_guard_passes_a_run_that_did_nothing(self) -> None:
        """An audit of no documents must never be a pass."""
        mutant = load_mutated(("    if not visited:", "    if False:"))
        with fixture({"tex/g.tex": BARE_TEX}, tracked=["IsingModel/A.lean"], module=mutant):
            report = mutant.audit([])
        self.assertEqual(report.hard, [])
        self.assertTrue(report.ok_structurally)

    # 11 - self-reference
    def test_shrinking_the_cue_list_misses_a_self_reference(self) -> None:
        """Documented as under-detecting; the test pins how much it detects today."""
        mutant = load_mutated(
            (
                r'r"re-exported|legacy|split into|former split|merged into|now lives in"',
                r'r"__no_such_cue__"',
            )
        )
        report = self.audit_with(
            mutant, {"tex/g.tex": SELFREF_TEX}, tracked=["IsingModel/A/X.lean"]
        )
        self.assertEqual(report.selfrefs, [])

    def test_dropping_the_suffix_relation_misses_a_self_reference(self) -> None:
        """The two citations must be recognised as the same file."""
        mutant = load_mutated(
            (
                "    return first[-length:] == second[-length:]",
                "    return False",
            )
        )
        report = self.audit_with(
            mutant, {"tex/g.tex": SELFREF_TEX}, tracked=["IsingModel/A/X.lean"]
        )
        self.assertEqual(report.selfrefs, [])

    # 12b - the baseline's target set
    def test_without_the_target_check_a_partial_run_shrinks_the_baseline(self) -> None:
        """One ``--targets`` run would drop the other target's rows for good."""
        mutant = load_mutated(
            ("    if set(report.visited) != set(TARGETS):", "    if False:")
        )
        with fixture(
            {"tex/a.tex": BARE_TEX, "tex/b.tex": BASENAME_TEX},
            tracked=["IsingModel/Foo/Bar.lean"],
            module=mutant,
            TARGETS=("tex/a.tex", "tex/b.tex"),
            MIN_CITATIONS={"tex/a.tex": 1, "tex/b.tex": 1},
        ) as root:
            code, _ = run_main(
                mutant, "--targets", "tex/a.tex", "--update-baseline", "audit/base.tsv"
            )
            written = (root / "audit" / "base.tsv").read_text(encoding="utf-8")
        self.assertEqual(code, 0)
        self.assertIn("tex/a.tex", written)
        self.assertNotIn("tex/b.tex", written)

    # 13 - the frozen corpus
    def test_a_relaxed_resolution_rule_moves_the_frozen_corpus_census(self) -> None:
        """The pin's whole claim: an extractor change is a diff in expected.tsv.

        Two weakenings the ratchet is blind to -- accepting a bare basename, and
        dropping the boundary widening so glued spellings resolve -- both of
        which look like remediation in the debt total (findings fall) and are
        caught here because the frozen corpus says otherwise.
        """
        expected = baseline_body((CORPUS_DIR / "expected.tsv").read_text(encoding="utf-8"))
        mutants = {
            "basenames accepted": (
                '    if "/" not in token:\n        return (BASENAME_ONLY, None)',
                "    if False:\n        return (BASENAME_ONLY, None)",
            ),
            "glued text truncated": (
                "    left, right = start, end\n"
                "    while left > 0 and text[left - 1] in TOKEN_EDGE_CHARS:\n"
                "        left -= 1\n"
                "    while right < len(text) and text[right] in TOKEN_EDGE_CHARS:\n"
                "        right += 1\n"
                "    return text[left:right]",
                "    return text[start:end]",
            ),
        }
        for name, substitution in mutants.items():
            with self.subTest(mutation=name):
                mutant = load_mutated(substitution)
                report = corpus_report(mutant)
                self.assertNotEqual(baseline_body(mutant.render_baseline(report)), expected)

    def test_a_mis_attributed_class_breaks_the_partition_identity(self) -> None:
        """The live-run pin that replaced the census equality pin, exercised."""
        mutant = load_mutated(
            (
                "            per_class[verdict] += 1",
                "            per_class[verdict] += 0 if verdict == MALFORMED else 1",
            )
        )
        report = self.audit_with(
            mutant, {"tex/g.tex": GLUED_TEX}, tracked=["IsingModel/X/Y.lean"]
        )
        self.assertNotEqual(
            sum(report.counts["tex/g.tex"][name] for name in mutant.CITATION_CLASSES),
            report.citations["tex/g.tex"],
        )

    # 14 - the update path and the deletion budget
    def test_without_the_growth_refusal_a_grown_baseline_is_written(self) -> None:
        """The laundering hatch, as it actually shipped: print ``+N``, write anyway.

        This is the mutation the whole of :class:`BaselineUpdateTest` exists to
        make impossible to miss, and it is a defect fix rather than a
        hypothetical: before this change the tool computed the growth delta and
        wrote the file regardless.
        """
        mutant = load_mutated(("        if growth:", "        if False:"))
        committed = make_baseline(1, BASE_CENSUS_40, missing_rows(39))
        with fixture(
            {"tex/g.tex": missing_citations_tex(40), "audit/base.tsv": committed},
            tracked=["IsingModel/Corpus/Present.lean"],
            module=mutant,
            commit=True,
            TARGETS=("tex/g.tex",),
            MIN_CITATIONS={"tex/g.tex": 1},
        ) as root:
            code, _ = run_main(
                mutant, "--targets", "tex/g.tex", "--update-baseline", "audit/base.tsv"
            )
            written = (root / "audit" / "base.tsv").read_text(encoding="utf-8")
        self.assertEqual(code, 0)
        self.assertIn("Corpus/Missing39.lean", written)

    def test_judging_an_update_by_the_working_file_lets_a_branch_ratchet_itself(self) -> None:
        """The wrong "previous" side: a PR's own last write becomes its licence."""
        mutant = load_mutated(
            (
                "    for revision in _committed_revisions():\n"
                "        text = _git_committed_text(revision, relative)",
                "    for revision in ['worktree']:\n"
                "        text = (\n"
                "            destination.read_text(encoding='utf-8')\n"
                "            if destination.is_file()\n"
                "            else None\n"
                "        )",
            )
        )
        committed = make_baseline(1, BASE_CENSUS_40, missing_rows(39))
        grown = make_baseline(1, BASE_CENSUS_40, missing_rows(40))
        with fixture(
            {"tex/g.tex": missing_citations_tex(40), "audit/base.tsv": committed},
            tracked=["IsingModel/Corpus/Present.lean"],
            module=mutant,
            commit=True,
            TARGETS=("tex/g.tex",),
            MIN_CITATIONS={"tex/g.tex": 1},
        ) as root:
            (root / "audit" / "base.tsv").write_text(grown, encoding="utf-8")
            code, _ = run_main(
                mutant, "--targets", "tex/g.tex", "--update-baseline", "audit/base.tsv"
            )
        self.assertEqual(code, 0)

    def test_disabling_the_deletion_budget_passes_a_gutted_document(self) -> None:
        """Without R11, deleting the citing prose is the cheapest green run."""
        mutant = load_mutated(("        if committed - now > budget:", "        if False:"))
        committed = make_baseline(1, BASE_CENSUS_40, missing_rows(40))
        with fixture(
            {"tex/g.tex": missing_citations_tex(2), "audit/base.tsv": committed},
            tracked=["IsingModel/Corpus/Present.lean"],
            module=mutant,
            MIN_CITATIONS={"tex/g.tex": 1},
        ):
            code, out = run_main(
                mutant, "--targets", "tex/g.tex", "--baseline", "audit/base.tsv"
            )
        self.assertEqual(code, 0)
        self.assertIn("38 finding(s) cleared", out)

    # 12 - the ratchet
    def test_comparing_totals_hides_a_fix_paired_with_a_regression(self) -> None:
        """The reason the baseline is a multiset and not a number."""
        mutant = load_mutated(
            (
                "    for key, count in sorted(current.items()):\n"
                "        allowed = baseline.get(key, 0)",
                "    if sum(current.values()) > sum(baseline.values()):\n"
                "        return ([\"NEW total\"], 0)\n"
                "    for key, count in sorted(current.items()):\n"
                "        allowed = count",
            )
        )
        baseline = Counter({(ca.MISSING, "t", "A.lean"): 2})
        current = Counter({(ca.MISSING, "t", "A.lean"): 1, (ca.MISSING, "t", "B.lean"): 1})
        regressions, _ = mutant.ratchet(current, baseline)
        self.assertEqual(regressions, [])


# ---------------------------------------------------------------------------
# Real-tree pins
# ---------------------------------------------------------------------------


class RealTreePinTest(unittest.TestCase):
    """Claims about this repository, so the committed numbers cannot drift silently."""

    def test_coverage_is_clean_on_both_live_targets(self) -> None:
        """Today every raw ``.lean`` occurrence in both documents is accounted for,
        which is what makes the guard bite on the very next uncovered variant."""
        self.assertEqual(live_report().coverage, [])

    def test_no_hard_failure_on_the_live_tree(self) -> None:
        """The targets exist, are tracked, and resolve inside the owned prefixes."""
        self.assertEqual(live_report().hard, [])

    def test_the_class_census_partitions_the_citations(self) -> None:
        """Attribution pin, and it survives every edit to the documents.

        This is half of what replaced the census *equality* pin. That pin
        asserted ``extractor(live documents) == frozen numbers``, which is two
        claims -- the extractor did not change, and the documents did not change
        -- and only the first was ever wanted; the second made every remediation
        commit fail by construction. What is checked here holds whatever the
        documents say: every citation lands in exactly one class (the decision
        table is total and closed), so the classes have to add up to the
        citations. The other half is :class:`FrozenCorpusTest`.
        """
        report = live_report()
        for target in report.visited:
            self.assertEqual(
                sum(report.counts[target][name] for name in ca.CITATION_CLASSES),
                report.citations[target],
                target,
            )
            # SELFREF counts paragraphs, not citations, so it must *not* be in
            # that sum; a mutation that folded it in would double-count.
            self.assertEqual(report.counts[target][ca.SELFREF],
                             len([f for f in report.selfrefs if f.target == target]))

    def test_every_raw_occurrence_is_matched_or_acknowledged(self) -> None:
        """The coverage arithmetic, pinned on its addends rather than its result.

        ``matched + acknowledged == raw`` is what the coverage audit enforces
        line by line; asserting it on the published totals is what would catch
        an acknowledgement list that had quietly turned into a wildcard --
        coverage stays green in that case, because everything is "explained",
        while real citations stop being charged.
        """
        report = live_report()
        for target in report.visited:
            accounting = report.accounting[target]
            self.assertEqual(
                accounting["matched"] + accounting["acknowledged"], accounting["raw"], target
            )
            self.assertEqual(accounting["raw"], report.raw_occurrences[target], target)
            # Brace expansion is the only step that adds, so it is the only
            # direction in which citations may exceed the matches.
            self.assertGreaterEqual(report.citations[target], accounting["matched"], target)
            self.assertLess(accounting["acknowledged"], accounting["raw"] // 2, target)

    def test_the_rows_add_up_to_the_class_census(self) -> None:
        """Aggregation pin: the baseline rows are the findings, regrouped.

        A key or multiplicity lost in :func:`aggregate` would shrink the
        recorded debt without fixing anything, and the ratchet -- which reads
        only the rows -- could not see it.
        """
        report = live_report()
        rows: Counter = Counter()
        for row in ca.aggregate(list(report.findings) + list(report.selfrefs)):
            rows[(row.target, row.cls)] += row.count
        for target in report.visited:
            for name in ca.ALL_CLASSES:
                if name == ca.RESOLVED:
                    continue  # silent by design: resolved citations carry no row
                self.assertEqual(
                    rows.get((target, name), 0), report.counts[target][name], f"{target}/{name}"
                )

    def test_the_live_run_is_at_the_baseline(self) -> None:
        """The committed baseline is the current state, not an aspiration."""
        report = live_report()
        current: Counter = Counter()
        for row in ca.aggregate(list(report.findings)):
            current[(row.cls, row.target, row.token)] = row.count
        baseline, _, _ = ca.read_baseline(ca.BASELINE_FILE)
        gating = Counter(
            {key: count for key, count in baseline.items() if key[0] in ca.FINDING_CLASSES}
        )
        regressions, _ = ca.ratchet(current, gating)
        self.assertEqual(regressions, [])

    def test_the_citation_floors_are_backstops_against_the_committed_census(self) -> None:
        """A floor set to zero guards nothing; a floor set just below the live
        value is a document freeze.

        Measured against the **committed census** rather than the live run, so
        the pin stops moving when the documents are edited -- which is exactly
        the property the census equality pin lacked. The band says what the
        floor is for: far enough below to let ordinary remediation delete stale
        citations (that is the drop budget's job, one hundredth of the distance
        away), high enough that a gutted document still trips it.
        """
        _, census, _ = ca.read_baseline(ca.BASELINE_FILE)
        for target in ca.TARGETS:
            floor = ca.MIN_CITATIONS[target]
            committed = census[target]["citations"]
            self.assertGreaterEqual(floor, 0.40 * committed, target)
            self.assertLessEqual(floor, 0.75 * committed, target)

    def test_the_tracked_floor_is_below_but_close_to_the_live_value(self) -> None:
        """``MIN_TRACKED_LEAN`` is about the Lean tree, which remediation does not
        touch, so it stays pinned tightly against the live value."""
        report = live_report()
        self.assertLessEqual(ca.MIN_TRACKED_LEAN, report.tracked)
        self.assertGreaterEqual(ca.MIN_TRACKED_LEAN, 0.75 * report.tracked)

    def test_the_committed_baseline_carries_a_census_for_every_default_target(self) -> None:
        """Deleting a ``#census`` line would disarm R11 for that target.

        The runtime charges that only for a target the baseline still carries
        rows for (:func:`erosion_failures` explains why); the claim that the
        *default* targets always have one belongs here, against the committed
        file itself.
        """
        _, census, tracked = ca.read_baseline(ca.BASELINE_FILE)
        self.assertEqual(set(ca.TARGETS) - set(census), set())
        self.assertEqual(tracked, ca.tracked_lean_files().__len__())
        for target in ca.TARGETS:
            self.assertGreater(census[target]["citations"], 0, target)
            self.assertGreater(census[target]["raw"], 0, target)

    def test_the_deletion_budget_is_calibrated_against_the_committed_census(self) -> None:
        """The guard that actually fires per commit, with its numbers stated.

        Big enough that a real remediation pass (207 citations repointed, 44
        stale ones removed, measured) is not blocked, small enough that a
        document cannot be emptied a few dozen citations at a time without
        someone saying so in a diff.
        """
        _, census, _ = ca.read_baseline(ca.BASELINE_FILE)
        budgets = {
            target: ca.citation_drop_budget(census[target]["citations"]) for target in ca.TARGETS
        }
        self.assertEqual(
            budgets, {"tex/proof-guide.tex": 66, "docs/index.md": 134}
        )
        for target, budget in budgets.items():
            committed = census[target]["citations"]
            self.assertGreater(budget, 44, target)
            self.assertLess(committed - budget, committed, target)
            self.assertGreater(committed - budget, ca.MIN_CITATIONS[target], target)
        # A budget that is a constant stops meaning anything as the document
        # shrinks; a budget without a floor freezes a small target.
        self.assertEqual(ca.citation_drop_budget(0), ca.MIN_CITATION_DROP_BUDGET)
        self.assertEqual(ca.citation_drop_budget(10_000), 500)

    def test_every_allowed_prefix_matches_tracked_files(self) -> None:
        """A dead prefix is a review signal, exactly as in ``ScopeCoverageTest``."""
        tracked = ca.tracked_lean_files()
        for prefix in ca.ALLOWED_TRACKED_PREFIXES:
            self.assertTrue(
                any(path.startswith(prefix) for path in tracked), f"dead prefix {prefix}"
            )

    def test_default_targets_are_the_published_documents(self) -> None:
        """Shrinking ``TARGETS`` would make the tool pass by looking away."""
        self.assertEqual(ca.TARGETS, ("tex/proof-guide.tex", "docs/index.md"))

    def test_every_default_target_has_a_measured_floor(self) -> None:
        """A default target without a floor would fall back to the floor of one."""
        self.assertEqual(set(ca.TARGETS) - set(ca.MIN_CITATIONS), set())

    def test_the_tool_passes_on_the_current_tree(self) -> None:
        """End to end: the committed baseline plus today's documents exit 0."""
        code, out = run_main(ca)
        self.assertEqual(code, 0, out)
        self.assertIn("citation audit: PASS", out)


def run_suite() -> int:
    """Run every test. Return ``0`` on success, ``1`` otherwise."""
    loader = unittest.TestLoader()
    suite = loader.loadTestsFromModule(sys.modules[__name__])
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(run_suite())
