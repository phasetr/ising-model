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
glued to a match (``../X/Y.lean``, ``X/Y.lean.bak``), a directive read from a
quotation instead of from a comment, a directive that outlived the block it was
written for, an indented tree entry joined onto the heading above it, a census
published from a provably incomplete run, and a baseline rewritten from a
partial target set.

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
    **overrides: object,
) -> Iterator[Path]:
    """Build a throwaway repository and point the checker at it.

    ``documents`` maps a repository-relative path to its text; ``tracked`` lists
    ``.lean`` paths that are staged (and therefore resolvable); ``untracked``
    lists ``.lean`` paths written to disk but never staged, which is how "the
    filesystem is not the resolution set" is tested; ``tags`` maps a tag name to
    the ``.lean`` paths that exist *only* in that tag.

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
# 4 - archive tags and directives
# ---------------------------------------------------------------------------


ARCHIVED_TEX = "\\texttt{Peierls/RayExitAnchor.lean} was the old route.\n"

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


class ArchiveTagTest(unittest.TestCase):
    """An archive tag resolves nothing unless the document asks for it, in place."""

    def test_a_tagged_path_alone_does_not_resolve(self) -> None:
        """Measured: unconditional tag resolution exonerates 276 of 280 no-match
        citations, so the mechanism does not exist."""
        with fixture({"tex/g.tex": ARCHIVED_TEX}, tags=STUB_TAG):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(classes(report, "tex/g.tex"), {"MISSING": 1})

    def test_verified_directive_resolves_that_one_citation(self) -> None:
        """The exemption is written per citation and checked against the tag."""
        with fixture({"tex/g.tex": DIRECTIVE_TEX}, tags=STUB_TAG):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(classes(report, "tex/g.tex"), {"RESOLVED_BY_DIRECTIVE": 1})
        self.assertEqual(report.findings, [])

    def test_directive_naming_an_absent_path_is_a_finding(self) -> None:
        """A wrong exemption is a finding, not a pass (R12)."""
        with fixture({"tex/g.tex": DIRECTIVE_WRONG_TEX}, tags=STUB_TAG):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(classes(report, "tex/g.tex"), {"MISSING": 1})

    def test_directive_naming_an_unknown_tag_is_a_finding(self) -> None:
        """An unknown tag cannot verify anything, so nothing is exempted."""
        with fixture({"tex/g.tex": DIRECTIVE_TEX}):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(classes(report, "tex/g.tex"), {"MISSING": 1})

    def test_prefix_directive_resolves_a_block_of_basenames(self) -> None:
        """The tree blocks get a written, verified prefix instead of a guess."""
        with fixture({"tex/g.tex": PREFIX_TEX}, tracked=["IsingModel/Inequalities/GKS.lean"]):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(classes(report, "tex/g.tex"), {"RESOLVED_BY_DIRECTIVE": 1})

    def test_wrong_prefix_directive_is_a_finding(self) -> None:
        """A prefix that does not lead to a tracked file resolves nothing."""
        with fixture({"tex/g.tex": PREFIX_TEX}, tracked=["IsingModel/Peierls/GKS.lean"]):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(classes(report, "tex/g.tex"), {"MISSING": 1})

    def test_unparseable_directive_grants_nothing(self) -> None:
        """A typo in the directive keyword must not become a silent exemption."""
        text = DIRECTIVE_TEX.replace("archived", "arcived")
        with fixture({"tex/g.tex": text}, tags=STUB_TAG):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(classes(report, "tex/g.tex"), {"MISSING": 1})

    def test_a_quoted_directive_is_not_an_instruction(self) -> None:
        """Writing *about* the syntax must not arm it.

        The pattern used to match anywhere on a line, so transcribing this
        tool's own documentation into a document -- mid-sentence, inside
        ``\\texttt{...}``, inside a sample block -- exempted the next citation
        for real. A directive is now read only from a line that is itself a
        comment in that document's syntax.
        """
        for target, text in (
            ("tex/g.tex", DIRECTIVE_QUOTED_TEX),
            ("docs/g.md", DIRECTIVE_QUOTED_MD),
        ):
            with self.subTest(target=target):
                with fixture(
                    {target: text}, tracked=["IsingModel/Inequalities/GKS.lean"]
                ):
                    report = ca.audit([target])
                self.assertEqual(classes(report, target), {"BASENAME_ONLY": 1})

    def test_a_markdown_comment_directive_is_honoured(self) -> None:
        """The comment rule must still let a real directive through, in both syntaxes.

        Without this the markdown half of the rule could be spelled so that it
        never matches and every test would stay green -- a check that only ever
        refuses is indistinguishable from one that is broken.
        """
        with fixture({"docs/g.md": DIRECTIVE_MD}, tracked=["IsingModel/Inequalities/GKS.lean"]):
            report = ca.audit(["docs/g.md"])
        self.assertEqual(classes(report, "docs/g.md"), {"RESOLVED_BY_DIRECTIVE": 1})

    def test_a_directive_inside_a_verbatim_block_is_content(self) -> None:
        """A sample document printed in a block exempts nothing in the real one."""
        with fixture(
            {"tex/g.tex": DIRECTIVE_IN_VERBATIM_TEX},
            tracked=["IsingModel/Inequalities/GKS.lean"],
        ):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(classes(report, "tex/g.tex"), {"BASENAME_ONLY": 1})

    def test_a_directive_expires_when_its_subject_is_gone(self) -> None:
        """An exemption must not outlive the block it was written for.

        Nothing bounded the wait, so a directive left behind by a deletion armed
        whatever citation appeared next -- dozens of lines later, in a passage
        nobody wrote it for. It now expires at the first non-blank line that
        carries no citation.
        """
        with fixture({"tex/g.tex": DIRECTIVE_ORPHANED_TEX}, tags=STUB_TAG):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(classes(report, "tex/g.tex"), {"MISSING": 1})

    def test_a_blank_line_does_not_expire_a_directive(self) -> None:
        """The rule is "the next line with citations", not "the next line".

        Pinned because it is the boundary of the expiry rule: paragraph spacing
        between a directive and its citation is ordinary formatting and must
        keep working, or authors would learn to distrust the mechanism.
        """
        with fixture({"tex/g.tex": DIRECTIVE_BLANK_LINE_TEX}, tags=STUB_TAG):
            report = ca.audit(["tex/g.tex"])
        self.assertEqual(classes(report, "tex/g.tex"), {"RESOLVED_BY_DIRECTIVE": 1})


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
                ca, "--targets", "tex/g.tex", "--write-baseline", "audit/base.tsv"
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
                ca, "--targets", "tex/g.tex", "--write-baseline", "audit/base.tsv"
            )
            # Inside the fixture: the temporary tree is gone once it exits, so
            # this assertion would hold for the wrong reason outside it.
            self.assertFalse((root / "audit" / "base.tsv").exists())
        self.assertEqual(code, 1)
        self.assertIn("refusing to write a baseline", out)

    def test_baseline_is_not_written_from_a_partial_target_set(self) -> None:
        """``--targets`` plus ``--write-baseline`` must not shrink the record.

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
                ca, "--targets", "tex/a.tex", "--write-baseline", "audit/base.tsv"
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
    def test_unconditional_tag_resolution_exonerates(self) -> None:
        """The mechanism measured at 276/280 fail-open, reintroduced and caught."""
        mutant = load_mutated(
            (
                "    hits = resolver.matches(token)\n    if len(hits) == 0:\n        return (MISSING, None)",
                "    hits = resolver.matches(token)\n    if len(hits) == 0:\n"
                "        tagged = resolver.tag_matches('archive/stub', token)\n"
                "        if tagged:\n            return (RESOLVED_BY_DIRECTIVE, None)\n"
                "        return (MISSING, None)",
            )
        )
        report = self.audit_with(mutant, {"tex/g.tex": ARCHIVED_TEX}, tags=STUB_TAG)
        self.assertEqual(report.findings, [])

    # 4b - directive verification
    def test_unverified_directive_exonerates_an_absent_path(self) -> None:
        """A directive that is trusted instead of checked is just a comment."""
        mutant = load_mutated(
            (
                '        if hits is not None and len(hits) == 1 and "/" in token:',
                "        if True:",
            )
        )
        report = self.audit_with(mutant, {"tex/g.tex": DIRECTIVE_WRONG_TEX}, tags=STUB_TAG)
        self.assertEqual(report.findings, [])

    # 4c - directive scope
    def test_a_directive_matched_anywhere_arms_a_quotation(self) -> None:
        """Dropping the comment test turns documentation into an exemption."""
        mutant = load_mutated(
            (
                "    if not (TEX_COMMENT if is_tex else MD_COMMENT).match(line):\n"
                "        return None",
                "    if False:\n        return None",
            )
        )
        report = self.audit_with(
            mutant,
            {"tex/g.tex": DIRECTIVE_QUOTED_TEX},
            tracked=["IsingModel/Inequalities/GKS.lean"],
        )
        self.assertEqual(report.findings, [])

    def test_a_directive_read_inside_a_block_exempts_its_sample(self) -> None:
        """Without the block test, a printed sample document exempts for real."""
        mutant = load_mutated(
            (
                "        found = None if (verbatim_line or in_fence) "
                "else parse_directive(line, is_tex)",
                "        found = parse_directive(line, is_tex)",
            )
        )
        report = self.audit_with(
            mutant,
            {"tex/g.tex": DIRECTIVE_IN_VERBATIM_TEX},
            tracked=["IsingModel/Inequalities/GKS.lean"],
        )
        self.assertEqual(report.findings, [])

    def test_a_directive_that_never_expires_drifts_onto_a_later_citation(self) -> None:
        """The orphaned directive silently exempts a passage nobody wrote it for."""
        mutant = load_mutated(
            (
                "        elif (\n            pending_directive is not None\n"
                "            and not carried",
                "        elif (\n            False\n            and not carried",
            )
        )
        report = self.audit_with(mutant, {"tex/g.tex": DIRECTIVE_ORPHANED_TEX}, tags=STUB_TAG)
        self.assertEqual(report.findings, [])

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
            ("        if set(report.visited) != set(TARGETS):", "        if False:")
        )
        with fixture(
            {"tex/a.tex": BARE_TEX, "tex/b.tex": BASENAME_TEX},
            tracked=["IsingModel/Foo/Bar.lean"],
            module=mutant,
            TARGETS=("tex/a.tex", "tex/b.tex"),
            MIN_CITATIONS={"tex/a.tex": 1, "tex/b.tex": 1},
        ) as root:
            code, _ = run_main(
                mutant, "--targets", "tex/a.tex", "--write-baseline", "audit/base.tsv"
            )
            written = (root / "audit" / "base.tsv").read_text(encoding="utf-8")
        self.assertEqual(code, 0)
        self.assertIn("tex/a.tex", written)
        self.assertNotIn("tex/b.tex", written)

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

    def test_class_census_matches_the_committed_baseline(self) -> None:
        """A change in the extractor shows up here, not only in the debt total."""
        report = live_report()
        _, census, tracked = ca.read_baseline(ca.BASELINE_FILE)
        self.assertEqual(tracked, report.tracked)
        for target in report.visited:
            recorded = census[target]
            self.assertEqual(recorded["citations"], report.citations[target])
            self.assertEqual(recorded["raw"], report.raw_occurrences[target])
            for name in ca.ALL_CLASSES:
                self.assertEqual(
                    recorded.get(name, 0), report.counts[target][name], f"{target}/{name}"
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

    def test_floors_are_below_but_close_to_the_live_values(self) -> None:
        """A floor set to zero passes "the floor exists" and guards nothing."""
        report = live_report()
        self.assertLessEqual(ca.MIN_TRACKED_LEAN, report.tracked)
        self.assertGreaterEqual(ca.MIN_TRACKED_LEAN, 0.75 * report.tracked)
        for target in ca.TARGETS:
            floor = ca.MIN_CITATIONS[target]
            self.assertLessEqual(floor, report.citations[target])
            self.assertGreaterEqual(floor, 0.75 * report.citations[target])

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
