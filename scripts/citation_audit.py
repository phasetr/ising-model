#!/usr/bin/env python3
"""Fail-closed audit of ``.lean`` path citations in the audited documents.

``docs/index.md`` names Lean source files by path, and it is the one target
today; the tool takes a set of them so a second document can be added without
touching the rules. Refactors move and delete those files, so a document
accumulates citations
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
R11  citations lost since the committed census, beyond budget    hard failure ``ERODED``
R12  citations lost since the frozen measurement, beyond the cap  hard failure ``ERODED``
===  =========================================================  =========================

``RESOLVED`` is silent; ``MISSING``, ``AMBIGUOUS``, ``BASENAME_ONLY`` and
``MALFORMED`` are findings and gate the exit code through the baseline ratchet.
``SELFREF`` (below) is advisory. The table is total and it is closed: a citation
lands in exactly one row, and there is no row a document can put itself into.

The baseline file has three roles
---------------------------------
``scripts/audit/citation_baseline.tsv`` carries three kinds of number, and each
obeys a *different* rule. Conflating them is what made the first version of this
file's ``#census`` pin unusable (see below).

=============================  ===============================================
gating rows                    the ratchet, per ``(class, target, token)`` key,
                               monotone non-increase. The **only** part the exit
                               code reads.
``#census`` per-class counts   derived book-keeping, refreshed by
                               ``--update-baseline``. No rule of its own: what
                               is checked instead is the identity
                               ``citations == sum over the citation classes``,
                               on the live run, where it holds whatever the
                               documents say.
``#census`` ``citations`` /    the **per-run deletion budget** (R11). Remediation
``raw``                        may delete a stale citation, and the ratchet is
                               blind to that -- a deleted citation is
                               indistinguishable from a cleared finding -- so this
                               is where content loss is charged *per run*.
=============================  ===============================================

Why the cumulative cap is a frozen constant and not the census
--------------------------------------------------------------
R11 alone is not a brake on erosion, because ``--update-baseline`` rewrites the
``#census`` from the live run: each accepted deletion lowers the reference the
*next* run is judged against, so a budget of 5% compounds. Measured on the
retired proof guide's numbers, twelve within-budget updates take it from 1,333
citations to 723 -- a
46% loss, deletions of 66, 63, 60, ... 38 -- with no hard failure at any step
and ``ratchet: OK`` reported throughout, because deleting the citing sentence
clears its finding. Only the thirteenth is stopped, and only by the floor.

The cumulative cap (R12) is therefore charged against
:data:`MEASURED_CITATIONS`, a constant frozen in this file, and never against
anything a run can rewrite. That is also why the floors' sanity band is
expressed against the same constant in the test suite: a band anchored on the
committed census follows the erosion down, so once the census has drifted far
enough the suite turns red and the cheapest way to green it is to *lower the
floor* -- the tool asking to be disarmed. A guard whose reference point moves
with the thing it guards is not a guard.

Re-anchoring ``MEASURED_CITATIONS`` after a large, legitimate remediation is a
hand edit of this file plus the test that pins it, in one reviewable commit --
the same control the baseline's own growth uses, and deliberately not something
``--update-baseline`` can do.

An **equality** pin of the whole census against the live documents was tried
first and removed. Its intent was right (notice a silent change in the
*extractor*, which the ratchet cannot see because a relaxed resolution rule looks
exactly like remediation) but its input was wrong: with mutable documents,
``extractor(live documents) == frozen numbers`` also asserts that the documents
did not change, so it fails on every remediation commit by construction. It was
a document freeze wearing an extractor pin's clothes. What it was meant to pin is
pinned instead on a **frozen corpus**, ``scripts/audit/citation_corpus/``, whose
expected census is committed and which no edit to an audited document can move.

Updating the baseline
---------------------
``--update-baseline`` regenerates the rows from the current run, which is the one
operation that can retire a finding without fixing a citation. It therefore
refuses, and has **no override flag**, when:

* the run is not structurally sound, or scanned only some of the targets (a
  partial run would drop the unscanned target's rows for good);
* any key's count would be **higher** than in the committed baseline, compared
  against the strictest committed copy available (``merge-base(HEAD,
  origin/main)``, ``origin/main`` and ``HEAD``) rather than against the file in
  the working tree, so a branch cannot ratchet against its own earlier write;
* **any of those three revisions cannot be read**, which is a separate outcome
  from "that revision has no such file". Without the distinction the strictest
  copy degenerates silently: in a clone with no ``origin/main`` -- the default
  ``actions/checkout``, ``--depth 1`` and ``--single-branch`` all produce one --
  the comparison would fall back to ``HEAD`` alone, i.e. the branch's own
  previous commit, and a branch could re-arm the budget once per commit. If
  *no* revision could be read the fallback is worse still: it looks like "no
  committed copy at all", which is the bootstrap path, and that path disables
  the growth refusal and R11 together. Both are refused instead. The
  ``git show`` used to read a copy cannot tell the two apart (it exits non-zero
  for either), so the revision is separately resolved with ``git rev-parse
  --verify``, and at least two resolvable revisions are required;
* **fewer than two of those revisions actually carry the file.** Resolving a
  revision and holding the baseline are different facts, and only the second
  supplies an allowance. ``origin/main`` can resolve and still predate the commit
  that introduced the path -- a baseline created on this branch, or a stale fetch
  -- and then the one surviving reference is ``HEAD``, the branch's own last
  write, with all three revisions resolving and no refusal raised. Measured at
  review on that gap, with R12 out of the picture: six consecutive within-budget
  updates accepted, 1,000 citations down to 738, ``ratchet: OK`` throughout.
  With R12 armed the same walk is bounded by the cumulative cap instead -- which
  is all that stood behind this. Tree membership is therefore established
  separately (``git ls-tree``), and the "at least two" rule is applied to the
  revisions that *carry* the path, not to the revisions that resolve;
* **the path is in a revision's tree but its content cannot be read** -- a
  partial clone fetches trees without blobs, and a damaged object store looks the
  same. Read as absence, that can empty the carrier set, and an empty carrier set
  is the bootstrap path, which disables the growth refusal and R11 together;
* **a revision spells the destination's path some other way.** Membership is
  asked of a repository-relative, case-sensitive *pathname* while the write lands
  on whatever that name opens: a mis-cased spelling on a case-insensitive
  filesystem (macOS, where ``Path.resolve()`` does not canonicalise case) and a
  path outside the repository each name bytes no tree lists, so the carrier set
  is empty and the bootstrap path is taken while the write still reaches the
  committed file. Measured at review before either was charged: each rewrote a
  committed baseline of 1,000 rows into one of 300, exit 0, no refusal. So each
  revision's tree is listed whole and asked whether it holds a path differing
  from this one only in case. **The filesystem is not consulted**: two earlier
  forms of the check walked the destination's path on disk, and each stopped at
  the first component the worktree did not hold -- once at the leaf, then one
  level up. Measured at review on the second form, with ``scripts/audit`` moved
  aside, ``scripts/audit/Citation_baseline.tsv`` wrote 1,368 rows at exit 0 and
  left the tracked baseline modified, while the honest spelling refused. What
  this bullet does *not* claim is that every mis-cased destination is refused: a
  spelling of a path **no** revision carries under any case is a genuine creation
  and takes the bootstrap path below, where there is no committed allowance to
  launder. A hard link is the third way the two identities come apart, and it is
  not refused -- see below;
* a target lost more citations than R11's budget allows, or R12's cap does.

The write itself renders to a temporary file next to the destination and
replaces it, rather than writing through the name. That is what answers the hard
link: replacing a name detaches it from the inode any other name shares, where a
write through the name would have reached the bytes those other names hold. It
also means the path judged and the path written are one value, resolved once,
instead of two lookups of the same string. The temporary's own name is taken
with ``O_CREAT | O_EXCL`` (``tempfile.mkstemp``) rather than derived from the
destination: a predictable one is the same write-through one step removed --
measured at review, pre-creating ``.<name>.pending`` as a hard link or a symlink
to the tracked baseline landed the render on the committed bytes at exit 0.

**Bootstrapping** -- the one permissive outcome -- is correspondingly narrow, and
is defined positively: at least two revisions resolve, every one of them answered
the membership question, no revision's tree spells the destination's path another
way, and *none* of them lists it in its tree. Then no commit carries the file
under any spelling: there is no allowance to launder yet, and its creation adds a
path no revision had, which ``git status`` shows. "The revisions could not be
read", "the content could not be read", "a revision spells that path otherwise"
and "only this branch carries it" are each a refusal instead. So
an ordinary branch bootstraps a baseline once: after the creating commit,
``HEAD`` carries the file and the upstream does not, and the next update waits
until the file has landed on ``origin/main``. What that bounds is a *forward*
history -- removing the creating commit (a reset, or an amend that drops the
file) returns the branch to the bootstrap state, which the refusal says out
loud; it is a history rewrite, and the re-created file is a new file in the
diff, as a hand edit is a loud one.

The written file is therefore provably per-key ``<=`` a committed copy that at
least two revisions carry. What that does *not* say is that the tool can never
emit a smaller file: ``--format tsv`` renders the same bytes with none of these
refusals, and under a partial ``--targets`` it renders the unscanned target's
rows away. Installing such a file is a hand edit of the committed baseline, and
that is where the control sits -- the diff is loud, and the next gating run
charges every dropped row as a ratchet regression. Growth, and a deletion past
the budget, are likewise possible only as a hand edit, which is the intended
control.

Only the update path needs the committed copies. A gating run reads the working
tree's baseline, so a shallow CI clone still audits and still ratchets; what it
cannot do there is *rewrite* the baseline.

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
    python3 scripts/citation_audit.py --update-baseline PATH
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
class into a gating one. A future wiring commit calls :func:`audit`, adds
:func:`erosion_failures` to ``Report.hard`` (R11 needs the committed baseline,
so :func:`audit` cannot charge it on its own; R12 needs only a constant and is
already in there, which is why forgetting this step leaves the cumulative
tripwire armed and only the per-run one disarmed) and reads ``Report.findings``
(gating), ``Report.coverage`` and ``Report.hard`` (hard failures),
``Report.visited`` (scanned-set honesty) and ``Report.selfrefs`` (advisory, must
not gate) explicitly.

Runtime: Python 3.9 standard library only; no ``lake``, no network.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterable, List, NamedTuple, Optional, Sequence, Set, Tuple

# Repository root = parent of the ``scripts`` directory holding this file.
REPO_ROOT = Path(__file__).resolve().parent.parent
BASELINE_FILE = REPO_ROOT / "scripts" / "audit" / "citation_baseline.tsv"

# Documents whose ``.lean`` citations are audited by default.
TARGETS = ("docs/index.md",)

# Anti-vacuity floors (R8/R9), and **catastrophic backstops only**: they answer
# "was this document gutted", not "was it edited". A target accidentally emptied
# would otherwise report "0 findings, all clean" -- the most convincing possible
# false pass. Lowering these constants is the cheapest way to disarm the whole
# tool, so each move must be deliberate, in the same commit, with a reason.
# Measured on the tree this file was written against: 2,698 citations in the
# markdown, 2,018 tracked .lean files. (The proof guide, 1,333 citations, was a
# second target until it was retired; its floor and measurement went with it.)
#
# Why they sit near half of that and not just below it. A floor close to the
# working value does not guard the tokeniser -- a tokeniser that stops matching
# is caught earlier and more precisely by the coverage audit, whose raw side is
# ``line.count(".lean")`` and never consults ``TOKEN`` -- it guards the document
# *volume*, and at 1,200 it was already deciding the content of a published
# document: the first remediation pass repointed the legacy re-export sentences
# instead of deleting them because deleting them landed at 1,145. That is the
# wrong actor making an editorial decision, and it is structural rather than
# incidental, because the ``SELFREF`` class is *defined* as a duplicated legacy
# citation, so its correct fix always lowers the count. The guard that actually
# fires per commit is the drop budget below; these two are the cliff behind it.
MIN_CITATIONS = {"docs/index.md": 1400}
MIN_TRACKED_LEAN = 1800

# The measurement this tool was written against, frozen (R12). Unlike the
# ``#census``, nothing regenerates these: they are the fixed point the
# *cumulative* loss is measured from, and the module docstring's "Why the
# cumulative cap is a frozen constant" says why that matters -- a cap measured
# from the census would be recomputed from the eroded value on every update and
# would permit an unbounded geometric walk down to the floor.
#
# Charged only for a target listed here, so an ad-hoc ``--targets`` run against
# a document nobody measured is not judged against an invented reference. That
# the *default* targets are all listed is pinned by the test suite.
MEASURED_CITATIONS = {"docs/index.md": 2698}
# The tracked-set half of the same measurement. Nothing charges it at runtime,
# and that is deliberate: remediation edits documents and never deletes ``.lean``
# files, so there is no per-run erosion of the tracked set to bound, and a gutted
# tree is already a hard failure against ``MIN_TRACKED_LEAN`` (R9). What it is
# for is the test suite, where it is the frozen reference the ``#tracked`` band
# and the tracked floor's sanity check are stated against. Those two read the
# *live* count until this constant was wired in, which is the defect R12 exists
# to avoid one level up: a band around the live value reddens when the tree grows
# (ordinary work here) and relaxes as it shrinks (the direction worth guarding).
MEASURED_TRACKED_LEAN = 2018

# How far below the frozen measurement a document may drift in total (R12).
#
# Chosen against the two numbers it has to sit between. Above: the per-run
# budget is 5%, and a cap below ~3 budgeted runs would make R11 unreachable and
# turn every ordinary remediation commit into a re-anchoring ceremony -- which
# is how a frozen constant becomes a rubber stamp. Below: the floors, at ~48%
# loss, are a cliff that twelve compounding 5% runs get to within 23 citations
# of. 15% (404 citations for the markdown) admits three
# consecutive full-budget runs and the whole remediation programme measured so
# far (PR #4730 removed 47 of the retired proof guide's, its batch-1 follow-up 5
# more), and stops that walk at its fourth step.
#
# Exceeding it is not a defect to be forced through: it is the point at which
# somebody re-measures the documents and says so in a diff.
MAX_CUMULATIVE_CITATION_LOSS_FRACTION = 0.15

# Floor applied to a target passed on the command line that has no entry in
# ``MIN_CITATIONS``: auditing a document in which the extractor found nothing at
# all is never a meaningful pass.
DEFAULT_MIN_CITATIONS = 1

# Per-run deletion budget (R11), charged against the committed ``#census``.
#
# The ratchet cannot see a deletion: removing the sentence that carries a
# dangling citation clears the finding exactly as fixing it does. Without a
# budget the only thing standing between "remediation" and "delete the citing
# prose" is the floor above, i.e. a cliff hundreds of citations away, reachable
# by erosion nobody ever reviews. The budget is self-calibrating (a percentage
# of what is committed) with an absolute minimum so that a small target does not
# end up frozen.
#
# Sized against the frozen numbers rather than against today's census, which is
# whatever the last accepted deletion left behind: at ``MEASURED_CITATIONS`` the
# budget is 134 for the markdown (2,698), and at the lowest census R12 can ever
# admit -- ``measured - cap``, i.e. 2,294 -- it is still 114. Both ends clear
# ``MEASURED_REMEDIATION_DROP`` and are
# far below a gutting. The test suite states that as a claim over the whole
# range, so an ordinary remediation commit does not have to restate it.
CITATION_DROP_BUDGET_FRACTION = 0.05
MIN_CITATION_DROP_BUDGET = 25

# The drop measured on the first remediation pass over the proof guide this
# repository then tracked (PR #4730), whose ``#census`` citation count moves
# 1,333 -> 1,286. Frozen, and kept after that document was retired: it is a
# measurement of what a remediation pass costs, which is the same order of work
# on any target.
#
# It is not maintained as a running maximum of what remediation has needed, and
# a later pass that deletes more is not required to update it: it stands as the
# measured pass it names, whatever a later one costs.
# Nothing charges it at runtime -- like ``MEASURED_TRACKED_LEAN`` it is the test
# suite's reference point -- and what it is for is the *lower* side of the
# budget above, which has no other guard: a budget that stops clearing this
# turns the work the tool exists to support into a hard failure, and a guard
# that blocks legitimate work is a guard somebody deletes. Raising it honestly
# is fail-closed in the suite: at or above the low-end budget of 114 the headroom
# claim reddens, which is the point at which the sizing gets restated in a diff.
# 47 leaves 67 of those 114, so a re-measurement much larger than this one is the
# one that has to restate the sizing rather than edit this number again.
MEASURED_REMEDIATION_DROP = 47

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
# The verdict of a citation is exactly one of these, so they partition the
# citations of a target: ``sum(counts[t][c] for c in CITATION_CLASSES) ==
# citations[t]``. ``SELFREF`` is deliberately outside the partition -- it counts
# *paragraphs*, not citations -- which is why the identity names this tuple and
# not ``ALL_CLASSES``.
CITATION_CLASSES = (RESOLVED, MISSING, AMBIGUOUS, BASENAME_ONLY, MALFORMED)
ALL_CLASSES = CITATION_CLASSES + ADVISORY_CLASSES


def citation_drop_budget(committed: int) -> int:
    """Return how many citations a target may lose in one run (R11).

    ``committed`` is the citation count recorded in the baseline's ``#census``
    line for that target, so the budget shrinks with the document instead of
    being a constant that slowly stops meaning anything.

    That self-calibration is also why this cannot be the only brake: the census
    it reads is rewritten by ``--update-baseline``, so the budget is recomputed
    from the value the previous deletion left behind. The bound on the total is
    :func:`cumulative_loss_cap`, which reads a frozen constant instead.
    """
    return max(MIN_CITATION_DROP_BUDGET, int(committed * CITATION_DROP_BUDGET_FRACTION))


def cumulative_loss_cap(measured: int) -> int:
    """Return how far below its frozen measurement a target may drift (R12).

    ``measured`` is :data:`MEASURED_CITATIONS`, not the census: the whole point
    is a reference point no run can move. ``0`` means the target has never been
    measured, and nothing is charged for it -- inventing a reference point would
    be a number nobody reviewed, exactly as in :func:`erosion_failures`.
    """
    return int(measured * MAX_CUMULATIVE_CITATION_LOSS_FRACTION)

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


def extract(target: str, text: str) -> Tuple[List[Citation], List[str], Dict[str, int]]:
    """Extract every citation from a document and audit the extractor's coverage.

    Returns ``(citations, coverage_failures, accounting)``. The second list is
    the keystone guard: it holds one entry per line whose raw ``.lean`` count
    differs from the number of tokens attributed to it, plus one entry if the
    per-file totals disagree (an attribution bug that cancels across lines).

    ``accounting`` is that guard's arithmetic, published rather than discarded:
    ``raw`` occurrences, ``matched`` (``TOKEN`` hits, before brace expansion) and
    ``acknowledged`` (:data:`NON_CITATION` spellings). ``matched + acknowledged
    == raw`` is what the coverage audit enforces, and exposing the two addends
    lets a test pin *how* a document is accounted for -- in particular that the
    acknowledgement list has not quietly become a wildcard that absorbs real
    citations -- without pinning what the document says.

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
    matched_total = 0
    acknowledged_total = 0

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
                    matched_total += 1
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
                acknowledged = acknowledge_non_citations(unescaped, spans)
                captured += acknowledged
                acknowledged_total += acknowledged
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
    accounting = {
        "raw": raw_total,
        "matched": matched_total,
        "acknowledged": acknowledged_total,
    }
    return citations, coverage, accounting


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
    accounting: Dict[str, Dict[str, int]]
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

    Every rule of the decision table is charged here except R11, which compares
    the run against the *committed* census and therefore needs the baseline
    file: it lives in :func:`erosion_failures`, and every caller that gates on
    this report must apply it (``main`` does, for both the reporting and the
    update path). A caller that skips it keeps the per-run deletion tripwire
    disarmed. R12, the cumulative half, needs only a frozen constant and is
    charged here, so it survives a caller that forgets R11 or points
    ``--baseline`` at another file.
    """
    selected = list(targets) if targets is not None else list(TARGETS)
    visited: List[str] = []
    hard: List[str] = []
    coverage: List[str] = []
    findings: List[Finding] = []
    selfrefs: List[Finding] = []
    citation_counts: Dict[str, int] = {}
    raw_counts: Dict[str, int] = {}
    accounting: Dict[str, Dict[str, int]] = {}
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
            accounting={},
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
        citations, target_coverage, target_accounting = extract(target, text)
        visited.append(target)
        coverage.extend(target_coverage)
        raw_counts[target] = text.count(".lean")
        accounting[target] = target_accounting
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

        # R12, the cumulative half of the deletion charge. It is here rather
        # than in :func:`erosion_failures` because it needs no baseline: it
        # compares the run against a constant, so every mode charges it -- the
        # gating run, ``--strict`` and ``--update-baseline`` alike -- and it
        # cannot be disarmed by pointing ``--baseline`` somewhere else.
        measured = MEASURED_CITATIONS.get(target, 0)
        if target in TARGETS and measured <= 0:
            # The *value* is checked, not just the key: ``measured`` of ``0`` is
            # the "never measured" sentinel a line below, so an entry of
            # ``{"docs/index.md": 0}`` satisfies a membership-only arming
            # check while disarming the cap exactly as deleting the entry does.
            hard.append(
                f"VACUOUS {target}: default target with no positive frozen citation "
                "measurement, so the cumulative erosion cap is unarmed"
            )
        cap = cumulative_loss_cap(measured)
        if measured and measured - len(citations) > cap:
            hard.append(
                f"ERODED {target}: {len(citations)} citations, "
                f"{measured - len(citations)} below the frozen measurement of {measured} "
                f"(cumulative cap {cap}). The per-run budget is charged against the "
                "committed census, which every update rewrites; this one is charged "
                "against MEASURED_CITATIONS, which only a reviewed edit of "
                "citation_audit.py and its test can move. Re-measure the documents and "
                "say so in that diff"
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
        accounting=accounting,
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
        "# Three roles, three rules (see the module docstring):",
        "#   rows          gating. Ratcheted per (class, target, token); a count may only",
        "#                 fall. first_line is payload and is not part of the key. SELFREF",
        "#                 rows are advisory: they never gate an audit run's exit code,",
        "#                 though --update-baseline refuses a rise in any row, this class",
        "#                 included.",
        "#   #census       per-class counts: derived book-keeping, refreshed on update.",
        "#                 They are NOT pinned against the live documents -- an equality",
        "#                 pin there freezes the documents instead of the extractor. The",
        "#                 extractor is pinned on scripts/audit/citation_corpus/ instead.",
        "#   #census       citations/raw: the per-run deletion budget (R11). A target that",
        "#                 loses more than max(25, 5%) of its committed citations fails",
        "#                 hard, because the ratchet cannot tell a deleted citation from a",
        "#                 fixed one. The budget is recomputed from this file on every",
        "#                 update, so it bounds one run and not the total; the total is",
        "#                 bounded by R12 against MEASURED_CITATIONS, a constant in",
        "#                 scripts/citation_audit.py that no run rewrites.",
        "#",
        "# Update with:",
        "#   python3 scripts/citation_audit.py --update-baseline scripts/audit/citation_baseline.tsv",
        "# which refuses to raise any key's count against the strictest committed copy,",
        "# refuses a drop past the budget or the cumulative cap, and refuses to run at all",
        "# where those committed copies cannot be read (a shallow clone, or a partial one",
        "# that holds trees without blobs), where fewer than two commits carry this file",
        "# (a baseline created on a branch and not landed yet, or a stale fetch: the only",
        "# reference left is then the branch's own last write), or where one of those",
        "# copies' trees spells this path some other way (a mis-cased spelling names bytes",
        "# no tree lists, and a path outside the repository is not a tracked path at all).",
        "# The file is written by replacing the resolved path with a temporary file whose",
        "# own name is taken with O_EXCL next to it, so neither a hard link to these bytes",
        "# nor a pre-created temporary is written through. What the refusals leave is a",
        "# hand edit of this file or of the constants, and -- for a path no commit carries",
        "# any more -- removing the commit that created it; each of those is a loud diff,",
        "# and that is the point.",
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
    """Read a baseline file into ``(multiset, census, tracked)``."""
    return parse_baseline(path.read_text(encoding="utf-8"))


def parse_baseline(text: str) -> Tuple[Counter, Dict[str, Dict[str, int]], int]:
    """Parse baseline text into ``(multiset, census, tracked)``.

    Text rather than a path because the copy that governs an update is the one
    in a *commit*, read through ``git show`` (see :func:`committed_baseline`).

    The census comment lines are machine-readable because the ``citations``
    field is R11's reference point. The per-class counts are read as well, for
    reporting and for the corpus expectation, but nothing compares them to a
    live run: that comparison was the equality pin this file's header warns
    about, and it made every remediation commit fail by construction.
    """
    multiset: Counter = Counter()
    census: Dict[str, Dict[str, int]] = {}
    tracked = 0
    for line in text.split("\n"):
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


def erosion_failures(
    report: Report, census: Dict[str, Dict[str, int]], rows: Counter
) -> List[str]:
    """Charge the content loss the ratchet is blind to (R11).

    ``census`` and ``rows`` come from the *committed* baseline. Two things are
    charged, both hard failures:

    * a target whose citation count fell further below its committed census than
      :func:`citation_drop_budget` allows -- "remediation" by deleting the citing
      sentence clears findings without fixing anything, and nothing else in the
      tool can see it;
    * a target that carries baseline rows but has lost its ``#census`` line,
      which would leave the budget unarmed while looking like tidy-up.

    A target with neither rows nor a census entry is not charged: that is an
    ad-hoc ``--targets`` run against a document the baseline never covered, and
    inventing a reference point for it would be a number nobody reviewed. That
    the *default* targets always have a census entry is pinned by the test
    suite against the committed file, where the claim actually belongs.
    """
    failures: List[str] = []
    for target in report.visited:
        recorded = census.get(target)
        if recorded is None:
            if any(key[1] == target for key in rows):
                failures.append(
                    f"ERODED {target}: the baseline carries rows for this target but no "
                    "#census line, so the deletion budget is unarmed; restore it with "
                    "--update-baseline instead of deleting it"
                )
            continue
        committed = recorded.get("citations", 0)
        now = report.citations.get(target, 0)
        budget = citation_drop_budget(committed)
        if committed - now > budget:
            failures.append(
                f"ERODED {target}: {now} citations, {committed - now} below the committed "
                f"census of {committed} (per-run budget {budget}). Deleting cited text "
                "clears findings without fixing them; a larger drop has to be stated "
                "explicitly by editing the #census line in the same commit, where review "
                "sees it"
            )
    return failures


def _git_committed_text(revision: str, relative: str) -> Optional[str]:
    """Return ``revision:relative``'s content, or ``None`` if it could not be read.

    ``git show`` answers "no such revision", "no such path in this revision" and
    "the object is not in this clone" with the same non-zero exit status, so on
    its own ``None`` is three outcomes with opposite consequences. Both of the
    other two questions are therefore asked separately before this is called:
    the revision resolves (:func:`_revision_commit`) and the path is listed in
    its tree (:func:`_git_path_in_tree`). After those, ``None`` means exactly
    one thing -- *the content of a path this commit does have could not be
    read* -- which is a refusal and never the bootstrap case.
    """
    try:
        proc = subprocess.run(
            ["git", "show", f"{revision}:{relative}"],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError as exc:  # pragma: no cover - git missing is an environment fault
        raise GitError(f"git show {revision}:{relative}: {exc}") from exc
    return proc.stdout if proc.returncode == 0 else None


def _git_path_in_tree(revision: str, relative: str) -> Optional[bool]:
    """Return whether ``revision``'s tree lists ``relative``; ``None`` if unknown.

    The membership question, asked of the tree rather than of the blob. It is
    what separates "this commit does not have the file" -- the only fact that
    may lead to the bootstrap path -- from "this commit has it but the content
    did not come back", which a blob read alone reports identically. A partial
    clone (``--filter=blob:none``) has every tree and no blob, so the two are
    not hypothetical alternatives of each other.

    ``None`` is returned when git itself failed, i.e. when the question was not
    answered; the caller refuses on it rather than guessing an answer, which is
    the same rule the rest of this module applies to an approximation.
    """
    try:
        listed = _git(["ls-tree", "--full-tree", "--name-only", revision, "--", relative])
    except GitError:
        return None
    return bool(listed.strip())


def _destination_identity_refusals(
    destination: Path, relative: str, revisions: Sequence[str]
) -> List[str]:
    """Return refusals when ``revisions`` spell ``relative``'s path another way.

    Membership is asked of a **pathname** (``git ls-tree``, repository-relative
    and case-sensitive) while the write lands on whatever that name opens. On a
    case-insensitive filesystem -- macOS by default, where this repository has
    ``core.ignorecase=true`` -- ``audit/Base.tsv`` *opens* ``audit/base.tsv``
    while git lists nothing for it, and ``Path.resolve()`` does not canonicalise
    case, so the two identities come apart with nothing to report it. Then every
    answer the revisions gave is about a different file than the one about to be
    overwritten -- and because no tree lists the alias, the carrier set is empty,
    which is the bootstrap path, which switches off the growth refusal and R11
    together. Measured at review before this was charged: a mis-cased spelling
    and an in-repo hard link each took the bootstrap branch with no refusal at
    all and rewrote a committed baseline of 1,000 rows into one of 300.

    So each revision's tree is listed whole (``ls-tree -r``, ~2,100 paths here,
    one query per revision) and asked one question: does it hold a path that
    differs from ``relative`` only in case? **The filesystem is not consulted at
    all**, and that is the fix rather than an economy. Two earlier forms of this
    check walked the path on disk, and each stopped at the first component the
    worktree did not hold -- once at the leaf, then, one round later, one level
    up. Measured at review on the second form, on this repository with
    ``scripts/audit`` moved aside (what a sparse checkout gives for free) and one
    citation added to ``docs/index.md``: the honest spelling refused with
    ``GROWN`` while ``scripts/audit/Citation_baseline.tsv`` wrote 1,368 rows at
    exit 0, after which ``git status`` reported the tracked baseline modified. A
    disk walk cannot answer for a path the disk does not hold, and the trees are
    what ``git ls-tree`` will match anyway, so they are the only authority here.

    A revision whose tree cannot be listed is charged, not skipped: an unanswered
    question read as "no alias" is the exoneration this module does not do. It is
    charged here rather than left to :func:`committed_baseline` because the two
    queries are not the same one -- this lists every subtree, that one only the
    trees along a single path -- so a store that has lost a tree elsewhere can
    fail here and answer there.

    A destination spelled as the trees spell it is left to the carrier count, and
    so is a symlink to the tracked path, which ``resolve()`` has already turned
    into that path. Two other ways the identities come apart are handled where
    they belong rather than here: a destination outside the repository is refused
    by the caller, where ``relative`` cannot be formed at all, and a second name
    for the tracked file's bytes (a hard link) no longer reaches them, because
    :func:`update_baseline` renders to a temporary file and replaces the resolved
    path with it, which severs the link instead of writing through it.
    """
    refusals: List[str] = []
    folded = relative.casefold()
    for revision in revisions:
        try:
            listed = _git(["ls-tree", "-r", "--full-tree", "--name-only", "-z", revision])
        except GitError as exc:
            refusals.append(
                f"UNREADABLE {revision}: git could not list that revision's tree, so "
                f"whether it spells {relative} some other way is unknown ({exc})"
            )
            continue
        for name in listed.split("\0"):
            if name != relative and name.casefold() == folded:
                refusals.append(
                    f"ALIASED {destination}: {revision} lists {name}, which differs "
                    f"from {relative} -- the path the membership question is asked "
                    "about -- only in case. A case-insensitive filesystem opens both "
                    "through one file, so the copies that were read and the bytes that "
                    "would be overwritten need not be the same. Spell the path as the "
                    "tree spells it"
                )
                return refusals
    return refusals


def _revision_commit(revision: str) -> Optional[str]:
    """Return the commit ``revision`` names, or ``None`` if it does not resolve.

    The existence question, asked separately from the content question, because
    ``git show rev:path`` answers both with the same non-zero exit status. This
    is the whole of the distinction the update path is built on.
    """
    try:
        resolved = _git(["rev-parse", "--verify", "--quiet", f"{revision}^{{commit}}"])
    except GitError:
        return None
    return resolved.strip() or None


def _committed_revisions() -> Tuple[List[str], List[str]]:
    """Return ``(revisions, refusals)`` for the copies that govern an update.

    ``merge-base(HEAD, origin/main)`` is what review diffs against, ``origin/main``
    is where the file will land, and ``HEAD`` is the branch as committed so far.
    All three are *commits*: the working file is deliberately absent, because a
    branch that judged itself by its own last write could raise the baseline one
    commit at a time and never show a growth.

    A revision that does not resolve is a **refusal**, not an omission. Dropping
    it silently is how "the strictest committed copy" degenerates into "this
    branch's previous commit": ``origin/main`` is absent in every shallow or
    single-branch clone, and with it gone the remaining reference is ``HEAD``,
    which the branch itself wrote. The list is required to hold at least two
    resolvable revisions for the same reason -- one reference is the branch
    judging itself, whatever it is called.

    Resolvability is all this function establishes. Whether a revision *carries*
    the baseline is a different question with the same failure mode -- three
    revisions can resolve while only ``HEAD`` holds the file -- and it is asked,
    against the same "at least two" rule, in :func:`committed_baseline`, which
    is where the path is known.

    ``merge-base`` failing while both named revisions resolve (unrelated
    histories) is refused too: it means the reference review will diff against
    cannot be computed, and guessing one is exactly the exoneration this module
    does not do.
    """
    revisions: List[str] = []
    refusals: List[str] = []
    for name in ("origin/main", "HEAD"):
        if _revision_commit(name) is None:
            refusals.append(
                f"UNREADABLE {name}: not a commit in this clone. A shallow or "
                "single-branch checkout has no origin/main, and judging an update "
                "without it compares the branch against its own previous commit"
            )
        else:
            revisions.append(name)
    if len(revisions) == 2:
        try:
            merge_base = _git(["merge-base", "HEAD", "origin/main"]).strip()
        except GitError as exc:
            merge_base = ""
            refusals.append(f"UNREADABLE merge-base(HEAD, origin/main): {exc}")
        if merge_base:
            revisions.insert(0, merge_base)
    if len(revisions) < 2:
        refusals.append(
            f"UNREADABLE only {len(revisions)} committed revision(s) could be read; "
            "at least two are required, because a single reference is the branch "
            "judging itself"
        )
    return (revisions, refusals)


def committed_baseline(
    destination: Path,
) -> Tuple[Optional[Counter], Dict[str, Dict[str, int]], List[str], List[str]]:
    """Return the committed baseline an update to ``destination`` is judged by.

    ``(rows, census, sources, refusals)``. The first two take the **strictest**
    value over every revision of :func:`_committed_revisions` that has the file:
    the per-key *minimum* for the rows (a smaller allowance refuses more, so a
    stale branch cannot reintroduce a row ``origin/main`` has already cleared)
    and the *maximum* recorded ``citations`` for the census (a larger reference
    charges a bigger drop). Both err towards refusing, and the remedy for a
    refusal caused by a stale branch is a rebase, after which every revision
    agrees.

    ``refusals`` is non-empty when the comparison could not be *set up*, which
    is four separate outcomes: a revision that does not resolve, a revision
    whose tree could not be listed or whose committed content could not be read,
    fewer than two revisions that **carry** the file, and a revision whose tree
    spells ``destination``'s path some other way (see
    :func:`_destination_identity_refusals`). The caller must treat it as fatal,
    because every downstream verdict here -- including the permissive ones -- is
    a claim about copies that were not read, or about a different file.

    The last of those is the one that is easy to lose. ``_committed_revisions``
    guarantees two revisions *resolve*; only a revision that has the path
    supplies an allowance, and the two sets differ exactly when the baseline is
    newer than the upstream ref -- a branch that created it, or a stale fetch.
    The reference would then be ``HEAD`` alone with every revision resolving and
    nothing to report, which is the branch judging itself under another name.
    So the counted quantity is carriers, not sources of a successful
    ``rev-parse``.

    ``rows is None`` is the **bootstrap** case and is stated positively: at least
    two revisions resolved, each answered the membership question, none of their
    trees spells the destination's path another way, and none of them lists it.
    Then no commit carries the file under any spelling: it is not yet anyone's
    allowance, and its creation adds a path no revision had. It is reachable only
    with ``refusals`` empty: a run that could not read a revision, could not read
    a blob it does have, found exactly one carrier, or was pointed at a spelling
    a revision's tree holds under another case does not get this path, which
    would otherwise switch off the growth refusal and R11 at once.
    """
    revisions, refusals = _committed_revisions()
    resolved = destination.resolve()
    try:
        relative = resolved.relative_to(REPO_ROOT.resolve()).as_posix()
    except ValueError:
        refusals.append(
            f"OUTSIDE {destination}: resolves to {resolved}, which is not under "
            f"{REPO_ROOT}, so no revision of this repository can be asked whether it "
            "carries the file -- while the write would still land, on a baseline the "
            "growth refusal and R11 were both switched off for. Name the baseline's "
            "path inside the repository"
        )
        return (None, {}, [], refusals)
    refusals.extend(_destination_identity_refusals(destination, relative, revisions))
    rows: Optional[Counter] = None
    census: Dict[str, Dict[str, int]] = {}
    sources: List[str] = []
    carriers = 0
    for revision in revisions:
        present = _git_path_in_tree(revision, relative)
        if present is None:
            refusals.append(
                f"UNREADABLE {revision}: git could not list {relative} in that revision's "
                "tree, so whether it carries the file is unknown"
            )
            continue
        if not present:
            continue
        carriers += 1
        text = _git_committed_text(revision, relative)
        if text is None:
            refusals.append(
                f"UNREADABLE {revision}:{relative}: the path is in that revision's tree "
                "but its content did not come back (a partial clone holds trees without "
                "blobs), so this copy cannot be compared against and reading it as an "
                "absent file would be the bootstrap path"
            )
            continue
        revision_rows, revision_census, _ = parse_baseline(text)
        sources.append(f"{revision}:{relative}")
        if rows is None:
            rows = revision_rows
            census = revision_census
            continue
        for key in set(rows) | set(revision_rows):
            rows[key] = min(rows.get(key, 0), revision_rows.get(key, 0))
        for target, entries in revision_census.items():
            if target not in census:
                census[target] = dict(entries)
                continue
            census[target]["citations"] = max(
                census[target].get("citations", 0), entries.get("citations", 0)
            )
    if 0 < carriers < 2:
        refusals.append(
            f"UNCOMPARABLE only {carriers} committed revision(s) carry {relative}; at "
            "least two are required, because a single reference is the branch judging "
            "itself. The path is not new here -- bootstrapping is for a path no readable "
            "revision has -- so land it on origin/main (or rebase onto an origin/main "
            "that has it) before updating it again. Removing the commit that created it "
            "instead (a reset, or an amend that drops it) puts the path back in the "
            "bootstrap state; that is a history rewrite, and the file's re-creation is a "
            "new file in the diff either way"
        )
    if rows is not None:
        rows = Counter({key: count for key, count in rows.items() if count})
    return (rows, census, sources, refusals)


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
    report: Report,
    regressions: Sequence[str],
    cleared: int,
    strict: bool = False,
    census: Optional[Dict[str, Dict[str, int]]] = None,
) -> str:
    """Render the human report.

    ``census`` is the committed one, when the caller has it: the citation delta
    against it is printed for every target that moved, so a within-budget
    deletion is a number in the report -- and in the PR body quoting it --
    rather than something a reader has to reconstruct from two TSV diffs.

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
        recorded = (census or {}).get(target, {}).get("citations")
        if recorded is not None and recorded != report.citations[target]:
            delta = report.citations[target] - recorded
            out.append(
                f"    citations {recorded} -> {report.citations[target]} ({delta:+d}); "
                f"deletion budget {citation_drop_budget(recorded)}"
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
            class_census = "  ".join(
                f"{name}={report.counts[target][name]}"
                for name in ALL_CLASSES
                if report.counts[target][name]
            )
            out.append(f"{target}: {class_census}")
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


def update_baseline(report: Report, destination: Path) -> int:
    """Rewrite ``destination`` from ``report``; return the process exit code.

    Regenerating the rows from the current run is the one operation that retires
    a finding without fixing a citation, so it is fail-closed by construction:
    what is written is provably per-key ``<=`` the committed copy, and every
    refusal below is unconditional. There is no ``--force``, because the
    operations refused here are exactly the ones that must be visible in a diff
    rather than performed by a tool.

    The destination is resolved once, here, so that the path the revisions are
    asked about below and the path written to at the end are the same one. The
    write itself renders to a temporary file next to it and replaces it, which
    is what makes that true of the *bytes* as well: replacing a name detaches it
    from any other name that shared its inode, where writing through the name
    would have reached the file those other names hold.

    That temporary is created by :func:`tempfile.mkstemp`, i.e. ``O_CREAT |
    O_EXCL`` on a name this run picked, and is unlinked whatever happens. A
    *predictable* temporary name is the same write-through one step removed: with
    ``.<name>.pending`` next to the destination, that name was never resolved and
    never judged, and ``write_text`` follows links, so pre-creating it as a hard
    link or a symlink to the tracked baseline put the render straight onto the
    committed bytes. Measured at review on this repository's own fixtures: both
    spellings exited 0 and rewrote a committed 100-row baseline to 150 rows.
    ``O_EXCL`` answers both at once -- the name cannot pre-exist -- without a
    refusal to test or a branch in the gate. What it does not preserve is the
    destination's mode: the temporary is created ``0600`` and ``replace`` carries
    that to the destination. git records only the exec bit, so this leaves no
    diff.
    """
    if not destination.is_absolute():
        destination = REPO_ROOT / destination
    destination = destination.resolve()
    if not report.ok_structurally:
        print(format_text(report, [], 0), end="")
        print("refusing to write a baseline from an untrustworthy run")
        return 1
    if set(report.visited) != set(TARGETS):
        # The file is the count-of-record for *all* targets, and it is rendered
        # from this run alone, so a partial run would silently drop every row of
        # the targets it did not open -- shrinking the recorded debt without
        # fixing a single citation, and leaving the ratchet with nothing to
        # compare against later.
        missing = sorted(set(TARGETS) - set(report.visited))
        extra = sorted(set(report.visited) - set(TARGETS))
        print(format_text(report, [], 0), end="")
        print(
            "refusing to write a baseline from a partial target set "
            f"(not scanned: {missing or 'none'}; not a default target: {extra or 'none'})"
        )
        return 1

    committed, committed_census, sources, refusals = committed_baseline(destination)
    # R11 before anything is printed, so an eroded run suppresses its own census
    # here exactly as it does in the reporting path: the numbers a deletion
    # produced are not numbers to publish.
    report.hard.extend(erosion_failures(report, committed_census, committed or Counter()))
    print(format_text(report, [], 0, False, committed_census), end="")
    if not report.ok_structurally:
        print("refusing to write a baseline that records a deletion past the budget")
        return 1
    if refusals:
        # Before the growth and bootstrap branches below, both of which would
        # otherwise draw a conclusion from revisions this run could not read.
        for item in refusals:
            print(item)
        print(
            "refusing to write a baseline with no readable committed copy to be judged "
            "against -- or with a destination that is not the path that was judged: "
            "fetch origin/main (an unshallowed, non-single-branch clone, with its "
            "blobs) and run this again; if the refusal above says only one revision "
            "carries the file, land that file on origin/main first; if it says the "
            "destination is aliased or outside the repository, name the tracked path "
            "itself. There is no override flag"
        )
        return 1

    current: Counter = Counter()
    for row in aggregate(list(report.findings) + list(report.selfrefs)):
        current[(row.cls, row.target, row.token)] = row.count
    if committed is None:
        print(f"no committed copy of {destination}; writing it as a new file")
        committed = Counter()
    else:
        print(f"judged against {', '.join(sources)}")
        growth = sorted(
            (key, count, committed.get(key, 0))
            for key, count in current.items()
            if count > committed.get(key, 0)
        )
        if growth:
            for (cls, target, token), count, allowed in growth[:40]:
                print(f"GROWN {cls} {target} {token} (committed {allowed}, now {count})")
            if len(growth) > 40:
                print(f"... {len(growth) - 40} more")
            print(
                f"refusing to write a baseline that grows by {len(growth)} key(s): a row "
                "that rises is an unfixed finding turned into an allowance. Fix the "
                "citations, or record the growth by hand so the diff shows it."
            )
            return 1

    destination.parent.mkdir(parents=True, exist_ok=True)
    handle, name = tempfile.mkstemp(
        dir=str(destination.parent), prefix=f".{destination.name}.", suffix=".pending"
    )
    pending = Path(name)
    try:
        with os.fdopen(handle, "w", encoding="utf-8") as stream:
            stream.write(render_baseline(report))
        pending.replace(destination)
    finally:
        pending.unlink(missing_ok=True)
    added = sum(max(0, count - committed.get(key, 0)) for key, count in current.items())
    removed = sum(max(0, count - current.get(key, 0)) for key, count in committed.items())
    print(f"wrote {destination}")
    print(f"delta: +{added} finding(s), -{removed} finding(s) versus the committed file")
    return 0


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
        "--update-baseline",
        metavar="PATH",
        help=(
            "Rewrite a baseline file from this run. Refuses to raise any key's count "
            "against the strictest committed copy, refuses a citation drop past the "
            "per-run budget (R11) or the cumulative cap (R12), and refuses to run at "
            "all where those committed copies cannot be read -- a shallow or "
            "single-branch clone, which is what a default CI checkout produces -- "
            "where fewer than two commits carry the file, which is a baseline this "
            "branch created and has not landed upstream yet, or where one of those "
            "copies' trees spells the destination's path some other way (a mis-cased "
            "spelling, a path outside the repository); there is no override flag. The "
            "file is written by replacing the resolved path with a temporary file "
            "whose own name is taken with O_EXCL next to it, so neither a second name "
            "for its bytes (a hard link) nor a pre-created temporary is written "
            "through."
        ),
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

    if args.update_baseline:
        return update_baseline(report, Path(args.update_baseline))

    current = Counter()
    for row in aggregate(list(report.findings)):
        current[(row.cls, row.target, row.token)] = row.count
    advisory = Counter()
    for row in aggregate(list(report.selfrefs)):
        advisory[(row.cls, row.target, row.token)] = row.count

    regressions: List[str] = []
    cleared = 0
    committed_census: Dict[str, Dict[str, int]] = {}
    baseline_path = Path(args.baseline)
    if not baseline_path.is_absolute():
        baseline_path = REPO_ROOT / baseline_path
    if args.strict:
        regressions = [
            f"UNRESOLVED {finding.cls} {finding.target}:{finding.line} {finding.token}"
            for finding in report.findings
        ]
    if not baseline_path.is_file():
        # Charged in both modes: the baseline is the ratchet's reference *and*
        # R11's, so a run without one measures less than it appears to, even
        # under ``--strict``.
        report.hard.append(f"BASELINE {baseline_path}: missing")
    else:
        baseline, committed_census, _ = read_baseline(baseline_path)
        # R11 before the ratchet, so a target whose citations were deleted away
        # suppresses the report rather than being congratulated for the findings
        # that went with them.
        report.hard.extend(erosion_failures(report, committed_census, baseline))
        audited = set(report.visited)
        if not args.strict and report.ok_structurally:
            gating = Counter(
                {key: count for key, count in baseline.items() if key[0] in FINDING_CLASSES}
            )
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
        print(
            format_text(report, regressions, cleared, args.strict, committed_census),
            end="",
        )

    ok = report.ok_structurally and not regressions
    if args.format == "text":
        print("citation audit: PASS" if ok else "citation audit: FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
