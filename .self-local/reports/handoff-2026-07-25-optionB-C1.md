# Handoff — 2026-07-25 — Option-B deletion campaign + C1 (HLS positivity) — SESSION FINAL STATE

## FINAL UPDATE 2026-07-25 (session end) — main = `673aabd8`

This session's Option-B + C1 work is **fully merged**. Three PRs landed in sequence:

| PR | issue | title | merged main |
|---|---|---|---|
| **#4703** | #4701 | Remove LatticeSystemBridge scaffold (5 files, 323L, 12 reference-0 decls) + docs retraction | `5090f6de` |
| **#4705** | #4700 | Retract §18.4 Mayer order-3 docs/tex claims left stale by #4702 | `a3046ce6` |
| **#4707** | #4706 | Replace `positivity` at 3 measured hot sites in `HLSSharpPairBound.lean` (C1) | `673aabd8` |

**Closed this session**: #4701, #4700, #4706 (all `completed`, auto-closed via `Closes #NNNN` in
the respective PR bodies).

**New issue opened this session**: **#4704** — docs/tex repo-wide stale `.lean` reference sweep
(tracking only). Headline counts re-anchored after PR #4705: **docs 9 / tex 156** (down from the
original 12/159 — the 3-item delta is exactly the Mayer-order-3 references retracted by #4705,
excluded here to avoid double-counting with #4700's now-closed scope).

**User approval pending** (technical work fully disposed, close is a pure administrative step
withheld per `feedback_approval_required`): **#4692** (Option-D reference-0 campaign umbrella)
and **#4559** (folded-in predecessor, all 3 items disposed). **Not closed by dev-pr-clerk this
session** — do not close without explicit user instruction.

## Key finding this session: the #4702 defect class and its systemic root cause

**#4702**'s squash commit message (main `4d23d7cc`, 2026-07-24) asserted the PR "retracts the
corresponding §18.4 order-3 docs claim" — **this was false**: the PR deleted 4 Lean declarations
across 2 files but never touched `docs/index.md` or `tex/proof-guide.tex`, which continued to cite
the deleted declarations/files as if they still existed. This went undetected through the normal
gate sequence for a structural reason, not a one-off oversight:

- **`lake build` cannot detect it**: docs/tex files are not part of the Lean build graph, so a
  build-warning-zero gate is blind to doc/code divergence by construction.
- **The existing `dev-review` audit_gate V1–V4** checks build health, axiom hygiene,
  sorry/admit/native_decide, and structural diff shape — **none of the four gates compares
  declared-entity names in the diff against docs/tex prose**, so this defect class passes V1–V4
  cleanly every time it occurs.
- Detection in this session came only from `dev-issue-manager`'s manual `git grep` cross-check
  during a governance re-verification pass (#4701's review), not from any standing gate. This
  session's own PRs (#4703, #4705, #4707) were each explicitly checked for the same pattern before
  merge (grep the diff's deleted/renamed decl names against `docs/` + `tex/`, zero-hit
  requirement) — see #4704's "Recurrence-prevention proposal" for the standing-gate version of
  this check (candidate "V5" for `dev-review`'s audit_gate), which remains unimplemented and is a
  good candidate for the next session if a lightweight, low-false-positive form can be designed
  (the existing #4704 evidence shows naive basename/path regex scans carry a nontrivial
  false-positive rate, so V5 needs the same per-declaration audit discipline as #4704's own scope
  item 1, not a blind grep).

## Session summary (chronological, full session)

Build-speed refactor campaign continues from main `978e8289`. Merged this session:

- **#4693** — import dep-explicit refactor.
- **#4695** — positivity refactor, own-cost reduction ~7.6s (`BallBoundaryInfinite.lean:194`,
  `add_nonneg`/`mul_nonneg` explicit route replacing interpreted `positivity`).
- **#4698** — removed the only `native_decide` from the `IsingModel/` library
  (`TestGenerators.lean`; duplicated verbatim in `test/IsingModel/Generators.lean`, so no coverage
  lost), own-cost reduction ~2.4s.
- **#4699** — `TwoSiteInteractingLayerSpectralData.lean`: converted 4 of ~15 `nlinarith` calls to
  explicit `linarith`/`pow_left_inj₀`, own-cost reduction ~0.9s (16-branch orthogonality check at
  line 217 kept as `nlinarith`, genuinely nonlinear).
- **#4702** — Mayer order-3 deletion (Option-B item 1/2, code only). Deleted
  `MayerCore/Truncations.lean` + `MayerCore/MayerTermThreeEval.lean` (4 reference-0 decls:
  `mayerExpansionTerm_three`, `mayerPartialSum_three`, and evaluated forms), subsumed by the
  general recurrence `mayerExpansionTerm`/`mayerPartialSum_succ`. Removed umbrella import
  `IsingModel.lean:424`. **Docs/tex retraction was claimed in the squash message but never
  performed** — see "Key finding" above; corrected by #4705 below.
- **#4703** (issue #4701) — LatticeSystemBridge scaffold removed (5 files / 323L / 12
  reference-0 decls: `ClassicalSpinSystem`, `isingAsClassicalSpinSystem`,
  `gibbsExpectationOfAbstract`, `correlationOfAbstract`, `couplingOf` and variants), umbrella
  imports `IsingModel.lean:502–506` removed, `docs/index.md:2048–2050` retracted **in the same
  PR** (the #4702 failure mode did NOT recur here). Follow-up commit `ead50911` also fixed a
  dangling `scripts/noshake.json:46` entry. Merged squash main `4d23d7cc` → `5090f6de`. Issue
  **#4701 CLOSED**.
- **#4705** (issue #4700) — docs/tex retraction of the §18.4 Mayer order-3 claims left stale by
  #4702: `docs/index.md:2126` clause deleted, `tex/proof-guide.tex:19368–19383` paragraph deleted
  whole, `tex/proof-guide.tex:21081–21097` deleted (21077–21080 + GJ citation line 21098 kept).
  Preserve-list verified intact (`UrsellFinThree`, `ursellCoefficient_fin_three_eq`,
  `mayerPartialSum_two`/`_succ`, `mayer_identity_general_t`,
  `mayerExpansionTerm_*_eq_of_pairwise_disjoint`). Zero Lean-file diff. Merged squash main
  `5090f6de` → `a3046ce6`. Issue **#4700 CLOSED**. Unblocked close-readiness for #4692/#4559
  (user approval still pending) and re-anchored #4704's counts (12/159 → 9/156).
- **#4707** (issue #4706, "C1") — `dev-perf` measured 3 of 35 `positivity` call sites in
  `IsingModel/PseudoMass/HLSSharpPairBound.lean` (`darts_cross_sum_le_sharp_decay`,
  `tsum_mul_neighborFinset_sum_pow_neg_le`, `summable_mul_neighborFinset_sum_pow_neg`) account for
  77% of the module's `positivity` cost because their shared goal shape (`Finset.sum` inside a
  product) forces `Positivity.evalMul` to recurse through the sum extension. Folded into one
  shared `private lemma mul_neighborFinset_sum_pow_neg_nonneg`. Own-cost 3.05s → 2.48s
  (implementer paired measurement) / **2.43s** (independent `dev-verify` re-measurement, median of
  3 replicates); largest `Positivity.evalMul` entry 405ms → 27ms. The remaining 32 sites
  (0.19s aggregate, ~3% of the module) were **deliberately left untouched** — measured ROI
  insufficient. Merged squash main `a3046ce6` → `673aabd8`. Issue **#4706 CLOSED**. A correction
  comment was posted on #4706 fixing the issue body's inaccurate "33/30" site count (true: 35 base
  / 32 remaining after excluding doc-comment mentions) and formally returning the unused portion
  of the user's original "~30 sites" authorization (net ROI ~0.1s after replacement overhead did
  not justify converting the remaining 32).

Closed (non-code, campaign bookkeeping, prior to this session's final three merges): **#4694**
(build-time campaign complete-for-this-round), **#4696**/**#4697** (import-hygiene candidates —
refuted 0/10 via full-build oracle).

## Key findings (carry forward)

- The build-time-per-module axis is at measured diminishing returns after the clear outliers
  (`positivity` in `BallBoundaryInfinite`, `native_decide` in `TestGenerators`, and now the 3 hot
  `positivity` sites in `HLSSharpPairBound`). Remaining call sites yield sub-second, marginal
  wins per site — worth doing only for specifically-authorized, budgeted items with measured ROI,
  not as a blanket sweep (C1's own remaining-32-sites decision is the canonical example: measured
  and declined).
- `shake` is **systematically false-positive** for umbrella-import removal in this re-export-heavy
  repo: it flags imports as unused that are actually needed transitively through umbrella re-exports.
  The **full build is the only reliable oracle** for import-removal safety; `shake` output is a
  candidate-generation hint only, never a deletion justification by itself.
- The "reference-0" (zero-static-reference) candidate pool is **~45% false-positive**, dominated by
  items that are actually deliverables (book-cited results, docs-referenced rows, or GJ/Lee-Yang
  endpoint theorems that are correct to have zero *internal* Lean consumers). Each reference-0
  candidate needs consumer-side + docs-side verification before deletion, not just declaration-side.
- **New this session (the #4702 defect class)**: deletion-type PRs must be explicitly grep-checked
  (deleted/renamed decl names against `docs/` + `tex/`, zero-hit requirement) before merge, in the
  *same* PR that performs the deletion — this check is currently manual (performed by
  `dev-issue-manager`/`dev-pr-clerk` on request), not a standing automated gate. See #4704 for the
  broader pre-existing debt of this same class, and its proposed (unimplemented) "V5" gate.
- Process hygiene: **never run 2 concurrent Lean builds** in this repo (this lake has no `-j`, so
  builds must be strictly serialized). `dev-verify` = build, `dev-review` = static + codex — these
  must not overlap in time on the same working tree.

## PENDING / NOT STARTED — resume here

### Candidate 1: #4704 — repo-wide stale docs/tex `.lean` references (needs scope confirmation)

9 stale refs in `docs/index.md`, 156 in `tex/proof-guide.tex` (candidate clusters:
`RangeAscoliPatches/*`, `SubseqCompactOpen/*`, `BranchAscoliCompactOpen/*Patches/*`,
`Peierls/SingleOrbit*`, `Branches/*`). Pre-existing debt, unrelated to #4703/#4705/#4707. Needs
its own **per-declaration audit** before any deletion/fix — the raw regex scan has a nontrivial
false-positive rate (do not blind-delete/blind-retract on the basis of the raw count alone). Not
scoped for implementation yet; the next session should first produce the precise audit (file
existence via `git ls-tree`, declaration existence via `grep -rn`), then bring the scoped plan
back to the user/main-agent for a go/no-go before touching `docs/` or `tex/`. See issue #4704 body
for the recurrence-prevention proposal (docs/tex grep gate on deletion PRs + `dev-review`
audit_gate "V5" extension) — this is also a good candidate to design and implement standing
tooling for, given the #4702 defect class finding above.

### Candidate 2: #4642 (generalize K_n closed form) — premise likely stale, needs re-verification first

Opened as a follow-up from #4640 (2026-07-21) to generalize the hardcoded K0/K2/K3/K4
`completeGraph` closed-form base cases. Given how much the repo has changed since (multiple
refactor campaigns, #4693's import-dependency work touching adjacent modules), **the issue body's
premise should be re-verified against current `main` before any implementation work starts** —
confirm the K0/K2/K3/K4 special-cases still exist as described and that no intervening PR already
generalized or removed them.

### Candidate 3: #4563 (SpecialCases consolidation, wave-3) — large, needs fresh measurement

Standing-authorization family-consolidation campaign; wave-1/wave-2 (28 families) already
complete per the campaign log in `.self-local/issues/INDEX.md`. Wave-3 (~9 escalation-prone
families deferred pending design review) is the remaining scope. Real measured size: **193
modules** touch `SpecialCases` per the most recent scan referenced in prior sessions — this is a
large campaign and should get a fresh `dev-audit-tier2` hot-spot pass before resuming, rather than
trusting the stale wave-3 family list.

### Declined (carried forward, do not re-propose)

- **C2** (preventive lint rule to stop future interpreted-`positivity`/`nlinarith` regressions) —
  **declined by user**. Do not re-propose unless user reopens the topic.
- **C1 remaining 32 `positivity` sites in `HLSSharpPairBound.lean`** — measured and declined this
  session (0.19s aggregate / ~3% of module, ROI-insufficient); the user's original "~30 sites"
  authorization for this specific item was formally returned via the #4706 closing comment. A
  fresh authorization would be needed to revisit.

## Resume protocol

1. `docs/index.md` (progress table, single source of truth for "what's next" content).
2. `git log` on main (current HEAD after this session: `673aabd8`).
3. This handoff doc.
4. `.self-local/issues/` mirrors: `4706.md` / `4700.md` / `4701.md` (all closed, full history),
   `4704.md` (open, tracking, 9/156), `4692.md` / `4559.md` (open, user-approval-pending close).

**Reminder carried forward**: builds strictly serialized (≤1 concurrent Lean build in this repo's
current constraint framing — verify against CLAUDE.local.md / memory for the exact concurrency cap
in force this session, since prior notes mention both "≤3 concurrent Lean procs" and "no `-j`
serialize builds"; when in doubt, serialize to 1 for build vs. review overlap).

## Next-session confirmation items (user action required — do not resolve autonomously)

Added 2026-07-25 by `dev-pr-clerk` after correcting the #4563/#4642 GitHub bodies (issue-manager
governance re-verification). None of these are executed; all require the user's own decision:

1. **#4692 / #4559 close approval** — all technical work is disposed (Option-D reference-0
   campaign umbrella + folded-in predecessor); only the close itself is withheld pending user
   approval per `feedback_approval_required`.
2. **#4704 implementation authorization** — the issue body itself declares "tracking only,
   implementation to be authorized separately"; no scope has been authorized yet (9 stale
   `docs/index.md` refs + 156 stale `tex/proof-guide.tex` refs, needs a per-declaration audit
   before any deletion/fix, see #4704 body for detail).
3. **#4563 standing authorization currency** — confirm whether the 2026-07-18 "Blanket
   Authorization Record" is still considered in force. Reasons this needs re-confirmation rather
   than being assumed valid: (a) this repo's `gh` comments are all posted under the single
   `phasetr` account regardless of whether the words are the user's own or an agent's paraphrase,
   so the record has no independently verifiable primary-source text; (b) it has gone unexercised
   for 6 days / 100+ commits since the last family PR (#4573, merged `45b770d7`, 2026-07-19),
   during which the user issued several other item-specific authorizations (Option-B/C1) without
   invoking this one. GitHub body corrected 2026-07-25 to state this explicitly (was previously
   silent on the question).
4. **#4642 disposition** — either (A) close as `not planned` (this is `dev-issue-manager`'s
   recommendation — the true residue is only 3 reference-0 declarations K0/K2/K4, all docs-gated,
   net value is negative once the required docstring/tex retraction is counted), or (B) authorize
   the keep-criterion-(f) override (retract the `AlternatingCompleteGraph.lean:24-25` `c(K_4)=-6`
   docstring + corresponding `tex/proof-guide.tex` prose) and retire K0/K2/K4 in a follow-up PR
   (K1 and K3 must stay regardless — they are load-bearing / docs-cited, not deletable under
   either option).

## Repo hygiene note — benchmark worktree pollution in repo-wide scans

`.self-local/benchmarks/4519/*/worktrees/` contains full duplicate copies of the repo tree (left
over from the #4519/#4506 measurement-protocol campaign). A repo-wide `grep`/`rg` without a path
restriction picks up these duplicates as false positives — this session's scan for the
`SusceptibilityPointwiseRegularity*` family measurement returned ~181KB of duplicate noise from
this source before the scope was narrowed to `IsingModel/`. **Future repo-wide scans should either
restrict to `IsingModel/` (or the specific subtree under audit) or exclude `.self-local/benchmarks/`
explicitly.** Deleting the benchmark worktree artifacts themselves is a candidate cleanup but is
**not performed here** — it requires user approval (the artifacts are preserved evidence from a
prior measurement campaign, per `.self-local/issues/4519.md`).
