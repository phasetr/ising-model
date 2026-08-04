## 2026-08-04 PR #4892 merged (import-hygiene PR-A, edges 1/2 of #4889 REMOVE), edge 4 KEEP, edge 3 open (PR-B)

- **PR #4892 squash-merged** (`refactor/4889-import-hygiene-pr-a` -> `main`, commit
  `5f935ba54e9c06dde1c4ea68f42b168fcf41504a`), all checks green (`build`, `discover`,
  `evaluate (4892)`, `import-dag-contract`, `completion-claim/live`). Removed edge 1
  (`CubicMayerClusterFreeEnergyComplex -> LatticeBoundaryBED`) and edge 2
  (`LatticeFreeEnergyInfiniteKPBound -> NeighborDegree`) with compiler-backed evidence
  (`dev-review` APPROVE-equivalent after record fixes, `dev-audit-tier1` PASS,
  `dev-issue-manager` resolution-verification PASS). Remote tip confirmed matching reviewed head
  before merge; local and remote branch deleted.
- **Issue #4889 kept OPEN** (edge 3 not yet resolved); body updated to record edge-by-edge
  status: edges 1/2 REMOVE (PR #4892), edge 4 KEEP (compiler evidence: prototype removal fails
  with 8x Unknown identifier errors for `latticeGraph`/`cubicExhaustion`), edge 3 not yet
  started (PR-B, Shake proposes REPOINT `PlusHighTempRepresentation -> CubicBoxScreening` to
  `Inequalities.MonotonicityExtremal`).
- Mirror updated: `.self-local/issues/4889.md`.

## 2026-08-03 8 new issues filed (#4883-#4890), 3 closed as rollback-duplicates, #4884 premise corrected

- **Correction: the "zero open issues remain" claim below (2026-08-03 entry) is stale.** 8 new
  issues were filed the same day: #4883-#4890, none previously mirrored here.
- **#4885, #4886, #4887 closed as duplicates of rolled-back work.** All three re-proposed
  content from PR #4821/#4824 (finite-volume lattice wrapper cluster B, `Spin.sign_mul`
  canonicalization, complex lattice wrapper clusters C/D), which were merged and then
  **explicitly reverted at the user's own instruction** on 2026-08-01 (see close comments on
  #4823 and #4826, both timestamped 2026-08-01T04:35Z). Closed with cross-references to #4884
  and #4823.
- **#4884's premise corrected.** Original framing ("how did the ledger acquire a merged claim
  inconsistent with current main") mischaracterized this as a ledger-integrity bug. Corrected:
  #4820/#4821/#4824 genuinely merged (`167ff124`/`4bfe4aeb`/`e5b7675c`) and were then
  deliberately rolled back at the user's instruction — current main correctly lacking those
  declarations is the intended end state, not a defect. Noted that `docs/index.md` and this
  INDEX had zero prior record of the episode (only in uncommitted auto-memory), which is why
  #4885/#4886/#4887 were re-filed. Scope narrowed to: (a) add a durable repo-tracked record of
  the episode, (b) confirm main HEAD has zero residual traces of the rolled-back declarations.
- **Open after this pass**: #4883 (parent tracker), #4884 (narrowed), #4888, #4889, #4890.
  **Closed**: #4885, #4886, #4887 (rollback-duplicates, this pass).
- Mirrors created: `.self-local/issues/4883.md` through `4890.md` (all 8, new).

## 2026-08-03 PR #4881 merged, #4879 CLOSED completed, zero open issues remain

- **PR #4881 squash-merged** (`docs/4879-pr-b1-dangling-citations-remaining` -> `main`, commit
  `5197b4842b19d178d0a1af83688c681346a8c315`), all checks green (`build`, `discover`,
  `evaluate (4881)`, `import-dag-contract`, `completion-claim/live`). Fixed all 107 remaining
  dangling PR-B1 (#4298, `109690bd`) declaration-name citations across 5 `tex/proof-guide.tex`
  paragraphs and 20 `docs/index.md` rows (1662, 1663, 1682-1694, 1701-1705). Independently
  verified (`dev-verify`: all pass, exhaustive re-scan of all 196 declarations from the 30
  removed PR-B1 modules found 129 -> 0 occurrences across both documents, `citation_audit`
  ratchet clean, box regression re-derived 1657 -> 1653 = 4 removed/0 added/0 moved) and reviewed
  (`dev-review` + codex: one Med declaration-count off-by-one in prose found and fixed in
  follow-up commit `9567c3c7`, one optional Low disclosure added, two informational/pre-existing
  notes not blockers). Remote tip confirmed matching reviewed head, CI green, `git diff
  main..origin/branch` non-empty before merge; local and remote branch deleted.
- **Issue #4879 closed as completed**:
  https://github.com/phasetr/ising-model/issues/4879#issuecomment-5166198120 — all 107 dangling
  names confirmed fixed, preserved live citations (docs rows 1662-1663/1695-1700, tex line 6587+)
  confirmed byte-identical/unmodified.
- **This closes the last known tracked backlog item from the #4866 -> #4869 -> #4874 -> #4879
  citation-cleanup campaign chain**: `gh issue list --state open` returns **zero** open issues
  immediately after this close. Flagging for main's final governance check on whether this
  campaign, or any other tracked work, is genuinely fully closed out.
- Mirror note: `.self-local/issues/4879.md` is untracked and gitignored (confirmed via
  `git ls-files` / `git check-ignore -v`) and does not exist on disk; no per-issue mirror file
  edit was made for #4879, consistent with the repo's existing pattern for this file.

## 2026-08-03 PR #4878 merged, #4874 CLOSED completed, backlog #4879 filed (107 remaining)

- **PR #4878 squash-merged** (`docs/4874-pr-b1-dangling-declaration-citations` -> `main`, commit
  `de301fdb4b052eb96e3adb2ed1c9abb2d57fe9e3`), all checks green (`build`, `discover`,
  `evaluate (4878)`, `import-dag-contract`, `completion-claim/live`). Fixed all 8 in-scope
  paragraphs (5 in `tex/proof-guide.tex` + parallel `docs/index.md` rows): 2 relocated onto live
  reconstruction lemmas (Perron-Frobenius finite-volume spin two-point decay rows 1621/1622), 6
  converted to honest historical/no-live-equivalent framing after a confirmed exhaustive search
  (`topDeflat*`/`allOnesMatrix*`/`vectorAbsRatioSup` etc. all 0 occurrences in `IsingModel/`).
  Independently verified (`dev-verify`: all pass, Overfull/Underfull box list byte-identical to
  main's 1657-entry ordered list) and reviewed (`dev-review` + codex: no High/Med, one Low
  namespace-membership overclaim affecting 3 of 7 declarations fixed in follow-up commit
  `6f9e95da` and re-verified before merge). Remote tip confirmed matching reviewed head, CI green,
  `git diff main..origin/branch` non-empty before merge; local and remote branch deleted.
- **Issue #4874 closed as completed**:
  https://github.com/phasetr/ising-model/issues/4874#issuecomment-5165083442 — citation_audit
  ratchet clean (31 cleared, 0 new).
- **New backlog issue #4879 filed** (same filed-not-authorized pattern as #4866/#4869/#4874,
  larger-scope continuation): a repo-wide scan of all 231 PR-B1-removed declaration names against
  `tex/proof-guide.tex` + `docs/index.md` found **164 dangling names before PR #4878, 107
  remaining after it** — substantially larger than #4874's original ~10-paragraph estimate,
  concentrated in paragraphs *not* covered by #4874's scope: `tex/proof-guide.tex` ~lines
  6503/6527/6544/6562/6582 and `docs/index.md` rows ~1662/1663/1682-1705. Body states the exact
  counts and locations and explicitly does not prescribe or attempt investigation/fix; requires
  the same per-paragraph rigor #4874 received before any edit.
- Mirrors updated: `.self-local/issues/4874.md` (new, CLOSED completed).

## 2026-08-03 PR #4876 merged, #4869 CLOSED completed

- **PR #4876 squash-merged** (`refactor/4869-retire-viaLocal-direct-duplicate` -> `main`, commit
  `a3887fd358cf658720bfa3cee863864855b2a322`), all checks green (`build`, `discover`, `evaluate`,
  `import-dag-contract`, `completion-claim/live`) and independently reviewed (dev-review + codex,
  no High/Med findings, one Low non-blocking note already tracked under #4874). Local and remote
  branch deleted; the implementer's `.self-local/worktrees/4869` git worktree also removed.
- **Merge mechanics note**: `gh pr merge --squash` initially failed with `mergeStateStatus:
  BEHIND` despite `mergeable: MERGEABLE` (the 1-commit gap to `main` was docs-only mirror sync,
  unrelated files). Resolved by merging `origin/main` into the feature branch (no conflicts),
  pushing (`bfdcb2b5` -> `37e277de`), waiting for CI to re-pass, confirming `mergeStateStatus:
  CLEAN`, then squash-merging.
- **Issue #4869 closed as completed**:
  https://github.com/phasetr/ising-model/issues/4869#issuecomment-5164059844 — retired the
  byte-identical duplicate `toRangeRelCompactData_viaLocal_direct` (zero in-repo consumers);
  doc comments in `ViaLocal.lean`/`RelCompact.lean` and citations in `docs/index.md`/
  `tex/proof-guide.tex` updated in the same commit; two independent verify/review passes
  confirmed no regression (citation_audit ratchet clean, Overfull/Underfull box count
  regression-checked, census/citation-row pins re-measured correctly).
- **Main confirmed green post-merge**: both `Lean Action CI` and `Completion Claim Live` on
  `a3887fd3`.
- Mirrors updated: `.self-local/issues/4869.md` (new, CLOSED completed).

## 2026-08-03 PR #4873 merged, #4866 CLOSED completed, backlog #4874 filed

- **PR #4873 squash-merged** (`docs/4866-relocate-removed-layercylinder-spectral-decay-citations`
  -> `main`, commit `a1681abbf1a11a02f0c34f3ee4140521466e6053`), all checks green (`build`,
  `discover`, `evaluate`, `import-dag-contract`, `completion-claim/live`). Local and remote branch
  deleted.
- **Pre-merge body fix**: the PR body was stale w.r.t. HEAD `86b3bd47` (claimed `docs/index.md`
  untouched and repin "26912 -> 26926 / +14 lines" when the follow-up commit had already fixed
  `docs/index.md:1642` for the same six names and the real repin was 26912 -> 26931 / +19 lines).
  `dev-pr-clerk` corrected the body via `gh pr edit --body-file` before merge; CI's `discover`
  job re-fired on the edit and re-passed before the merge gate check.
- **Issue #4866 closed as completed**:
  https://github.com/phasetr/ising-model/issues/4866#issuecomment-5163662831 — both
  `tex/proof-guide.tex` and `docs/index.md:1642` fixed for the same six dangling declaration
  names (module `TransferMatrix/LayerCylinderSpectralDecay.lean` deleted by `109690bd`, #4298
  PR-B1); citation-audit ratchet OK, `QualifiedGlobCitationTest` repin 26912 -> 26931 confirmed.
- **New backlog issue #4874 filed** (same filed-not-authorized pattern as #4866/#4869): tracks
  ~10 further PR-B1-era paragraphs (tex lines ~7014/7036/7058/7328/8335/8378/8405/8437/8557/33174)
  with at least 16 further declaration names charged at zero occurrences in `IsingModel/`, several
  confirmed deleted by `109690bd`. Root cause noted: `citation_audit.py` audits `.lean` **paths**
  only, never declaration names, so this defect class is invisible to every existing gate.
- Mirrors updated: `.self-local/issues/4866.md` (CLOSED completed, pre-merge defect section marked
  corrected, follow-up section cross-referenced to filed #4874).

## 2026-08-03 PR #4871 merged, #4830 AC4 re-verified PASS, tracker CLOSED completed

- **PR #4871 squash-merged** (`docs/4830-qualify-bare-lean-citations` -> `main`, commit
  `b32a45bceaf0359093106a51ede05b2f2792c927`), all checks green (`build`, `import-dag-contract`,
  `discover`, `evaluate`, `completion-claim/live`) and independently reviewed (dev-review + codex,
  one Med finding — a new Overfull hbox in the public PDF — fixed in follow-up commit `bac772cd`
  with measured before/after proof). It qualified the four bare `.lean` basename citations that
  PRs #4839/#4840 had introduced and repinned the downstream `QualifiedGlobCitationTest` line
  numbers. Local branch deleted (`--delete-branch`).
- **AC4 re-verified on post-merge `main`**: `python3 scripts/citation_audit.py` now reports
  `ratchet: OK -- 31 finding(s) cleared, 0 new` / `citation audit: PASS`. This was the sole unmet
  item of #4830's 8-item "Common acceptance criteria" checklist per the prior
  `dev-issue-manager` pass (below); all 8 (AC1-AC8) are now SATISFIED.
- **#4830 closed as completed**: https://github.com/phasetr/ising-model/issues/4830#issuecomment-5162934494
  Summary: real implementation work #4850 (PR #4856), #4851 (PR #4859, reduced scope), #4857
  (PR #4862), #4854 (PR #4868, single-group pilot with an explicit "STOP -- no rollout to the
  other 22 groups" checkpoint); declined not-planned #4852/#4853 (audit gate failed on its own
  stated threshold); first-wave children #4831/#4832/#4833/#4834/#4835/#4836/#4837 per their own
  closure records; #4869 referenced as an out-of-scope-for-this-tracker follow-up (duplicate
  data-layer declaration found during #4854's review), not a 14th sub-issue. AC4's citation-audit
  regression (from #4839/#4840) was caught and fixed by PR #4871 before closing this tracker.
- Mirrors updated: `.self-local/issues/4830.md` (CLOSED completed, AC4 section marked superseded),
  `.self-local/issues/4854.md` (cross-reference to parent's closure).

## 2026-08-03 dev-issue-manager holistic acceptance-criteria verification of tracker #4830 — 7/8 SATISFIED, AC4 UNMET, tracker NOT closed despite 13/13 sub-issues

- **Verdict: DO NOT CLOSE #4830.** All 13 native sub-issues are resolved
  (`sub_issues_summary` = 13/13, 100%: first wave #4837/#4832/#4833 completed and
  #4831/#4834/#4835/#4836 declined not planned; second wave #4850/#4851/#4857/#4854 completed and
  #4852/#4853 declined not planned), but the parent body's **"Common acceptance criteria" are 8
  items, of which AC8 ("every child completed or explicitly declined") is only one**. Verified
  holistically against `main` `a7c1dfad93b5b35c3767c90c6aba10c0ea2df149` (clean tree):
  **AC1/AC2/AC3/AC5/AC6/AC7/AC8 SATISFIED, AC4 UNMET.**
- **AC4 failure (the blocker)**: the criterion requires "documentation/citation checks pass".
  `python3 scripts/citation_audit.py` reports `ratchet: FAIL -- 4 finding(s) above the baseline`,
  and its own `RealTreePinTest` self-tests fail on the same tree, so this is a genuine tree
  regression rather than a tool defect. The four findings are
  `NEW BASENAME_ONLY docs/index.md BetaDerivativeFieldJ.lean (0 -> 2)`,
  `docs/index.md MagnetizationPointwiseRegularityFieldJ.lean (0 -> 1)`,
  `tex/proof-guide.tex BetaDerivativeFieldJ.lean (0 -> 1)` and
  `tex/proof-guide.tex BetaDerivativeMagnetization.lean (0 -> 1)`. `git blame` attributes every
  offending line to this tracker's **own** children — `6147071c` (PR #4839, #4837 stage A1;
  `tex:21437,21453`, `docs/index.md:1999`) and `e3a0dc01` (PR #4840, #4837 stage A2; `tex:23936`,
  `docs/index.md:1832,1992`) — and `scripts/audit/citation_baseline.tsv` has not moved since the
  pre-wave commit `ee981926`, so the ratchet is measuring the wave, not baseline drift.
  **Why it escaped**: `citation_audit.py` and `test_citation_audit.py` are not wired into
  `.github/workflows/lean_action_ci.yml` (which runs `audit_gate.py`, `dead_candidate_scan.py`,
  `import_dag_contract.py` and the completion-claim gates), so both PRs merged green.
- **Everything else re-verified positively, on the current tree rather than from merge-time
  claims**: `lake build` 4944 jobs exit 0 with zero warnings (`lakefile.toml` has
  `warningAsError = true`, so a green build is itself the zero-warning proof); `lake exe GKSTest`
  exit 0; `audit_gate.py --full` exit 0; `import_dag_contract.py --check` PASS; `#print axioms` on
  11 representative wave-touched declarations all `[propext, Classical.choice, Quot.sound]`;
  the #4854 compatibility aliases and #4857's relocated declarations exist under their original
  public names. Deletion sweep (AC5): the wave truly removed 6 declaration names plus the duplicate
  `Lebowitz.sum_spin`, and an independent normalised sweep (backslash/brace/whitespace/underscore
  insensitive, so `\_` escapes and line-split `\texttt{}` spellings cannot hide) over `tex/`,
  `docs/**`, `README.md` finds **0** dangling references. Import closure (AC6/AC7), measured over
  all 1874 modules from baseline `f23fa1e7` to `a7c1dfad`: **579 decreased, 1294 unchanged, 1
  increased** — `Inequalities.MonotonicityField` 6 -> 8, exactly the increase PR #4862 disclosed in
  advance with net-new-modules 0. #4837's missing numeric closure figure was supplied
  retrospectively (120 -> 106, 120 -> 106, 118 -> 105, all decreases). Caveat recorded: cold-build
  wall-clock and RSS were never measured by any child, so those two AC7 thresholds were unexercised
  rather than violated.
- **Remediation before #4830 can close** (docs/TeX only, no Lean change): qualify the 4 bare
  basenames with their directory paths (e.g. `IsingModel/AmbientLattice/BetaDerivativeFieldJ.lean`)
  at `docs/index.md:1832,1992,1999` and `tex/proof-guide.tex:21437,21453,23936`, re-run
  `citation_audit.py` and `--self-test` to green, and repin `scripts/test_dead_candidate_scan.py`
  in the same PR because the TeX edits shift line numbers (same pattern as `4e3288cf`). Separate
  governance decision worth taking: wire `citation_audit.py` into CI.
- **Scope rulings restated**: **#4869** (byte-identical `toRangeRelCompactData_direct` /
  `_viaLocal_direct` in `AscoliData/ClosedBallConversions/DeviationDirect.lean`) stays an
  independent backlog issue, **not a 14th sub-issue**, to be referenced from #4830's eventual close
  comment. **#4866** is not this wave's debt either: its dangling citations come from `109690bd`
  (2026-06-26, #4298), a verified ancestor of the wave baseline `f23fa1e7`.
- `.self-local/issues/4830.md` updated with the same per-criterion verdict; the tracker's GitHub
  body was **not** edited and the issue was **not** closed.

## 2026-08-03 dev-pr-clerk process-gap remediation — PR #4868 body/evidence fixed, #4869 filed (duplicate data-layer twin backlog), #4830/#4866 mirrors fixed

- **PR #4868 body rewritten** (`.self-local/tmp/pr4868-body.md`): removed the stale
  `## Status: Implementation to follow on this branch.` placeholder (implementation was already
  pushed at `0a52f59c`/`ca402258`); corrected the "Disclosed cost" section's false blanket claim
  ("this repo does not run reference-0 deletion campaigns") to the narrower, corrected framing
  from `ca402258`'s commit message (scope, not policy — citing counter-examples #4641/#4749/
  #4751/#4764/#4839/#4851); rewrote `Refs #4854 (do not close it yet …)` into a standalone
  `Refs #4854` trailer line (fixes `completion-claim/live`'s `AMBIGUOUS_NON_CLOSING_DIRECTIVE`
  per `docs/completion-claims.md`'s standalone-trailer rule), moving the "don't close yet"
  explanation into a separate `## Notes` prose paragraph.
- **Evidence posted as a tracked PR comment**
  (https://github.com/phasetr/ising-model/pull/4868#issuecomment-5161896717), synthesized from
  the gitignored `.self-local/reports/review-4854-closedball-alias-pilot.md`: statement-
  preservation confirmation (byte-identical signatures + elaborated-type `rfl` checks), the
  4-declaration consumer citation table for the identical-statement group (3 in pilot scope + the
  1 deliberately-excluded 4th sibling with its own consumers), confirmation the TeX sweep covered
  both `\_` and `_` citation forms, argument-mapping and build/axiom health evidence. Also
  recorded #4830's secondary measurements: import closure for the 3 touched files is unchanged
  (zero `import`-line diff, `git diff main..ca402258`), and `lake build` CI wall-clock shows no
  meaningful change (main recent green run 3m58s vs this PR's head 5m29s-to-an-unrelated-failure,
  consistent with a proof-body-only change).
- **New backlog issue filed**: **#4869** — `AscoliData/ClosedBallConversions/DeviationDirect.lean`
  `toRangeRelCompactData_direct` (L45-62) and `toRangeRelCompactData_viaLocal_direct` (L69-86) are
  byte-identical in signature and body (same duplicate-twin pattern as #4852/#4853, one layer
  deeper), found during #4868's independent review. Filed as an **independent** issue per
  `dev-issue-manager`'s explicit ruling — NOT a #4830 sub-issue, to be referenced from #4830's
  eventual close comment rather than counted in its 12/13 (soon 13/13). Not authorized for
  immediate work.
- **`.self-local/issues/4830.md` internal contradiction fixed**: the "Sub-issue progress" heading
  said "current authoritative figure is 10/13, 76%" while the body's live re-query further down
  said 12/13, 92% (re-verified live via `gh api`/GraphQL this session: 12 CLOSED + #4854 OPEN =
  12/13, 92%, unchanged since the prior INDEX entry). Heading corrected to point at the 12/13
  figure and clarify that the per-item percentages inside the first-wave list are individually
  superseded incremental snapshots, not the current total.
- **`.self-local/issues/4866.md` mirror created** (previously missing despite #4866 being OPEN
  since 2026-08-03 per the INDEX entry below) — dangling-TeX-citation tracked backlog, not
  started, template matches `4852.md`.
- **Not done (explicitly out of clerk scope this pass, per instructions)**: PR #4868 not merged
  (CI `build` is currently FAILING on an unrelated pinned self-test —
  `test_dead_candidate_scan.py::QualifiedGlobCitationTest`, a `tex/proof-guide.tex` line-number
  fixture that appears to have drifted from this pilot's own doc edits; `completion-claim/live`
  also fails `AMBIGUOUS_NON_CLOSING_DIRECTIVE` pre-fix, not yet re-checked post body-edit); #4854
  not closed; #4830 not closed.

## 2026-08-03 dev-pr-clerk close sync — #4853 declined not planned, #4866 filed (new dangling-TeX-citation finding), second-wave 5/6, sub_issues_summary 12/13

- **#4853 closed `not planned`** (`gh issue close 4853 --reason "not planned"`, closing comment
  https://github.com/phasetr/ising-model/issues/4853#issuecomment-5161471010). An independent
  design pass verified the issue's own audit gate directly against the current tree and found
  FAIL on the first criterion: both current capstone consumers of the shared ratio algebra are
  on the open path
  (`correlation_layerOpenSlabGraph_same_transverse_abs_le_of_openMinSpectralGapCertificate`,
  `LayerOpenSlabGraph.lean:538`;
  `correlation_layerOpenSlabGraph_two_transverse_abs_le_of_boundarySpectralDenominator`,
  `LayerOpenTwoMarkedSpectralDecay/Certificate.lean:253`). The cyclic/balanced decay theorems
  have zero external consumers and their former capstone was deleted in `109690bd` (#4298
  PR-B1), so the issue's own "one cyclic/balanced + one open" ≥2-consumer gate is not
  constructible today; sharing beyond the four scalars and five sign conditions needs
  higher-order numerator/denominator plumbing (the explicit non-goal). A fifth structure sharing
  the same fields/proof tail that the issue's file list omitted, `LayerOpenMinSpectralGapCertificate`
  (`LayerOpenSlab.lean:123`, 14 external consumers), was recorded for completeness — doesn't
  change the verdict. No core extraction authorized.
- **New unrelated finding from the same audit, filed as tracked backlog (not fixed)**: issue
  **#4866** — `tex/proof-guide.tex` lines 7561/7573/7580 dangling-cite three declarations from
  the `TransferMatrix/LayerCylinderSpectralDecay.lean` cluster, deleted by the same `109690bd`
  (#4298 PR-B1) commit. Checked against #4714/#4704 (a prior dangling-TeX-citation PR/tracker):
  #4704 is CLOSED `NOT_PLANNED` and neither its history nor #4714's mentions this
  `LayerCylinderSpectralDecay` cluster, so this is a genuine new recurrence, not something
  already covered — filed as a new, precisely-scoped issue rather than reopening #4704's broader
  (and declined) sweep scope. Not authorized for work this session (goal-scope discipline).
- **#4830 (master tracker) body updated**: second-wave checklist line for `#4853` flipped to
  `[x]` with verdict `declined (not planned)`, the closing-comment link, and a pointer to #4866;
  second-wave progress text updated to "5/6 resolved"; `sub_issues_summary` line updated to
  12/13, 92% (`gh api repos/phasetr/ising-model/issues/4830 --jq '.sub_issues_summary'` ->
  `{"completed":12,"percent_completed":92,"total":13}`).
- Mirrors updated: `.self-local/issues/4853.md` (status flipped to CLOSED not planned, Resolution
  section with the evidence + #4866 pointer appended), `.self-local/issues/4830.md` (subissue
  summary line, second-wave table row for #4853, second-wave progress line all updated to
  12/13, 92%).
- Remaining OPEN second-wave child: #4854 (P2, Patches canonicalization). New standalone tracked
  issue: #4866 (P-unset, dangling TeX citations, not a sub-issue of #4830).

## 2026-08-03 dev-pr-clerk close sync — #4852 declined not planned, second-wave 4/6, sub_issues_summary 11/13

- **#4852 closed `not planned`** (`gh issue close 4852 --reason "not planned"`, closing comment
  https://github.com/phasetr/ising-model/issues/4852#issuecomment-5161386998). `dev-research`
  measured the issue's own audit gate ("at least two current consumers of every extracted core
  theorem: the edge-avoidance route and the vertex-avoidance route") against the live tree and
  found FAIL: `FieldAvoidingRatio.lean`'s edge-route `Gavoid` (616 lines, 14 theorems) and
  `FieldVertexAvoidingRatio.lean`'s vertex-route `GavoidVertex` (714 lines, 23 declarations) are
  near-line-for-line duplicates and `GavoidVertex` already generalizes `Gavoid` definitionally
  (`Gavoid_eq_GavoidVertex_polymerSupport`, `FieldVertexAvoidingRatio.lean:79`, `rfl`), but the
  vertex route has real consumers (`FieldSourceWeightBound.lean:19`,
  `FieldCorrelationUniformBound.lean:57,99,136`, `FieldSourcePeel.lean`) while the edge route's
  own capstone `fieldPolymerZℂ_Gavoid_div_norm_le_exp` (`FieldAvoidingRatio.lean:551`) and every
  other declaration in that file have zero code-level consumers anywhere in the live tree
  (grep-verified). Same pattern as #4831/#4834/#4835/#4836's audit-gate failures. No core
  extraction authorized; `Gavoid`/`GavoidVertex` unchanged.
- **#4830 (master tracker) body updated**: second-wave checklist line for `#4852` flipped to
  `[x]` with verdict `declined (not planned)` and the closing-comment link; second-wave progress
  text updated to "4/6 resolved"; `sub_issues_summary` line updated to 11/13, 84%
  (`gh api repos/phasetr/ising-model/issues/4830 --jq '.sub_issues_summary'` ->
  `{"completed":11,"percent_completed":84,"total":13}`).
- Mirrors updated: `.self-local/issues/4852.md` (status flipped to CLOSED not planned, Resolution
  section with the evidence matrix appended), `.self-local/issues/4830.md` (subissue summary line,
  second-wave table row for #4852, second-wave progress line all updated to 11/13, 84%).
- Remaining OPEN second-wave children: #4853 (P1, spectral-gap numeric core audit), #4854 (P2,
  Patches canonicalization).

## 2026-08-02 dev-pr-clerk merge sync — #4857 completed, second-wave 3/6, sub_issues_summary 10/13

- **PR #4862 squash-merged** to `main` as commit `c3bfdc4072cb93ec48b6253b5fa5b640e2111246`
  (title: "refactor: move gibbsExpectationBC_field_mono generic block to MonotonicityField
  (#4857)"). `gibbsExpectationBC_field_mono` and its supporting block relocated verbatim from
  `Concrete/LatticeGraphCorrelation/MagnetizationFieldMonotone.lean` into
  `Inequalities/MonotonicityField.lean`; `MonotonicityBetaBoundaryCondition.lean` retargeted;
  import-DAG contract INFO edge count 27 -> 26. Branch head required a GitHub-side update
  (`PUT .../pulls/4862/update-branch`) to merge `main` (which had advanced with #4863's
  completion-claim gate relaxation) before merge, per branch protection's "up to date" requirement;
  all checks (build, import-dag-contract, discover, completion-claim/live, evaluate) passed green
  on the updated tip before squash-merge.
- **#4857 closed completed** (`gh issue close 4857 --reason completed`), all five acceptance
  criteria checked off in `.self-local/issues/4857.md`. This issue's full scope was covered by the
  single PR; nothing carries forward under its number.
- **#4830 (master tracker) body updated**: second-wave checklist line for `#4857` flipped to `[x]`
  with the completed verdict and merge commit; progress line corrected 2/6 -> 3/6, combined-wave
  figure 9/13 -> 10/13 (cross-checked against GitHub's native `sub_issues_summary` =
  `{"completed":10,"percent_completed":76,"total":13}`).
- **Mirrors synced**: `.self-local/issues/4857.md` (status flipped to CLOSED completed, resolution
  section + checked acceptance criteria added), `.self-local/issues/4830.md` (second-wave table row
  for #4857 flipped to CLOSED completed, progress corrected 2/6 -> 3/6).
- `docs/index.md` was already synced by the PR itself (both the §4.1 `MonotonicityField.lean` row
  and the §3.6/#3599 `MagnetizationFieldMonotone.lean` row correctly attribute the relocation to
  #4857) — no additional edit needed post-merge.
- Local branch cleanup: no local checkout of the feature branch existed at merge time (working
  directory was already on `main`); remote branch deleted via `gh pr merge --delete-branch`;
  confirmed absent both locally (`git branch --list`) and on origin (`git ls-remote`).

## 2026-08-02 dev-pr-clerk INDEX sync — #4857 filing recorded as an independent entry, second-wave denominator corrected 2/6, sub_issues_summary 9/13

- **#4857 filed 2026-08-02 as a native sub-issue of #4830 (P0/P1)**: "restore generic ownership of
  `gibbsExpectationBC_field_mono`" — `IsingModel/Inequalities/MonotonicityBetaBoundaryCondition.lean:3`
  imports `Concrete.LatticeGraphCorrelation.MagnetizationFieldMonotone` only to obtain
  `gibbsExpectationBC_field_mono` (`MagnetizationFieldMonotone.lean:120-141`), which is fully
  generic over `(G : SimpleGraph ι) [Fintype G.edgeSet]` with no ℤ^d/`cubicBox` dependency in its
  statement or proof — the same ownership-violation shape as the previously fixed
  `boltzmannWeightJ_uniform_eq` relocation (#4833). Spun off from #4850's own AC2 ownership audit
  (`.self-local/reports/research-4850-audit-gate-l2-l4-edges.md` row 21), out of #4850's bounded
  pilot scope. Proposed fix: relocate the declaration to a non-`Concrete` generic owner module,
  preserving the public statement, with a compatibility alias if needed. OPEN, not started.
  Mirror: `.self-local/issues/4857.md`. (Previously this filing was recorded only in prose inside
  the prior #4850-entry below; this is its own INDEX entry.)
- **Second-wave denominator corrected 2/5 → 2/6, and combined-wave figure added**: #4857's filing
  makes the second-wave programme six children (#4850, #4851, #4852, #4853, #4854, #4857), not
  five. Second-wave progress is **2/6 completed** (#4850, #4851). Combined with the seven-child
  first wave, GitHub's native `sub_issues_summary` = **9/13 completed (69%)** across both waves.
  These corrections are already reflected on GitHub #4830's body (checklist lists `#4857` under
  "Second-wave plan (2026-08-02)", states "2/6 completed", "GitHub `sub_issues_summary` = 9/13
  across both waves") and in `.self-local/issues/4830.md` (`sub_issues_summary` = 9 completed /
  13 total, 69%; "Second-wave progress: 2/6 completed") — both corrected ahead of this INDEX
  entry; this entry brings the INDEX up to the same state.

## 2026-08-02 dev-pr-clerk merge sync — #4851 completed (reduced scope), #4830 checklist updated 2/5

- **#4851 CLOSED (completed, reduced scope)**: merged via PR #4859
  (`refactor/4851-fourfoldsite-dedupe`), squash-merge commit
  `261322222e853b25f9cd480452f263aacaf3e50a` on `main`. Retired the duplicate
  `IsingModel.Lebowitz.sum_spin` declaration (`FourfoldSite.lean:34-37`), a specialization
  (`α := ℝ`) of the general `IsingModel.sum_spin {α} [AddCommMonoid α]`
  (`IsingModel/GibbsMeasure.lean:224`); no call-site/import/proof-text changes. `docs/index.md`
  and the `scripts/test_dead_candidate_scan.py` declaration-census pins (`10567 → 10566`) synced
  in the same PR. CI green (`build`/`import-dag-contract` pass; `completion-claim/live`/
  `evaluate` fail per the known structural gh-auth-user=PR-author cause, consistent with recently
  merged #4848/#4856); `dev-verify` independent build re-verify (2x), `dev-review` (Claude +
  codex) verdict MERGE (no High/Med findings), `dev-audit-tier1` findings addressed,
  `dev-issue-manager` resolution verification = resolved. Mirror `.self-local/issues/4851.md`
  updated OPEN → CLOSED (completed, reduced scope) with resolution summary. **Scope note**: the
  original AC's full `GibbsMeasure`-independence move remains parked as a #4830 Non-goals P2
  candidate pending explicit user authorization; not reopened by this closure.
- **#4830 (master tracker) body updated**: second-wave checklist line for `#4851` flipped
  `[ ] → [x]` with `— completed (reduced scope)` and the parked-P2 note; second-wave progress
  recorded at the time as **2/5** (#4850, #4851) — this predates #4857's filing later the same
  day; see the corrected **2/6** entry above.

## 2026-08-02 dev-pr-clerk merge sync — #4850 completed, #4830 checklist updated

- **#4850 CLOSED (completed)**: merged via PR #4856 (`refactor/4850-gksboundary-import-repoint`),
  squash-merge commit `ac942a458f27d3a12b723b9fad943bdfe610ede8` on `main`. Import-line repoint
  (`GKSBoundaryCondition.lean:3` `Concrete.LatticeGraphCorrelation.CubicBoxScreening` +
  `FKGBoundaryCondition` → single `IsingModel.Inequalities.MonotonicityExtremal`) confirmed as the
  full pilot; no declaration added/removed/renamed/moved. Measured: `IsingModel`-level static
  import closure **182 → 13** modules; `import_dag_contract.py`'s unranked
  `L2_THEORY → L4_LATTICE/L5_CHAIN` `INFO_CEILING` ratchet **28 → 27**.
  `docs/architecture-import-layers.md` / `scripts/test_import_dag_contract.py` docstring synced in
  the same PR. AC2 (audit every non-`Concrete` → `Concrete.*` edge, record ownership verdict)
  satisfied per `dev-research` inventory (`.self-local/reports/research-4850-audit-gate-l2-l4-edges.md`);
  the one genuine ownership-violation edge found outside this bounded pilot's scope
  (`MonotonicityBetaBoundaryCondition.lean` → `MagnetizationFieldMonotone.lean`'s
  `gibbsExpectationBC_field_mono`) filed separately as #4857. Mirror `.self-local/issues/4850.md`
  updated OPEN → CLOSED (completed) with resolution summary.
- **#4830 (master tracker) body updated**: second-wave checklist line for `#4850` flipped
  `[ ] → [x]` with `— completed (PR #4856, merge commit `ac942a45`; AC2 ownership-violation edge
  tracked separately as #4857)`.

## 2026-08-02 dev-pr-clerk governance corrections — #4830 checklist sync, second-wave INDEX entry, #4850/#4851 premise fixes

- **#4830 (master tracker) body corrected**: the first-wave checklist (`#4831`/`#4832`/`#4833`/
  `#4834`/`#4835`/`#4836`/`#4837`) was self-contradictory — all 7 items showed unchecked `[ ]`
  boxes while the prose said "the initial seven-child programme is resolved". `gh issue view`
  confirms all 7 are CLOSED: **completed** = #4832, #4833, #4837; **declined (not planned)** =
  #4831, #4834, #4835, #4836. Body now checks each box and appends an explicit verdict word per
  line (not `[x]` alone, to avoid a declined item reading as completed).
- **Second-wave issues #4850–#4854 filed 2026-08-01/02, OPEN, no INDEX record until now**:
  - #4850 (P0) — restore the generic-to-Concrete ownership boundary around extremal
    configurations (`GKSBoundaryCondition.lean`).
  - #4851 (P0) — re-home `sum_spin` at its Spin-level owner (`FourfoldSite.lean` duplicate).
  - #4852 (P1) — audit a forbidden-edge core shared by edge- and vertex-avoidance proofs.
  - #4853 (P1) — audit/extract the shared numeric core of spectral-gap certificates.
  - #4854 (P2) — canonicalize one identical-statement Patches group with compatibility aliases.
  All five are children of #4830's "Second-wave plan (2026-08-02)" section; mirrors exist for
  all five (`4850.md`–`4854.md`) as of this entry.
- **#4850 body premise corrected**: original body proposed to "move the minimal concept-complete
  extremal-configuration slice to its generic owner". `dev-issue-manager` (main `496d0b5f`) found
  every declaration `GKSBoundaryCondition.lean` consumes (`plusConfig`,
  `partitionFunctionBC_pos`, `boltzmannWeightJ_uniform_eq`, etc.) already has a non-`Concrete`
  owner on current main; the real bounded pilot is a **single import-line repoint**
  (`GKSBoundaryCondition.lean:3` → `import IsingModel.Inequalities.MonotonicityExtremal`), not a
  declaration move. Body rewritten to state this; ownership table + closure measurement (182 vs
  12 modules) carried over from mirror `4850.md`.
- **#4851 body premise corrected**: original body said `FourfoldSite.lean` imports `GibbsMeasure`
  "for `sum_spin` alone" (implying it consumes `IsingModel.sum_spin`). `dev-issue-manager` found
  `FourfoldSite.lean:35` instead declares its own duplicate `IsingModel.Lebowitz.sum_spin` (the
  `GibbsMeasure.lean:224` general form is never referenced by this file), and the file uses
  **zero** Gibbs-layer names (`hamiltonian|boltzmann|partitionFunction|gibbs|correlation` all 0
  hits) — its IsingModel-layer dependency is `Basic` only; the replacement Mathlib import set is
  unmeasured (`dev-review`'s `lake env lean` swap to `IsingModel.Basic` alone hit missing
  `AddCommMonoid ℝ` / `CommRing ℝ` instances, and adding `Mathlib.Data.Real.Basic` left 5 further
  errors, so the current `import IsingModel.GibbsMeasure` is load-bearing as a transitive Mathlib
  supplier, not simply "unnecessary"). Body rewritten: debt = duplicate declaration; target
  IsingModel-layer owner = `IsingModel.Basic`, not a "move a consumed declaration" story. Carried
  over from mirror `4851.md`.
- Governance corrections only; no Lean/build change, no issue closed, no PR opened by this pass.

## 2026-07-30 audit checkpoint — #4786 hierarchy and #4803 evidence

- PR #4806 candidate `f425143c96c865d40efb401c24b49d0ffdd970ef` was
  squash-merged as `c2a06741c65c2f31d26d2c95af4aa78c3d304858`; both
  commits have tree `b9784c5ed3a82c7e7612033d0187478aba1e5c46`.
- Completion Claim Live
  [run 30539037148](https://github.com/phasetr/ising-model/actions/runs/30539037148)
  and Lean Action CI
  [run 30539037390](https://github.com/phasetr/ising-model/actions/runs/30539037390)
  succeeded on PR #4806 squash `c2a06741c65c2f31d26d2c95af4aa78c3d304858`.
- By the 2026-07-30 audit checkpoint, the two-file #4803 protocol and complete
  same-repository A–J lifecycle canary had merged.
- PR #4807 candidate `564ad7d2448b431894eaa3d38a09be836309c2db` was
  squash-merged as `2e87b4b1e1cacad5c98bf169cfd136ea6c717d9e`; both
  commits have tree `f81031ffe33b709839641cfa618f216b56b58874`.
- Completion Claim Live
  [run 30543098347](https://github.com/phasetr/ising-model/actions/runs/30543098347)
  and Lean Action CI
  [run 30543098366](https://github.com/phasetr/ising-model/actions/runs/30543098366)
  succeeded on PR #4807 squash `2e87b4b1e1cacad5c98bf169cfd136ea6c717d9e`.
- At the 2026-07-30 audit checkpoint, #4786, #4790, #4796, #4801, #4802,
  and #4803 were OPEN.
- At the 2026-07-30 audit checkpoint, the direct OPEN #4786 children #4788,
  #4789, #4790, #4791, #4792, #4793, #4794, #4795, and #4796 were governed
  by their own acceptance criteria.
- GitHub issue bodies and durable comments are canonical for current lifecycle
  state. This INDEX entry is historical and must not be read as a current-state
  assertion.

**2026-07-27 PR #4743 MERGED (dev-pr-clerk, main `2a3a9baf`)**: closed the `docs/index.md`
`MISSING` citation class (12 findings -> 0, 11 edited lines), completing the `MISSING`-class
lane opened by #4704 (tex side was already closed by #4741). Re-measured: gating
**972 -> 960**, advisory 94 -> 93, `docs/index.md` census 2698 -> 2693; `MISSING` now absent
from `citation_audit.py`'s output for both `tex/proof-guide.tex` and `docs/index.md`. #4704
GitHub title/body + mirror `4704.md` resynced to this count; **#4704 stays OPEN** (follow-ups:
row-2019 evidence-path umbrella wording, a spelling-form inconsistency, CI-wiring decision
pending). **Self-reported clerk defect (not amended, per no-main-amend rule)**: the PR body's
own corrective footnote for a line-count error (2,331 -> 2,330) quoted the wrong figure
inline, so the literal string `2,331` is present in the merged squash-commit body on `main`
(`2a3a9baf`) even though the actual `docs/index.md` line count is correctly 2,330 everywhere
else in that body — recorded here for a future corrective PR or explicit user decision, main
was not amended/force-pushed.

**2026-07-26 PR #4728 MERGED (dev-pr-clerk, main `365fb294`), session terminal state**: the
fail-closed citation auditor (`scripts/citation_audit.py` + `scripts/test_citation_audit.py` +
`scripts/audit/citation_baseline.tsv`) for `.lean` path citations in `tex/proof-guide.tex` and
`docs/index.md` merged (issue #4704 "Part of"; branch `refactor/4704-citation-checker` deleted,
CI green, `dev-verify`/`dev-audit-tier1`/`dev-review`+codex/`dev-issue-manager` all PASS/RESOLVED
before merge). No exemption channel of any kind (built and deleted again across 3 review rounds,
per `dev-principles`' twice-recurring-defect rule). Count-of-record: **1,272 gating findings**
(529 tex + 743 docs) **+ 95 advisory**. CI is **not** wired to it (separate authorization item).
**#4704** GitHub title/body resynced to this count (clerical, no authorization needed), retiring
157/268/285/"12 in docs, 159 in tex"; PR #4728 added to Scope 1 (Done); item 2(b)'s stated
precondition recorded satisfied (not authorization) — stays **OPEN**. Session totals: **15 PRs
merged**, aggregate build-time reduction **≈ −37s**. Closed this session: PR #4714 (user
instruction, not merged) + issues #4700/#4701/#4706/#4715/#4717/#4721. New issues this session:
#4704/#4709/#4718/#4724. **11 user-approval-pending items remain, next move = STOP-and-ask** (see
`.self-local/reports/handoff-2026-07-25-optionB-C1.md` EIGHTH UPDATE for the full list and
session lessons).

**2026-07-26 #4724 filed (dev-pr-clerk)**: build-speed numeric-discrepancy tracking issue —
measurement A (2026-07-18, #4563's decision basis, per-module fixed cost ≈7.0s) vs. measurement B
(2026-07-24/25 full-coverage `dev-perf` sweep, `.self-local/reports/perf-full-coverage-buildtime-4b14a205.md`,
1.55–2.19s/module) disagree by ~4.5x. Direction is **not** in dispute — both #4563 and measurement B
agree consolidation reduces build cost; only the magnitude is unresolved. Cross-referenced on #4563
(not closed); mirror `4724.md` created.

**2026-07-26 governance sync (dev-pr-clerk)**: (1) **#4721 mirror was missing** (build-speed
`Nat.cast_nonneg` A/B proposal, `dev-perf` measured -3.75s) — created (`4721.md`), verbatim from
the GitHub issue body, no implementation started. (2) **#4709 was stale** (title/body still said
"four false-claim incidents" while the actual count is **nine**: #4702/#4703/#4707/#4708 + #4710
(provenance-claim error) + #4711 (mis-stated codepoint count) + #4716 + #4720 (two rounds)) —
title and body updated via `gh issue edit` to the full count and to record a **new subclass**
(#4716/#4720): draft-time plan-form body/mirror text never rewritten after implementation was
pushed, which a pure fact-vs-diff check does not catch. A proposed (not-implemented, authorization
-pending) fix is recorded in the GitHub body. Both changes ride PR
`docs/4709-4721-governance-sync` (see PR for exact diff), not a direct `main` commit.

# ローカルミラー・インデックス (2026-07-25 更新 — PR #4711 MERGED (main `4b188515`), #4704 GitHub body + mirror Scope section moved item (a) `.lean` doc-comment fix into Done (explicitly NOT user-authorized, main agent's own scope judgment recorded), #4704 stays OPEN with 2 remaining items; the #4303 dangling-reference cluster (docs + `.lean`) is now fully closed out across PR #4705/#4708/#4710/#4711; #4692/#4559 GitHub-side completion comments posted (bodies already updated, mirror #4692 stale checklist line fixed) — still OPEN pending user close approval; #4642 park/close judgement posted as a GitHub comment (still OPEN pending user decision); #4563 standing-authorization-validity language already present in body, not duplicated)

**2026-07-25 #4715 CLOSED (merged PR #4716, squash main `cfcead29`) + #4717 governance fixes
(dev-pr-clerk)**: build-speed `isDefEq` cluster fix squash-merged — measured reduction
**-22.09s** (implementation back-to-back) / **-22.30s** (`dev-verify` independent
re-measurement), superseding the original A/B planning estimate of **-21.7s**
(`.self-local/issues/4715.md`, `.self-local/reports/perf-isdefeq-cluster-analysis.md:28` both
annotated with the explicit version chain: -21.7s → -22.09s → -22.30s). GitHub #4715
auto-closed via the PR's `Closes` trailer; closing comment posted with the same version chain.
New process issue **#4718** filed for the direct-to-`main` artifact-commit incident that left
`main` red for 2 commits (`b4bec721`/`b67b62fe`, fixed by `7991a01d`; distinct defect class from
#4709). Governance corrections found by `dev-issue-manager`: (1) **#4717 mirror was
missing** (the only open issue with no `.self-local/issues/` mirror) — created (`4717.md`).
(2) **#4717 GitHub body had a stale-path defect** (2 occurrences, missing the
`Concrete/LatticeGraphCorrelation/` path prefix — same class as #4704) — corrected via
`gh issue edit`. Next in-lane item needing no further authorization: **#4717** (dedup
`finiteRegionPseudoMassDistFV_le_of_mem` / `_le_pair`). Mirrors: `4715.md`, `4717.md`, `4718.md`.
Handoff: `.self-local/reports/handoff-2026-07-25-optionB-C1.md`.

**2026-07-25 goal-scope 検問 + ミラー是正 (dev-issue-manager, main `4b14a205`, mirror-only edits)**:
(1) **#4692 は GitHub 上で CLOSED** (`2026-07-25T13:22:38Z`, `gh issue view` 実測) — ミラー
`4692.md` の "Status: OPEN" と本 INDEX ヘッダの「#4692/#4559 still OPEN」記述が stale だった;
`4692.md` を是正済. GitHub の open issue は **#4704 / #4709 / #4642 / #4563 / #4559 の 5 本のみ**.
(2) **#4559** は 3 items すべて disposed (PR #4702+#4705 / #4636 / #4693) = 実体 RESOLVED,
GitHub は OPEN のまま — close はユーザー承認待ちであって作業レーンではない (`4559.md` 是正済).
(3) **goal-scope 判定**: mutating な作業で追加認可なしに着手できるものは **無し**
(#4704 (b)/(c) と `.lean` doc-comment sweep = issue 本文自身が authorization-pending と明記,
#4709 gate = global skill 変更を伴う, #4563 = item-specific gate + standing auth 未確認,
#4642 = off-book 新規定理, OZ/§17.5.1 = off-book). 形式化レーンは現 main でも on-book 枯渇を
再確認 (docs の non-Done 行は連続体 φ⁴ の Out of scope と supersede 済 Partial のみ).
(4) **未記録の負債 2 件 (新規, 本 INDEX が初出)**:
   - **`ring` → `ring_nf` fallback 2 サイト**: full build のたびに
     `info: Try this: [apply] ring_nf` + "The `ring` tactic failed to close the goal" を出す
     (`IsingModel/ContinuousSpin/Phi4AllOdd.lean:41`,
     `IsingModel/TransferMatrix/TwoSiteInteractingLayerOpenBoundaryWindow.lean:223`).
     5040 job の full build で info を出すのはこの 2 モジュールのみ
     (`.self-local/reports/verify-optionB-latticesystembridge.log` 全 16 行が証拠).
     warning ではないのでゲートは通るが, 失敗する `ring1` 探索コストを毎回払っている.
     2026-07-17 以降の verify ログにも同じ 2 行が残存 (長期未記録). 未 issue 化.
   - **docs/index.md の status 散文の内部矛盾**: `docs/index.md:496` / `:1076` が §4.6 Prop 4.6.1 を
     "(convergence) pending" と書く一方, 同 `:401` / `:1332` / `:1338` は同命題を **Done
     (unconditional, PR #3898)** と書く; さらに `:2219` 付近の節見出し "The following GJ Ising
     infinite-volume discussions are **not yet formalized**" の直下で item 1/2/3/6 が
     "DONE"/"(Resolved.)" と書かれている. #4704 は stale `.lean` パス/宣言参照のみを追跡しており,
     この **status 散文の陳腐化は既存 issue のどれにも記録されていない**. 修正は達成主張の表現変更を
     伴うためユーザー判断事項.
(5) **build 高速化レーンの「枯渇」は未実証**: 実測済みモジュールは 48/2011 のみで, その候補選定基準
(`maxHeartbeats` 保持ファイル + 最大行数 top-25) は同じレポートが「実測コストと無相関」と結論した
proxy そのもの (`refactor-axis-buildtime-measured-2db44a2b.md` finding 3). 全数カバレッジは
**clean full build 1 回**の per-job 所要時間出力 (`✔ [n/m] Built X (12s)` 形式; replay 時は出ない)
で得られるため, 8h の逐次 sweep は不要.

**2026-07-25 #4710 merged + #4704 Scope section resynced (dev-pr-clerk)**: PR #4710
(`docs/4704-fix-dangling-transfermatrix-citation`) squash-merged with `--body-file` from the
current PR body (title corrected `drop`→`repoint` before merge per `dev-issue-manager`
UPDATE #7) → main `d97f9612` (fast-forward from `3e085137`, branch deleted). `Part of #4704`
only, no `Closes` keyword — confirmed #4704 stays **OPEN**. #4704 GitHub body + mirror Scope
section updated: `docs/index.md:1715` moved from "Not started" (Scope item 2) to "Done" (Scope
item 1), citing PR #4710. #4704's remaining work is now explicitly **3 items**: (a)
`ClusterExpansionSupersession.lean:18-19` doc-comment stale reference (sole surviving `.lean`
doc-comment reference to the retired `Layer*.lean` modules, invisible to docs/tex scans; scope
extension is a user decision), (b) `docs/index.md:1974` count over-statement (8→6, 12→10;
authorization-pending), (c) unclassified tex-side + remaining docs identifier-token pool
(false-positive-dominant, needs a better scanning method first). Mirror: `4704.md`.

**2026-07-25 #4708 merged + #4704 GitHub-side corrected + #4709 filed (dev-pr-clerk)**: PR #4708
(`docs/4704-fix-stale-lean-paths`) squash-merged with `--body-file` from the verified 4-line body
→ main `472731b3` (branch deleted). `Closes` keyword was never present; confirmed #4704 NOT
auto-closed, remains **OPEN**. #4704 GitHub issue body rewritten to state the final 4-line outcome
(withdrawing the "9-line"/`HLS*` claims) and the settled citation-convention test; the stale
2026-07-25T12:01 comment corrected via a follow-up comment withdrawing only its items 2/3 (items 1
and 4 remain valid, untouched). Filed **#4709** — separate process-level tracking issue for
recurrence-prevention proposal (c) (PR-body/claim verification gate before merge; four PR bodies
this session, #4702/#4703/#4707/#4708, were factually wrong about their own diff). Remaining open
work under #4704: `docs/index.md:1715` stale path (3 files absent), `docs/index.md:1974` count
error, unclassified tex-side pool. Mirror: `4704.md`.

**2026-07-25 #4704 body corrected (dev-pr-clerk, GitHub body + mirror edited, no build, no
close)**: `dev-research` deep pass found the original "9/156" headline counts were raw mechanical
token-scan counts dominated by false positives (common-stem/multi-file doc shorthand, Mathlib/core
API references — 42% of surviving tokens). **Zero classification-B cases** (silently deleted
content, hidden false Done claim) found; no keep-criterion(f) trigger. Confirmed classification-A
(rename/move, declarations survive) count = **4 lines** in `docs/index.md` (lines
1973/1974/1976/1979), addressed by **PR #4708** (merged, main `472731b3`).
Remaining ~1200 docs / 85+3195 tex candidate tokens left unclassified/out-of-scope pending a
lower-false-positive scanning method. Issue remains OPEN (tracking only).
Evidence: `.self-local/reports/research-4704-stale-refs-inventory.md`. Mirror: `4704.md`.

**2026-07-25 #4708 resolution verification (dev-issue-manager, HEAD `33cf2e5e`, main `99ed7f68`)
= RESOLVED / merge-eligible (squash only; `Part of #4704`, #4704 stays OPEN).** The earlier
"9-line" figure is retracted: 3 of those lines (2010/2012/2019, `HLS*`) were never stale, 2
(1980/1982, joint analyticity) were reverted as umbrella-vs-leaf granularity, leaving 4. Citation
rule settled: *a path citation is stale iff the cited module's transitive import closure does not
reach the cited declarations.* Still-open GitHub-side defects (dev-pr-clerk): #4704 body + its
2026-07-25T12:01 comment still describe #4708 as 9-line / 6-line and umbrella→leaf. New
cross-cutting finding: **4 consecutive PR bodies this session (#4702/#4703/#4707/#4708) were
factually wrong about their own diff — no workflow stage verifies the PR body against the diff,
although squash merge writes it into `main`. Needs its own tracking issue.** Mirror: `4704.md`.

**2026-07-25 #4563 / #4642 body corrections (dev-pr-clerk, GitHub body edited, no build, no close)**:
**#4563** — stale 253-module / "243 modules deferred" figures corrected to measured **193 modules /
18-of-46 families completed / 28 remaining**; Next-concrete-step candidate recorded
(`SusceptibilityPointwiseRegularity*`, 8 modules, 1 external dep) with an explicit pre-work
condition (fresh `dev-perf` re-measurement required, prior estimates disagree ~4.5×); the
2026-07-18 "Blanket Authorization Record" is now described honestly as **record-exists /
no-independent-primary-evidence** (all `gh` comments post under the single `phasetr` account) and
**unexercised for 6 days / 100+ commits** — body now requires user reconfirmation before resuming,
does not assume it is still in force. **#4642** — 3 mis-statements corrected: the stated Goal
(`alternatingConnectedSubgraphSum(completeGraph n)` closed form) is **already proven**
(`RecurrenceClosedForm.lean:143`); the "4 modules K0/K2/K3/K4" are actually 2 files
(`CompleteGraphSmallCases.lean` + `CompleteGraphK4.lean`); "0 codebase references" is false for K1
(induction base of the closed form) and K3 (cited by `AlternatingFinThree.lean` + tex) — only
K0/K2/K4 are true reference-0 and even those are docs-gated (keep-criterion (f), `c(K_4)=-6`
docstring/tex). Body now presents 2 disposition options for the user (close not planned, or
authorize keep-criterion-(f) override) without executing either. **Both issues remain OPEN**; no
close performed (close is a user-approval step per repo policy). Mirrors: `4563.md`, `4642.md`.
Handoff: `.self-local/reports/handoff-2026-07-25-optionB-C1.md` (added "next-session confirmation
items" section).

**2026-07-25 (final) #4706 CLOSED (merged PR #4707, squash main `673aabd8`)**: HLS
`positivity` hot-site refactor — 3 of 35 call sites (folded into one shared `private lemma`)
account for 77% of module own-cost; own-cost 3.05s → 2.48s (implementer) / **2.43s** (independent
`dev-verify` re-measurement, median of 3). Remaining 32 sites (0.19s aggregate, ~3% of module)
deliberately left untouched — issue comment records the 33/30 → 35/32 count correction and
returns the unused portion of the user's authorization. Mirror: `4706.md`. Handoff:
`.self-local/reports/handoff-2026-07-25-optionB-C1.md`.

**2026-07-25 #4700 CLOSED (final, merged PR #4705, squash main `a3046ce6`)**: docs/tex retraction
of the §18.4 Mayer order-3 claims left stale by PR #4702; both title deliverables (code deletion +
docs retraction) now complete. Downstream: **#4704 re-anchored 12/159 → 9/156** (the 3-item delta
= the retracted Mayer-order-3 references, excluded to avoid double-count); **#4692/#4559 remain
OPEN** — all technical work is disposed, close is pending the user's explicit approval only
(not closed by dev-pr-clerk). Mirrors: `4700.md`, `4704.md`, `4692.md`, `4559.md`.

**2026-07-25 #4701 CLOSED (merged PR #4703, squash main `5090f6de`)**: LatticeSystemBridge scaffold
removed (5 files, 323L, 12 reference-0 decls), docs retracted in same PR. `#4700 REOPENED`, body
re-anchored to post-merge line numbers (`docs/index.md:2126`, `tex/proof-guide.tex:19368–19383` +
`21076–21098`); `scripts/noshake.json:46` item resolved by #4703. New issue **#4704 OPEN**
(tracking only): repo-wide stale `.lean` references in `docs/index.md` (12) and
`tex/proof-guide.tex` (159), pre-existing debt unrelated to #4703. Mirrors: `4701.md`, `4700.md`,
`4704.md`. Handoff: `.self-local/reports/handoff-2026-07-25-optionB-C1.md`.

**2026-07-22 #4662 refactor (ratio_bound_bundle cluster-1 deletion) / tracking PR #4661 / CLOSED**: Sixth application of #4639 adoption rule. Remove first self-contained closure-component subset of `ratio_bound_bundle` family (≈28 decls across ~11 components total; this PR removed 6 from base-Conditioning layer). Merged at squash commit a1ead114 (2026-07-22, CI green 34m0s). All six claimed removals executed, zero cascade references, audit gates passed. Under standing user authorization (continuing #4648/#4651/#4655/#4657/#4659). Scanner methodology, cascade-zero check, fixture integrity verification per #4639. Source enumeration: `.self-local/reports/remaining-safe-clusters-2026-07-22.md`. Mirror: `4662.md`.

**2026-07-22 #4653 follow-up (audit-gate 自己テストの残り 5 件) / OPEN**: PR #4652 の review が変異 18 種類を実測し 6 件無検出. Med 3 件 (観測点ズレ: 列挙関数と実走査の乖離 / V1・V2 の行ループ truncation / capstone リスト間引き) は PR #4652 で是正済み. 残る Low 5 件 (テスト件数ラチェット無し, `_AXIOM_RE` が同一行 `in` 前置を取りこぼす, 走査対象ゼロで V1/V2 が PASS, CI wiring が部分文字列 assert のみ, pre-push フック未設置) を本 issue で追跡. tooling のみ, Lean/docs/tex 変更なし. Mirror: `4653.md`.

**2026-07-22 #4639/#4649/#4650 dev-issue-manager pass (PR #4648)**: #4639 mirror corrected from
stale OPEN to CLOSED (GitHub state was already CLOSED since 2026-07-21T17:58:18Z; mirror had not
been updated). PR #4648 verified as the first compliant operational use of the #4639 adoption
rule (full scanner output incl. `LIMITS:` banner + `--lean` cross-check pasted for the exact
3-candidate set). #4649 checklist updated to reflect actual gate results; blocked only on CI
(`build` check `in_progress` at time of this pass). New follow-up issue #4650 opened for 5
reference-0 Lee-Yang subdomain/domain declarations (1 cascade from #4648 + 4 pre-existing
siblings found during this audit), in-scope decoration removal under standing authorization.
Mirrors: `4639.md`, `4649.md`, `4650.md`.

**2026-07-21 #4646 refactor (shake import-precision) / user-authorized / OPEN**: Tracking issue for PR #4645 (draft). Build-speed / simplification refactor under standing authorization. `lake exe shake` reports 346 findings; after filtering structural noise (PR #4644), exactly 3 genuine import-precision issues remain in modules with declarations. Three findings: (1) `ComplexAnalyticityCore.lean` imports `Families.SandwichBounds` but only needs `Families.VertexDisjoint`; (2) `WalshBasisOrthogonality.lean` suggests replacing `OneSiteLayerSpectralWindow` with direct imports (needs checking); (3) `ComponentFiber.lean` reaches `AlternatingCompleteGraph.SignedSums` through facade. Policy note: repository keeps facades as re-export window; these three are import-precision issues (not facade dismantling), so in scope. Mirror: `4646.md`.

**2026-07-21 #4639 dead-sweep candidate extraction / corrective procedure / OPEN**: Fix standing operating procedure for "dead sweep" candidate extraction (used by dev-refactoring / lean-refactoring dead-code passes) to require two-part condition: (1) internal dependency closure (declaration is referenced if any other declaration in repo, including same file/namespace, depends on it, not just cross-file importers); (2) docs/tex name citation (declaration counts as referenced if cited in docs/index.md or tex/proof-guide.tex). Only declarations satisfying neither should be proposed for deletion. Identified from Profile.lean audit for #4637 PR-3: 22-declaration candidate list had 10/22 false positives (7 live via internal closure, 3 cited in docs). General operating-procedure correction project-wide, not specific to alternatingConnectedSubgraphSum. Mirror: `4639.md`.

**2026-07-21 #4640 refactor (pseudoMassG dead-declaration removal) / user-authorized / CLOSED**: PR #4641 merged via squash commit 272b310e (2026-07-21). Completed: 12 reference-0 declarations deleted from `IsingModel/PseudoMass/Profile.lean` (audit-narrowed from 22 reported; 7 load-bearing, 3 cited in docs). Final audit: all 10 protected declarations confirmed present (7 load-bearing + 3 docs-cited); CI green; axiom-free; review PASS. Mirror: `4640.md`. Follow-up: #4642 (generalize K_n closed form, retire hardcoded K0/K2/K3/K4 base cases). Mirror: `4642.md`.

**2026-07-21 #4642 follow-up (K_n closed-form generalization) / user decision required / OPEN**: New issue tracking generalization of `alternatingConnectedSubgraphSum(completeGraph n)` to derive closed form `(-1)^(n-1)·(n-1)!`, enabling deletion of four hardcoded base-case modules (K0/K2/K3/K4) currently retained only for TeX documentation citation. Requires explicit user authorization before implementation; treat as future-scope optional optimization. Mirror: `4642.md`.

**2026-07-17 SESSION-END CLEANUP (user-instructed)**: PR #4520 closed as superseded (branch deleted; Rev18-22 evidence preserved under `.self-local/benchmarks/4519/`). Issue #4533 closed not-planned (execution authority never granted across v1-v11; reopen only on explicit item-specific user authorization). **Open issues: 0 / Open PRs: 0.** Session handoff: `.self-local/reports/handoff-session-refactor-2026-07-17.md` (refactor cycles 1-7 complete, main `f3f1e899`).

**2026-07-12 CANONICAL BOOTSTRAP DEPRECATED**: canonical #4259 を CLOSED (single source of truth = docs/index.md)。三層 issue 構造は廃止。ローカルミラーは監査証跡として保持; ミラーは`.self-local/issues/<n>.md` 形式のまま無期保持するが, resume protocol からは削除。

**新規セッション再開手順**: `docs/index.md` の GJ §17-18 進捗表を読む → git log で main hash 確認 → closed issue (#4386/#4413/#4418/#4433/#4405/#4499/#4501/#4503/#4504/#4506/#4519/#4521/#4522/#4524/#4525/#4531 など) で背景・completion/superseding 理由を確認 (measurement/refactor B0/B1 cycle 完了)。再開ステップは `docs/index.md` 本体に記載。

**2026-07-17 #4535 refactor cycle (H1/M2 dead-decoration + import removal) / user-authorized / CLOSED completed — merged PR #4536 (commit 1793e549)**: Tier2 audit findings H1 (94 dead decoration lemmas + 3 optional `_apply` aliases = 97 total) + M2 pinned (1 safe import removal; 1/2 candidates; unsafe WalkSum candidate rejected). Implementation: H1 all 97 removed (Intervals.lean whole-file deletion + 76 removals across 4 other files, pure deletions). M2: 1/2 applied (`CycleGraphLink.lean` `Mathlib.Tactic` removed); `WalkSum.lean` `Mathlib.Tactic.Positivity` REJECTED as false positive (`positivity` genuinely used line 71). Issue-manager corrected title/body (2026-07-17) from "2 unused imports" to "1 unused import". Verification: tier2 audit → dev-verify → dev-review + codex → tier1 audit → issue-manager PASS. Deferred: H2 gate, M1 file splits, mathlib fine-grain swaps.

**2026-07-17 #4538 refactor M1 cycle (file splits + micro-cleanup) / user-authorized / CLOSED completed — merged PR #4539 (squash as commit `4a44ad71`)**: M1 umbrella split completed per PR #4512 precedent: MayerMontroll.lean split into 3 children (ProperColorings, EdgeInclusionExclusion, ColorClassFibre) + umbrella; LayerPerronExistence.lean split into 5 children (QuadraticForm, OrthogonalSpectralData, LayerWrappers, SpinObservableCertificates, MaximalColumnCertificates) + umbrella; declaration multiset preserved verbatim, machine-verified; 61 decls (MayerMontroll) / 66 decls (LayerPerronExistence) by comprehensive count incl. attribute-prefixed declarations. Micro-items: removed `pseudoMass_deriv_formula_corollary` (ref-0, IsingModel/PseudoMass/Basic.lean) and trimmed docs/index.md mention (§17.5 narrative); added scripts/noshake.json (report-only shake config). Verification: zero warnings, GKSTest green, axiom-free (`[propext, Classical.choice, Quot.sound]`), zero downstream importer churn (umbrella preserves paths), `lake exe shake` runnable. No fallback needed; both file splits completed first attempt. Design reference: `.self-local/reports/design-refactor-m1-2026-07-17.md`.

**2026-07-17 #4533 protocol-v11 corrective exact registration and approval complete / execution authority absent / OPEN**: attempt `v11-41a5ea8c54e4524153c9599ffe188d92`; anchor `71f79b0af982c819da0b749556122ddb211d3ebd`; core `c30c7e644122a650e2a819a68aa40982ee16516bbf949c23ee2ed564f372735a`; cache-seed `daa1dfd5565a87efdc01d2bd41f73ff4105151205317ae562c145d0307a5f0c8`; runner `854b3cbc3600ab883c9ac792c84073db1d1fa1d838fccc86fb242d40c2463727`; `cache_seed.py` `a1fe047d9ba19b7766e0fb33c934866fcf7664cc3936527e932c9b3665462515`. 57 tests and runner self-audit PASS. Fresh worktree exact/detached/clean. Donor/seeded proofs PASS for all 9 packages; exact 3 symlinks and seed commitments PASS. Execution authority and runtime surfaces absent. Registration is not execution authority; no approval, authority creation, execution, M0 measurement, ranking, selection, metrics, retry, resume, repair, or cleanup is authorized. Exact registration: https://github.com/phasetr/ising-model/issues/4533#issuecomment-4993733856 (ID `4993733856`, author `phasetr`, exact 219-byte read-back body SHA-256 `2e0e6a35da8c5e7906f2069a09c4ad6dece316f6235684f322791c1bf7711d24`). Exact approval: https://github.com/phasetr/ising-model/issues/4533#issuecomment-4993754940 (ID `4993754940`, author `phasetr`, exact 218-byte read-back body SHA-256 `56b7c06f665f6571f5be07aeaf479cdd453395da3c57f19239eaf056bf20f9be`). Execution authority remains absent; no `execution-authority.json` creation or M0 execution occurred in this checkpoint. `docs/index.md` remains unchanged.

**2026-07-16 #4533 v10 TERMINAL INVALID / v11 Stage-P design authorized / implementation-execution blocked / OPEN**: anchor `71f79b0af982c819da0b749556122ddb211d3ebd`; core `9b1581053cf3e7be4db37da450200788fa0806faa5dfd902d4a4e251ab4b19af`; consumed authority `4826388c463b00407639d90d505be8ba494ae60e8ab963e5a5aedf6019f3a6bd`. Sole runner exit `1`, exact error `RuntimeError: pass boundary drift`. Warm exit0/warning0. Pass1 1985/1985 valid, marker chain `b23db68ece9afd21be56a3b5244b102dc5c6d8cfc707c0d7070625e990dee78e`; pass2 1985/1985 per-row valid, cumulative reconstructed chain `04900a621fd16df19e55cde08b70ac8c4b20785628328074d939205c8b14a97c`, but whole-pass invalid and no complete marker. Total3970 per-row valid/warning0/nonzero0. Only gated boundary drift: power source `AC Power` → `Battery Power`, postflight 91% discharging; all non-power boundaries unchanged. Pass3/final/summary/ranking/checkpoint absent. Integrity and review findings0. Terminal INVALID, not NO_SELECTION; no retry/resume/reuse/repair/cleanup/ranking/metrics. Preserve all v10 evidence. Fresh v11 Stage-P design authorized; implementation/execution blocked pending later gates. Registration: https://github.com/phasetr/ising-model/issues/4533#issuecomment-4989494329 Approval: https://github.com/phasetr/ising-model/issues/4533#issuecomment-4989505092 Terminal checkpoint: https://github.com/phasetr/ising-model/issues/4533#issuecomment-4993195109 Audit report `.self-local/reports/verify-4533-m0-v10-invalid-boundary-2026-07-16.md`, SHA-256 `b384ebcf4618178de96cee5f709b5cd08450abd3781e71caea18cc5e84b01c10`. `docs/index.md` and PR #4520 remain unchanged.

**2026-07-15 #4519 Rev22 STATIC_AUDIT_FAIL / RETIRED; fresh Rev23 required**: root `.self-local/benchmarks/4519/20260715T113000Z-rev22-static` is terminal static-only evidence. The externally anchored suite result is `2 PASS / 1 ERROR`: `self.chain` runs twice, and the second state creation raises `FileExistsError`. Rev22 is immutable: no change/reanchor/retry/resume/repair/correction/reuse. A future attempt requires a separately authorized fresh Rev23. No setup, review, build, calibration, measurement, freeze, publication, metric calculation, or `docs/index.md` change is authorized. Measurement remains pending with no admissible rows/medians/percentage deltas/>=10% verdict; #4519/#4506 remain OPEN.

GitHub Rev22 STATIC_AUDIT_FAIL checkpoints: #4519 https://github.com/phasetr/ising-model/issues/4519#issuecomment-4979750222 / #4506 https://github.com/phasetr/ising-model/issues/4506#issuecomment-4979751432

**Consolidated #4519/#4506 ↔ PR #4520 handoff (2026-07-15)**: Rev18–22 are immutable
static-only retirements. Their terminal reasons are recorded in the canonical #4519 issue and
tracker backlinks above; no Lake/Lean/build, measurement, metrics, or >=10% verdict exists.
PR [#4520](https://github.com/phasetr/ising-model/pull/4520) (`b9c2da93e54d1839baa602a78d676c65a6d41e1e`)
archives Rev18–22 and these mirrors only, excludes Rev23, and remains Draft pending a designated
second maintainer/reviewer. `docs/index.md` and Lean sources are unchanged.

**Superseded 2026-07-15 #4519 rev18 protocol remediation / static-only**: rev17 is **DESIGN_REJECTED** and retired; no change, resume, retry, repair, correction, or reuse. Rev18 starts only as a new revision and is **STATIC-ONLY**. No build, calibration, measurement, freeze, result publication, or metric calculation is authorized. Measurement remains **pending**; no admissible measurements, medians, percentage deltas, or >=10% metrics verdict. #4519/#4506 remain OPEN.

GitHub superseded rev18 checkpoints: #4519 https://github.com/phasetr/ising-model/issues/4519#issuecomment-4976266141 / #4506 https://github.com/phasetr/ising-model/issues/4506#issuecomment-4976266997

**Superseded 2026-07-14 #4519 rev17 SETUP_ACCEPTED / conditional run gate**: package `.self-local/benchmarks/4519/20260714T105139Z`、seal `24a81c3d6023254d679710d11901405be438d1ebaae15670749d93f8f338d334`、execution `.self-local/benchmarks/4519/20260714T105139Z-execution`。setup hashes intent `2cb4a105282d281077e71b3e9e6a7b73bf24898c1ff7cd61cd40cdd94a14dadd`、complete `266d8fd3cc180994203bb7de5593e7878af868716f37aa186e0217fcbb3b5ea4`、manifest `0644e1dcca77dd9ea9a38325a7ce1623f90d556613dce0aa082797417b44988d`、tx `063ffbb71cc0fca13fb4301a3c75207838b7a3b81dc10c5733b13851f8e50dc8`、probes1/2 identical `ff6bda75b086731afe5aed589d689369536d6e01a3f042344f047f823fe947d1` + probe3 `975813ca080f259474feaecb50a4e8cb79517e5166af2372fe3ff7dd70afd2b7`、17 seals。lifecycle1-3 only、stage3 `calibration-post-setup-run-pending` current4569/immutable4277、A=`94ceb4f83906dc23069b7566ce31242240e22855`/B=`6a2470114fe0b5dd5c6cdcbb0e02b8acca351fb4` exact clean H0/artifacts0/registered once/inode-disjoint、main/anchors clean、no later surface/process。**SETUP_ACCEPTED findings0**。conditional `YES_4519_V17_CALIBRATION_RUN_AFTER_SETUP_REVIEW` NOT CONSUMABLE: pmset Battery Power72% discharging。needs exact AC Power、replay/A-B/main/anchors/projection unchanged、lowpowermode0、no warnings、sleep prevention、exact env。then only `Bf/Af/Ar/Br/Bw/Aw` exact `lake --no-ansi --no-cache build IsingModel`; STOP stage4 `calibration-complete`/`calibration-complete-reviewed` both H0 clean。no freeze/results、failure preserve/no retry/cleanup/repair/correction/resume/reuse、#4519/#4506 OPEN、>=10% unmeasured。

GitHub rev17 setup checkpoints: #4519 https://github.com/phasetr/ising-model/issues/4519#issuecomment-4969125171 / #4506 https://github.com/phasetr/ising-model/issues/4506#issuecomment-4969127237 / PR #4518 tracker-only https://github.com/phasetr/ising-model/pull/4518#issuecomment-4969128538

**Superseded 2026-07-14 #4519 rev17 ACCEPT0 / setup-only authority**: root `.self-local/benchmarks/4519/20260714T105139Z`、run `20260714T105139Z`、seal `24a81c3d6023254d679710d11901405be438d1ebaae15670749d93f8f338d334`、**ACCEPT0 findings0**、exact20 inventory/modes、package `0555`/files `0444`、sealed **62 PASS**、projection include10995/exclude112412/retain3 symlinks/residual0、v1-v16+rev15 terminal-execution anchors verified、main/local/origin `94ceb4f83906dc23069b7566ce31242240e22855` clean、execution/A-B/registry absent、no dynamic。exact setup-only token `YES_4519_V17_CALIBRATION_SETUP_AFTER_STATIC_REVIEW`: invoke once after package/anchor/main/execution/A-B/registry prechecks; success creates only execution copy、exact A/B、manifest、sealed three-probe transaction/lifecycle through `calibration-post-setup-run-pending` with `setup_reviewed:false`; then STOP independent setup review。no run token/calibration action/build/freeze/candidate/preflight/normalization/results。failure terminal/no retry/cleanup/repair/correction/resume/reuse。#4519/#4506 OPEN、>=10% unmeasured。

GitHub superseded rev17 ACCEPT0 checkpoints: #4519 https://github.com/phasetr/ising-model/issues/4519#issuecomment-4968556440 / #4506 https://github.com/phasetr/ising-model/issues/4506#issuecomment-4968558113 / PR #4518 tracker-only https://github.com/phasetr/ising-model/pull/4518#issuecomment-4968559618

**Superseded 2026-07-14 #4519 rev16 terminal DESIGN_REJECTED / retired**: root `.self-local/benchmarks/4519/20260714T100648Z`、seal `5af5610f0dcd7e959098d1637ecc234c5354051d3df4ac536d7ef2e6b779beea`、sealed review **60 PASS**、package `0555`/files `0444`、projection include10995/exclude112412/retain3 symlinks、rev15 package+terminal-execution anchors verified、main/local/origin `94ceb4f83906dc23069b7566ce31242240e22855` clean、execution absent、no dynamic。sole blocker: terminal validator accepts count1 iff `callback`, rejecting post-callback `after-capture`/`after-validation`/`target-delta`/`inventory-delta` count1; JSON is durable before validation and can remain unsealed; tests omit all four post points。rev16 setup/run tokens retired。rev17 exact: initial/before capture/validation=`not-invoked`/0、callback=`raised`/1、post four=`returned`/1; centrally derive state/count、prevalidate before write、JSON+detached seal+exact two-file dir+replay、table all9 actual cardinality/exact2files/retry refusal、negative state/count cross-product+all post injections。preserve rev16 projection/symlink/candidate/lifecycle/history/live-boundary requirements。rev17 PENDING/STATIC-ONLY AFTER SYNC、setup unauthorized pending fresh ACCEPT0+separate authorization、no setup/run/freeze/results、#4519/#4506 OPEN、>=10% unmeasured。

GitHub superseded rev16 terminal checkpoints: #4519 https://github.com/phasetr/ising-model/issues/4519#issuecomment-4968312202 / #4506 https://github.com/phasetr/ising-model/issues/4506#issuecomment-4968314020 / PR #4518 tracker-only https://github.com/phasetr/ising-model/pull/4518#issuecomment-4968315312

**Superseded 2026-07-14 #4519 rev15 terminal SETUP_FAILURE_VALID / retired**: package `.self-local/benchmarks/4519/20260714T090138Z`、seal `5715e649113accb66066a17e27e5933224119de9d8be50e6e081977b19149b8a`。execution sibling terminal、stages1/2 sealed/crosslinked、stage3 lifecycle absent、only exact empty `state`/`no-reuse`/`calibration-setup` dirs、A/B/setup complete、manifest present、registry0、main clean/process0、no retry/cleanup/run/freeze。cause: real `.lake/packages` production shape 123407 entries、3 valid contained symlinks、112394 `.lake/build` paths、8281 `.olean`、first `LeanSearchClient/.lake/build`; empty/minimal fixtures gap。rev15 retired/no cleanup/retry/resume/reuse。rev16 policy: include-by-default projection pruning `.lake` path-component descendants only (include10995/exclude112412/retain3 symlinks); hard reject residual `.olean`/`.ilean`/`.o`/`results`/`HANDOFF`; protocol-sealed exclusions; symlink exact link text + relative/contained/nondangling/acyclic/target included; candidate exact projected type/content/mode/link/no extras/inode disjoint + sealed counts/digest; realistic+actual read-only preflight/`LeanSearchClient`/negative tests; initial/before failure terminal seal `callback_count=0`/no unexplained dirs。rev16 PENDING/STATIC-ONLY AFTER SYNC、setup needs fresh ACCEPT0+authorization、no root/setup/run/freeze/results、#4519/#4506 OPEN。

GitHub superseded rev15 retirement checkpoints: #4519 https://github.com/phasetr/ising-model/issues/4519#issuecomment-4967870636 / #4506 https://github.com/phasetr/ising-model/issues/4506#issuecomment-4967875853 / PR #4518 tracker-only https://github.com/phasetr/ising-model/pull/4518#issuecomment-4967879533

**Superseded 2026-07-14 #4519 rev15 ACCEPT0 / setup-only authority**: root `.self-local/benchmarks/4519/20260714T090138Z`、seal `5715e649113accb66066a17e27e5933224119de9d8be50e6e081977b19149b8a`、exact sealed review **54 PASS**。package `0555`/files `0444`、all hashes/v1-v14/main `94ceb4f83906dc23069b7566ce31242240e22855` clean、execution absent、no repository change/no dynamic。ACCEPT0 findings 0: serialized historical replay only、live branch isolated、public freeze/candidate live boundaries + `freeze.py` gates verified。exact next authority ONLY token `YES_4519_V15_CALIBRATION_SETUP_AFTER_STATIC_REVIEW`: execution copy、exact A/B worktrees、lifecycle setup records/probes/transaction/manifest/seals through `calibration-post-setup-run-pending` のみ、その後 independent setup review のため STOP。no run token/build/calibration actions/freeze/results。failure terminal/no cleanup/reuse/retry/repair/correction/resume。quantitative median/percentage/>=10% classification なし、#4519/#4506 OPEN。

GitHub rev15 ACCEPT0 checkpoints: #4519 https://github.com/phasetr/ising-model/issues/4519#issuecomment-4967593208 / #4506 https://github.com/phasetr/ising-model/issues/4506#issuecomment-4967598056 / PR #4518 tracker-only https://github.com/phasetr/ising-model/pull/4518#issuecomment-4967602553

**Superseded 2026-07-14 #4519 rev14 terminal DESIGN_REJECTED**: root `.self-local/benchmarks/4519/20260714T080634Z`、seal `5d69e592eb508d3d2f53696546893f9cf6dcb5adbb47a18026b541b305650674`。exact sealed review **50 PASS**、evidence pristine、main/local/origin `94ceb4f83906dc23069b7566ce31242240e22855` clean、repository change なし、no dynamic。completion/history fixes は sealed static PASS。5 blockers: `require_live=False` が target-delta current path/stat reads、public freeze は current inventory + live destination identity/pristine 欠落、public candidate は live exact-copy/no-inode tree 欠落、`freeze.py` gates は generic disk lifecycle で止まり live public APIs 未 invoke、tests は public boundaries でなく later inventory で catch。rev14 terminal immutable/no marker/repair/correction/resume/reuse、dynamic admissible result/median/percentage/>=10% classification なし。rev15 PENDING/STATIC-ONLY AFTER SYNC: pure serialized delta/zero live reads、freeze `current inventory -> disk -> live identity/pristine`、candidate `current inventory -> disk/live transaction -> live exact tree`、both gates wiring、historical remains valid after live changes vs live rejects、freeze replacement/symlink/content、candidate add/remove/change/link/alias、positive public/gate wiring tests。rev15 root/implementation/branch/PR/dynamic authorization なし、all dynamic unauthorized、#4519/#4506 OPEN。

GitHub rev14 terminal checkpoints: #4519 https://github.com/phasetr/ising-model/issues/4519#issuecomment-4967069883 / #4506 https://github.com/phasetr/ising-model/issues/4506#issuecomment-4967074207 / PR #4518 tracker-only https://github.com/phasetr/ising-model/pull/4518#issuecomment-4967080071

**Superseded 2026-07-14 #4519 rev13 terminal DESIGN_REJECTED**: root `.self-local/benchmarks/4519/20260714T071908Z`、seal `5f3c94cd6cf016b924006b54306c039f1832c6eed2d991b93e565a9ea2d0f67b`。exact sealed review **50 PASS**、evidence pristine、main/local/origin `94ceb4f83906dc23069b7566ce31242240e22855` clean、repository change なし、no dynamic。sealed static design checks は all 36 timed rows + exact CSV を rederive し、execution paths/manifests/transaction replay/candidate copy を修正したが dynamic benchmark measurements ではない。5 blockers: historical results-complete semantics は keys+detached のみで expected schema/revision/run/evidence/count36 欠落かつ final publication が load しない、historical calibration-seal crosslinks 未 rederive、historical freeze/candidate は schema+detached のみで full disk crosslinks なし、consistently resealed wrong completion/seals が pass、historical tamper test が final metadata を propagate しない。rev13 terminal immutable/no marker/repair/correction/resume/reuse、dynamic admissible result/median/percentage/>=10% classification なし。rev14 PENDING/STATIC-ONLY AFTER SYNC: every historical stage に disk-only exact semantic validator、live separate、results completion を count36/CSV digest/journal head/normalization completion/protocol identity に bind/rederive、all calibration/freeze/candidate seal crosslinks recompute、resealed metadata を propagate し every field/candidate divergence/updated journal-CSV-lifecycle hashes 下の changed semantic result を reject する tests。rev14 root/implementation/branch/PR/dynamic authorization なし、all dynamic unauthorized、#4519/#4506 OPEN。

GitHub rev13 terminal checkpoints: #4519 https://github.com/phasetr/ising-model/issues/4519#issuecomment-4966708797 / #4506 https://github.com/phasetr/ising-model/issues/4506#issuecomment-4966714942 / PR #4518 tracker-only https://github.com/phasetr/ising-model/pull/4518#issuecomment-4966717880

**Superseded 2026-07-14 #4519 rev12 terminal DESIGN_REJECTED**: root `.self-local/benchmarks/4519/20260714T061904Z`、final seal `f9e0552334a3e430542b525faf7a5ab67aaecaf0bcec8a782b6cb58ef8aee2ac`。exact sealed review **45 PASS**、seal/hash/anchors PASS、evidence pristine、main/local/origin `94ceb4f83906dc23069b7566ce31242240e22855` clean、repository change なし、no dynamic。7 blockers: pre-record transaction/probes/additions shape-only + historical replay not disk-crosslinked、filesystem transaction が initial/before/after と exact lifecycle delta を関係づけない、permissive component roots で required artifacts/seals 欠落可、frozen candidate が extra results/`.lake`/`.olean`/arbitrary content を許容、freeze record は hash 前 pristine validation 欠落、historical stage semantics not replayed、sealed-protocol A/B paths が immutable package 下で production execution root と不一致かつ tests rewrite で隠蔽。rev12 terminal immutable/no marker/repair/correction/resume/reuse、admissible rows/median/percentage/>=10% classification なし。rev13 PENDING/STATIC-ONLY AFTER SYNC。fixes/tests: correct all mutable paths、exact typed per-stage manifests、empty artifact-free frozen/exact candidate tree、canonical historical transaction+seal+probes+additions+probe relations+stage semantics replay、pristine before inventory/freeze、sealed-protocol reachability without rewrite、consistent reseal/missing-each-required/extra-candidate/transaction-mismatch/swapped-probe/historical-final-publication negatives。rev13 root/implementation/branch/PR/dynamic authorization なし、all dynamic unauthorized、#4519/#4506 OPEN。

GitHub rev12 terminal checkpoints: #4519 https://github.com/phasetr/ising-model/issues/4519#issuecomment-4966357068 / #4506 https://github.com/phasetr/ising-model/issues/4506#issuecomment-4966359690 / PR #4518 tracker-only https://github.com/phasetr/ising-model/pull/4518#issuecomment-4966362174

**Superseded 2026-07-14 #4519 rev11 terminal DESIGN_REJECTED**: root `.self-local/benchmarks/4519/20260714T030926Z`、seal `8cea2dff9df5824fe54e9e97573ca07f13ab3519b342c1a888c3d06136a0c615`。exact sealed review **48 PASS**、seal/hash/anchors PASS、evidence pristine、main/local/origin `94ceb4f83906dc23069b7566ce31242240e22855` clean、repository change なし、no dynamic。10 blockers: inventory current-stage self-dependency、calibration seal/inventory cycle、freeze record/inventory cycle、candidate seal not allowlisted、lifecycle tests no-op semantic validator/placeholders、allowlist vs actual state/no-reuse paths、arbitrary freeze destination not protocol-bound、transaction/probes/seals not replayed、A/B paths incorrectly under immutable package vs execution root、shadowed legacy definitions。rev11 terminal immutable/no marker/repair/correction/resume/reuse、admissible rows/median/percentage/>=10% classification なし。rev12 PENDING/STATIC-ONLY AFTER SYNC。exact transition `predecessor validate -> locked creation -> sealed transaction/probes -> pre-inventory record -> capture inventory excluding explicit post seals -> post-inventory seal -> publish`。追加 fixes: split validators、exact protocol-derived paths、all dynamic worktrees under execution root、bind/replay probes/transaction/destination、unmocked public reachability + ordering/path/destination/evidence/replacement tests。rev12 root/implementation/branch/PR/dynamic authorization なし、all dynamic unauthorized、#4519/#4506 OPEN。

GitHub rev11 terminal checkpoints: #4519 https://github.com/phasetr/ising-model/issues/4519#issuecomment-4965962238 / #4506 https://github.com/phasetr/ising-model/issues/4506#issuecomment-4965964963 / PR #4518 tracker-only https://github.com/phasetr/ising-model/pull/4518#issuecomment-4965968007

**Superseded 2026-07-14 #4519 rev10 terminal DESIGN_REJECTED**: root `.self-local/benchmarks/4519/20260714T021634Z`、seal `0c78bdb7e13bf92f2a5b541aaeef6b5fe7d0c1e7d1ed8dda6a86b6b9aeb0d807`。seal/hash integrity・read-only review・predecessor anchors・pristine root・main/local/origin `94ceb4f83906dc23069b7566ce31242240e22855` PASS、main 後の repository change なし、no dynamic。self-report correction: 40 tests discovered だが sealed artifact は copied `0555` modes のため **37 pass + 3 lifecycle `PermissionError`** を再現し、pre-sealing 40/40 は reviewed baseline ではない。6 blockers: results semantics skip、same-label project/sentinel continuity と archived trace-byte replay 欠落、setup pristine/state + read-only root 到達不能、malformed intermediate lifecycle/CSV を certify 可、generic no-reuse delta により freeze/candidate 到達不能かつ evidence directory が lock 前、sealed suite 非 self-reproducing。rev10 terminal immutable/no marker/repair/correction/resume/reuse。admissible rows・median・percentage・>=10% classification なし。rev11 PENDING/STATIC-ONLY AFTER SYNC: dedicated scenario results semantics、archived sealed trace/sidecar bytes、continuity/reset events、immutable draft と writable execution root 分離、exhaustive phase semantics/canonical CSV、stage-specific deltas + lock-contained evidence/destination identity、sealed artifact から tests PASS が必要。rev11 root/implementation/branch/PR/dynamic authorization なし、all dynamic unauthorized。#4519/#4506 OPEN。

GitHub rev10 terminal checkpoints: #4519 https://github.com/phasetr/ising-model/issues/4519#issuecomment-4964996100 / #4506 https://github.com/phasetr/ising-model/issues/4506#issuecomment-4964998002 / PR #4518 tracker-only https://github.com/phasetr/ising-model/pull/4518#issuecomment-4964999756

**Superseded 2026-07-14 canonical progress checkpoint**: authoritative main `94ceb4f83906dc23069b7566ce31242240e22855` で resolved phase map は R1 PR #4510/#4511、R2 PR #4513 + final docs sync #4518、R3 effective current restoration #4516 after historical #4514、R4 #4508、R5 #4512、R6 #4504 NOT_PLANNED/no PR、R7 #4507。optional deferred R1/R5 は除外。main SHA 後の repository change なし。#4519/#4506 は OPEN で、admissible measurement rows・median・percentage・>=10% classification はすべて無し。history は v1 partial preflight inadmissible、v2 SETUP_FAILED、v3 PREFLIGHT_GATE_FAILED、v4 PREFLIGHT_INVALID、v5-v9 DESIGN_REJECTED。rev9 `.self-local/benchmarks/4519/20260714T005545Z` / seal `50483e23d6fd381d429c6fa1de2d9987874fc58599205bd0a5809b73232ad72a` は static34/34 + read-only review PASS だが 7 blockers/no dynamic/results/measurements。security filter は report-delivery false positive のみで、recovered review は同じ verdict。rev10 PAUSED/PENDING、root/implementation/branch/PR/dynamic authorization なし。

GitHub canonical progress checkpoints: #4519 https://github.com/phasetr/ising-model/issues/4519#issuecomment-4964638790 / #4506 https://github.com/phasetr/ising-model/issues/4506#issuecomment-4964640200 / PR #4518 https://github.com/phasetr/ising-model/pull/4518#issuecomment-4964641571

**2026-07-14 #4519 rev9 terminal DESIGN_REJECTED**: root `.self-local/benchmarks/4519/20260714T005545Z`、seal `50483e23d6fd381d429c6fa1de2d9987874fc58599205bd0a5809b73232ad72a`、static34/34 + read-only review PASS、pristine main/local/origin `94ceb4f83906dc23069b7566ce31242240e22855`。7 blockers: public normalization generic replay、production live checks omitted、action semantics/continuity incomplete、row27 subset-only started validation、pristine+required-state impossible setup gate、immutable inventory blocks CSV26→36/results-complete、before/before no-reuse + no main cleanliness + unbound freeze destination identity。no dynamic/results/measurements/marker/HANDOFF、immutable/no reuse。固定 plan `Bf Af Ar Br Bw Aw`、H0 417/`4a8bf2ce4218e4fc56734335917e4ed3f8d4a454d8e7981f6246762754eb101f`、H1 456/`aa2c86dbde72d14402dd291d5816a1b31f1b8acb390f4571b7591ef23bf711af`、prefix39/`57eed654f00d7fb73a5cbc5b314c058a83ab2e463b439670d3dc6ae8d749b258`、exact14 keys `action, artifact_root, artifacts, captured_utc, count, label, phase, revision, root, run_id, schema, source_state_sha, total_bytes, worktree_sha`、distinct `outputs.o=5c8aafbffc640a98` / `importAllArts=90d6b41762b8a349`。prior v1–v8 roots は amendment exact chain（v1 `b97eb2…472d` → v8 `d791e0…3c73`、v4 INVALID `5457e1…2b36`）。rev10 PENDING/static-only after sync、dynamic unauthorized。fixes: one public typed API、mandatory live publication+sealed replay、full started+typed normalization、one-time pristine then lifecycle additions、event-chain inventories+CSV prefix/append、lock/capture-before/create/capture-after exact delta、actual destination lstat/dev/inode。results 禁止、#4506 OPEN、>=10% 未計測。

Prior-root endpoint anchors: v1 `20260713T124906Z` / `b97eb2b048795550d3b71ca64a32aed9becce8b465b047247fed8c52c420472d`; v8 `20260714T001759Z` / `d791e0537888292a02a48255acc1a28f6fb2df294efbbc2a597ce1df483b3c73`; full v1–v8 chain remains in rev9 `amendment.json` and #4519.

GitHub rev9 design-rejection checkpoints: #4519 https://github.com/phasetr/ising-model/issues/4519#issuecomment-4964520659 / #4506 https://github.com/phasetr/ising-model/issues/4506#issuecomment-4964523345

Superseded rev8 design-rejection checkpoints: #4519 https://github.com/phasetr/ising-model/issues/4519#issuecomment-4964298697 / #4506 https://github.com/phasetr/ising-model/issues/4506#issuecomment-4964302802

Superseded rev7 design-rejection checkpoints: #4519 https://github.com/phasetr/ising-model/issues/4519#issuecomment-4964080702 / #4506 https://github.com/phasetr/ising-model/issues/4506#issuecomment-4964082502

Superseded rev6 design-rejection checkpoints: #4519 https://github.com/phasetr/ising-model/issues/4519#issuecomment-4963385233 / #4506 https://github.com/phasetr/ising-model/issues/4506#issuecomment-4963387595

Superseded rev5 design-rejection checkpoints: #4519 https://github.com/phasetr/ising-model/issues/4519#issuecomment-4963059760 / #4506 https://github.com/phasetr/ising-model/issues/4506#issuecomment-4963062939

Superseded v4 terminal checkpoints: #4519 https://github.com/phasetr/ising-model/issues/4519#issuecomment-4962582825 / #4506 https://github.com/phasetr/ising-model/issues/4506#issuecomment-4962586950

Superseded v4 post-setup checkpoints: #4519 https://github.com/phasetr/ising-model/issues/4519#issuecomment-4961899465 / #4506 https://github.com/phasetr/ising-model/issues/4506#issuecomment-4961904248

Superseded v4 pre-setup checkpoints: #4519 https://github.com/phasetr/ising-model/issues/4519#issuecomment-4961668257 / #4506 https://github.com/phasetr/ising-model/issues/4506#issuecomment-4961670773

### Superseded v3 terminal history

**2026-07-14 #4519 v3 terminal PREFLIGHT_GATE_FAILED**: v1 REJECTED/read-only/no reuse、v2 terminal SETUP_FAILED/read-only/no reuse。v3 `20260713T163251Z` revision 3 / seal `c0ca0bd53c796125ca45b8f5d89d50665194474c67924cadbd47bb6691aeb75f` は preflight exactly once exit 2 で terminal REJECTED/PREFLIGHT_GATE_FAILED。seed B 5679 / A 5467 は成功 warnings 0 だが canonical rows/timed attempts 0。ledger 6 + invocation stop 保存。全 pmset exit 0/source `Now drawing from 'AC Power'`、battery row は charging/present true だが literal `AC attached` なし。windows 3–6 は load/process/thermal PASS で、唯一の偽 failure は power parser。実 AC loss なし。v3 seed/olean/worktree/deps/state/ledger は no retry/correction/cleanup/reuse。fresh v4 revision 4 pending。parser は source line exact `Now drawing from 'AC Power'` anchor、pre-seed probe/tests/new seal/independent review 必須。v4 setup/preflight/results は全禁止。#4506 OPEN、>=10% 未計測、post-#4519 scope 未確定。

GitHub v3-failure checkpoints: [#4519](https://github.com/phasetr/ising-model/issues/4519#issuecomment-4961360847) / [#4506](https://github.com/phasetr/ising-model/issues/4506#issuecomment-4961363661).

### Superseded post-setup checkpoint history

**2026-07-14 #4519 v3 post-setup external checkpoint**: v1 `20260713T124906Z` は REJECTED/read-only/no reuse。v2 `20260713T141900Z` は terminal SETUP_FAILED/read-only/no reuse。v3 `20260713T163251Z` revision 3 sole candidate、seal `c0ca0bd53c796125ca45b8f5d89d50665194474c67924cadbd47bb6691aeb75f`。setup exactly once は exit 0 で消費済み・rerun 禁止、independent post-setup dynamic ACCEPT。state exact 3、probe/inventory/manifest/detached/tool crosslinks 整合。A/B exact SHA・clean・equal path length 94、deps 9 は revisions 同一・non-alias、artifact 0。predecessor anchors: v1 250068 / `c983880318162bf6fcb7afb13a8baedd78e629054b5078b93219cc39f1a3f8ef`、v2 243272 / `f6c8b0fb0dc15fa4acd3d639119f7ff5413e6debd08bc7101bdabda744447863`。CSV header-only、raw empty、process なし、main/predecessors/seal 不変。manager 再検証後の唯一の次 command candidate は foreground preflight 1回。setup/results 禁止、preflight は exit にかかわらず evidence 保存・no retry/cleanup/repair。v3 に in-root HANDOFF なし。#4506 OPEN、>=10% 未計測、post-#4519 scope 未確定。

GitHub post-setup checkpoints: [#4519](https://github.com/phasetr/ising-model/issues/4519#issuecomment-4960745071) / [#4506](https://github.com/phasetr/ising-model/issues/4506#issuecomment-4960749313).

| 層 | issue # | 状態 | 役割 | ミラー |
|---|---|---|---|---|
| **canonical (DEPRECATED)** | **#4259** | **CLOSED (2026-07-12)** | 廃止。resume = docs/index.md + git log (single source of truth) | `4259.md` (監査証跡) |
| 未完了タスク台帳 (SUPERSEDED) | #4405 | CLOSED | 廃止。全項目 done/close 済 | `4405.md` (監査証跡) |
| thread (OZ 3-faces wall, parked) | #4386 | CLOSED (not planned) | parked。Aizenman 1982 / CIV03 検証済み不十分 | `4386.md` (監査証跡) |
| thread (Thm 17.6.1 ∂/∂h, parked) | #4413 | CLOSED (not planned) | parked。同一 OZ wall gated | `4413.md` (監査証跡) |
| thread (OZ/random-current, parked) | #4418 | CLOSED (not planned) | parked。SL-A..D₁/M1 merged infra 現存; SL-D₂ gated | `4418.md` (監査証跡) |
| thread (off-book, group 1b, BANNED) | #4433 | CLOSED | field-CE 拡張禁止 | `4433.md` (監査証跡) |
| refactor R1 (shake imports) | #4499 | **CLOSED completed (2026-07-13)** | pure-removal 72 files/105 imports 完了 (PR #4510/#4511); umbrella→child narrow は decline | `4499.md` |
| refactor R3 (holomorphic equicontinuity core) | #4501 | **CLOSED completed/restored (PR #4516)** | main `01083488`; canonical module実在、CI/verify/review/Shake PASS | `4501.md` |
| refactor R5 (split large files) | #4503 | **CLOSED completed (2026-07-13)** | LayerSpectral 分割完了 (PR #4512); secondary 8 files は optional/見送り | `4503.md` |
| refactor R6 (twin/variant consolidate) | #4504 | **CLOSED not planned (2026-07-13)** | 前提無効 (design re-audit); ℤ^d 層縮小は明示指示待ち | `4504.md` |
| docs sync (PerStageComplex after R2) | #4517 | **CLOSED completed (PR #4518)** | main `94ceb4f8`; missing paths 0; review/verify/CI PASS | `4517.md` |
| build-speed benchmark B0 | #4519 | **CLOSED not planned** (superseded by #4521) | #4519 Rev22 terminal STATIC_AUDIT_FAIL; entire v1–v22 protocol retired. Fresh #4521 executed successful B0 measurement: 0.65% vs 10% target = FAIL. | `4519.md` |
| refactor phase tracker (R1-R7 + B0/B1) | #4506 | **CLOSED completed** | R1-R7 all resolved; B0 measurement FAIL (0.65%); B1 candidate PASS (29.78%); merged PR #4525 + docs PR #4522. | `4506.md` |
| refactor-B0 measurement execution | #4521 | **CLOSED completed** | B0 canonical measurement: 16.83s → 16.72s (0.65% vs 10% target FAIL); valid primary rows; independent verification. | `4521.md` |
| establish measured plan + final B0/B1 audit | #4522 | **CLOSED completed (PR merged 3ebbf56)** | Docs sync; final #4506 completion audit (B0 FAIL; B1 PASS); #4505 stale axiom doc correction. | `4522.md` |
| refactor-B1 candidate (LatticeGraphCorrelation) | #4524 | **CLOSED completed (merged PR #4525)** | Sole authorized B1 candidate; flatten internal umbrella; 11.74s (29.78% vs A, 30.49% vs B); all gates PASS. | `4524.md` |
| PR #4525 B1 merge to main | #4525 | **CLOSED completed (merged bc793dec)** | Squash-merge of refactor-B1; ancestor to final main at #4522 merge. | `4525.md` |
| resolve proof-guide cyclic build blockers | #4531 | **CLOSED completed (merged)** | Unrelated pdfLaTeX U+0085 control-byte fix (pre-existing); merged; current main ancestor. | `4531.md` |
| refactor H1/M2 (dead decoration + import) | #4535 | **CLOSED completed (2026-07-17)** | refactor cycle 2026-07-17 (97 dead decls + 1 import, PR #4536 merged 1793e549) | `4535.md` |
| refactor M1 (file splits) | #4538 | **CLOSED completed (2026-07-17)** | M1 umbrella split cycle completed (PR #4539 merged `4a44ad71`): MayerMontroll→umbrella + 3 children; LayerPerronExistence→umbrella + 5 children; declaration multiset preserved verbatim, machine-verified; 61 decls (MayerMontroll) / 66 decls (LayerPerronExistence) by comprehensive count incl. attribute-prefixed declarations; removed `pseudoMass_deriv_formula_corollary` (ref-0), trimmed docs/index.md mention, added scripts/noshake.json. All gates PASS (zero warnings, GKSTest green, axiom-free, importer churn 0). Design: `.self-local/reports/design-refactor-m1-2026-07-17.md` | `4538.md` |
| refactor cycle 3 (shake-imports + CI audit gate) | #4541 | **CLOSED completed (2026-07-17)** | shake-driven removals/downgrades (9 imports across 6 files) + CI audit_gate.py (V1/V2/V3, 13 capstones) wired into GitHub Actions; 2 false-positive candidates excluded (build arbiter); review QA fail-open holes (string-masking, modifier-prefixed axiom) FIXED in `e4532253` + re-verified; 680 umbrella→child downgrades + 298 coupled blocks DEFERRED (explicit approval required); all gates PASS (zero warnings, GKSTest, review+codex, tier1+issue-manager, CI green); PR #4542 merged `2b6b1c22` | `4541.md` |
| refactor cycle 4 (mathlib-only import downgrades) | #4544 | **CLOSED completed (2026-07-17)** | shake-suggested downgrades (mathlib-only scope): 9/13 designed blocks applied across 9 files; 19 Mathlib imports removed, 14 narrower added; 4 blocks reverted as build-proven false positives (Basic.lean DeriveFintype, Hamiltonian.lean ring, WeightedExpectation.lean ring, SurjectiveLogWeight.lean positivity); all gates PASS (zero warnings, GKSTest, audit_gate V1/V2/V3, umbrella-preservation grep zero); verify report `.self-local/reports/verify-4545-2026-07-17.md` (commit 77cb0103); 668 repo-internal umbrella downgrades + 298 coupled chains DEFERRED pending explicit user umbrella-convention ruling. PR #4545 merged 77cb0103 | `4544.md` |
| refactor cycle 5 (umbrella-to-child import downgrades) | #4547 | **CLOSED completed (2026-07-17)** | Phase A umbrella→child import downgrade completed (PR #4548 merged `ba0be416`): 626 files, 1584 umbrella imports removed / 759 child added (net -825), ~46 build-proven FP reverts, noshake.json seeded (49 umbrella ignoreAll + 4 mathlib-FP ignoreImport), umbrella files 49/49 byte-identical, shake residual 975→448, all gates PASS (zero-warning build, GKSTest, audit_gate V1/V2/V3, umbrella-integrity, CI green). Phase B (298 coupled chains) attempted, non-converging transitive-severance cascade documented (handoff `.self-local/reports/handoff-4547-2026-07-17.md`); retry requires fresh post-merge shake baseline + new tracking issue + design revision. Verification: `.self-local/reports/verify-4548-2026-07-17.md` (dev-verify independent). | `4547.md` |
| refactor cycle 6 (Phase-B-lite simple shake edits) | #4550 | **CLOSED completed (2026-07-17)** | Phase-B-lite simple shake edits merged (PR #4551 merged `816381d8`): 143 shake blocks + 1 root wire applied / 33 reverted (B1: 69/69 TranslationInvariance dead-import removals; B2: 35 pure removals; B3: 39 child-to-child downgrades + 32 FP reverts incl. 27-file umbrella-drop class wholesale revert; B4: MayerMontroll root umbrella wire). File coverage: 146 files, import lines -181/+63 incl. B4 wire (net -118), umbrella integrity PASS (49/49 protected untouched). Shake residual 448→318 (270 coupled chains, 48 non-target). All gates PASS (zero-warning build, GKSTest, audit_gate --full, umbrella integrity, per-file revert rule, CI green). Verification: dev-issue-manager independent re-check. Verdict: cycle-6 authorized scope discharged, no same-authorization follow-up justified. | `4550.md` |
| refactor cycle 7 (wire 66 umbrella-detached modules; 2 D-candidate duplicates) | #4553 | **CLOSED completed (2026-07-17)** | 66/68 W-class modules wired into `IsingModel.lean` (PR #4554 merged `7447d9e1`); 2 build-forced reverted on a genuine duplicate declaration (`IsingModel.mayerExpansionTerm_eq_zero_of_no_polymers` in `ClusterExpansion/MayerCore/Truncations.lean:84` ≡ reachable `ClusterExpansion/StrictPositivity/CycleSeven.lean:47`) — triage's line-39 "verified NOT superseded" claim for this pair was WRONG, corrected in report addendum. Deliverable discharged (66/68 wired, build-verified exclusions documented); P-class (11) + TestGenerators untouched. All gates PASS. **2 D-candidates require user dedup decision** (see next row). Outcome recorded: `.self-local/issues/4553.md`. | `4553.md` |
| umbrella-detached modules triage (Finding 2, corrected 2026-07-17) | — | **TRIAGED (2026-07-17, dev-issue-manager); CORRECTED (2026-07-17, cycle-7 merge-gate verification)**: 80 detached modules (9893 lines) reachable-closure-checked — **W = 66 modules/~8311 lines** (was 68/8312: 2 reclassified, see next row), 11 modules/1454 lines (`PseudoMass.FromParams*`) **P** (parked #2965, no citations, leave detached), 1 module/127 lines (`TestGenerators`) correctly detached-by-design. `lake build` on cycle-7 wiring caught a genuine duplicate declaration the original triage's spot-check grep missed; **D-class is no longer 0**, see next row. Full record + addendum: `.self-local/reports/issue-manager-triage-77modules-2026-07-17.md`. | — |
| D-candidate: MayerCore.{Truncations,MayerTermThreeEval} suspected superseded twin (user decision needed) | — | **OPEN QUESTION (2026-07-17, dev-issue-manager)**: 2 modules, genuine duplicate declaration `mayerExpansionTerm_eq_zero_of_no_polymers` vs reachable `ClusterExpansion/StrictPositivity/CycleSeven.lean:47` (build-caught during #4553 cycle-7 wiring, reverted from import list). Options: (a) delete the `MayerCore` twin, keep `CycleSeven`'s copy, wire the survivor; (b) keep both detached pending a dedup design. No deletion/wiring without explicit user authorization. | — |
| current-main bottleneck profile | #4533 | **CLOSED not planned (2026-07-17, session-end cleanup on user instruction)** | Attempt `v11-41a5ea8c54e4524153c9599ffe188d92`; no M0 execution. [registration](https://github.com/phasetr/ising-model/issues/4533#issuecomment-4993733856) / [approval](https://github.com/phasetr/ising-model/issues/4533#issuecomment-4993754940) | `4533.md` |

## reopen 条件 (close した各 issue 共通)

新しい構成的 β-解析性/質量ギャップ文献の提供 (Aizenman 1982 と CIV03 は検証済み・不十分と判明済み),
または対象を明示した複数月単位の from-scratch 構築の明示認可。一般的な `/goal` 再発行では reopen しない。

## 未完了タスク台帳 (#4405 冒頭セクション) の内訳 — 群ごとの一覧

台帳の実体は #4405 本文冒頭 "📋 UNRESOLVED TASK LEDGER" セクション (逐語ミラー `4405.md` 内)。
群と項目の対応:

- **群1 (2026-07-12 再編成)**: 1a (§17.5.1 lsc via OZ, → #4418, **PERMANENTLY BANNED**),
  **1a′ (§17.5.1 everywhere-continuity via §18 cluster-expansion, → #4386, AUTHORIZED)**,
  1b (§17.6.1 field-CE 拡張, → #4433 closed, **PERMANENTLY BANNED**), 1c (Dobrushin extremal
  monotone-only gate, `LocalObservableExtremalCoincidence.lean:270`, **PERMANENTLY BANNED**)。
- **群2 (scope 境界要判定, on-book, 未認可でも着手可)**: 2a (Thm 17.1.1/Cor 17.1.2),
  2b (Thm 17.2.1), 2c (Thm 17.3.1/17.3.2), 2d (Thm 17.4.1/17.4.2), 2e (Thm 17.7.1 ν/γ)。
  いずれも `docs/index.md` に in/out-of-scope 判定行が現状無い (docs-debt)。
- **群3 (ラベル誤帰属是正, on-book)**: 3a (「§17.1 Dobrushin」誤引用の是正),
  3b (「§18.x = GJ 第18章」誤帰属の disclaimer 未完了 — 前回 "C.6 RESOLVED" 主張を実測で
  再確認したが該当文言は docs/index.md に未検出)。
- **群4 (過大主張是正, ドキュメントのみ)**: 4a (`docs/index.md` Done 行の是正掃引),
  4b (`MEMORY.md` "programme COMPLETE" 記述の撤回 — ユーザー領域につき指示のみ)。

## 2026-07-12 PERMANENT BAN LIST (ユーザー明示指示, #4405/#4259/#4418/#4386 に記録)

以後絶対に触れない対象 (自律 `/goal` 再発行によっても再開しない — 個別・明示的な再認可が必要):
OZ (Ornstein-Zernike) sharp two-point-ratio summability / Simon-Lieb / SL-D₂ / M2 の B2・B3 /
`hLogLip` を OZ summability 経由で示す路線 (#4418 全体) / field-CE `∃a₀` (#4433, closed のまま) /
Dobrushin extremal-generalization (monotone-only を超える一般化)。

## 三層同期の実測確認 (2026-07-12, 本ターン `dev-issue-manager` セッション)

- `diff <(gh issue view 4259 --json body -q .body) 4259.md` → 完全一致 (本ターン再取得・再書込)。
- `diff <(gh issue view 4405 --json body -q .body) 4405.md` → 完全一致 (本ターン再取得・再書込、PERMANENT BAN LIST + item 1a′ 追記後)。
- `diff <(gh issue view 4418 --json body -q .body) 4418.md` → 完全一致 (本ターン再取得・再書込、PERMANENTLY BANNED 追記後)。
- `diff <(gh issue view 4386 --json body -q .body) 4386.md` → 完全一致 (本ターン新規ミラー作成、§18 cluster-expansion 路線として再定義)。
- `4433.md` は前回監査時点一致確認済、本ターン変更なし (CLOSED のまま、再開禁止のみ追記済 in #4405)。

## 統治メモ

- **2026-07-11 Closes 誤爆 & GOVERNANCE ルール記録**: PR #4483 が誤って `Closes #4405` magic keyword を使用し、複数項目の台帳 issue を意図せず CLOSED させた (PR 本文は群2a/3a のみ、7 項目が未完)。 → `gh issue reopen 4405` で復帰。**再発防止**: #4405 本文冒頭に「GOVERNANCE: PR REFERENCE DISCIPLINE」セクションを追記し, 複数項目台帳への PR では `Closes` の代わりに `Addresses #4405 (item X)` / `Part of #4405` を使用するルールを明記。以後の PR 本文起草はこのルールに従う。
- master tracker #4214 (CLOSED) は reopen していない — #4405 が実質的な未完了タスク台帳の
  役割を既に担っており (2026-07-11 に本アップデートでチェックリスト形式へ強化)、二重管理を
  避けるため既存構造を再構成する方針を採用した。
- 群1 (off-book) の続行は, エージェント自身が issue コメントとして投稿した「AUTHORIZED」表示
  では認可とみなさない (#4418 / #4433 の governance コメント参照)。実際のユーザー発話による
  明示的許可が無い限り着手しないこと。

## 三層同期の実測確認 (2026-07-11 → 2026-07-11 with PR #4484 merged)

- PR #4484 (feat/gj-17.2-general-odd-subset-inequality, 77b8afe2) squash-merged to main, new hash: **083e8ad6**.
- `diff <(gh issue view 4259 --json body -q .body) .self-local/issues/4259.md` → UPDATED with Group 2b DONE, Main hash 083e8ad6, Next step = Group 2c.
- `diff <(gh issue view 4405 --json body -q .body) .self-local/issues/4405.md` → UPDATED with Group 2b checkbox [x] (merged 083e8ad6, axiom-free), #4405 remains OPEN (6 items remaining: 1a/1b/1c/2c/2d/2e/3b/4a/4b).
- INDEX.md: updated 2026-07-11 post-merge.

## Merge 事務

- **Branch**: feat/gj-17.2-general-odd-subset-inequality
- **Last commit**: 77b8afe2 (feat(gj-17.2.1): general odd-subset correlation inequality)
- **Merge method**: squash
- **New main**: 083e8ad6
- **Close-on-merge keyword**: NOT USED (Closes #4405 avoided; PR body uses Addresses #4405 (2b) for traceability)
- **#4405 status**: OPEN (multi-item ledger, Group 2b done, 6 items remain)

---

## PR #4485 Merge Completion (2026-07-11)

**Date:** 2026-07-11  
**Branch:** `docs/gj-17.3-17.7-continuum-out-of-scope` (deleted)  
**Commit:** `14c0d849fef6d5755b849bba8fb4e823a79077b3`  
**Merged to main:** `148d0f63`  

### Completed Tasks

- [x] **Group 2c**: Thm 17.3.1/17.3.2 (p.307–308) — coupling constant λ_phys scope determination + `docs/index.md` explicit row
- [x] **Group 2d**: Thm 17.4.1/17.4.2 (p.309) — particle existence scope determination + `docs/index.md` explicit row
- [x] **Group 2e**: Thm 17.7.1 (p.314), ν≥½/γ≥1 half — critical exponent inequalities scope determination + `docs/index.md` explicit row

### Three-Layer Sync Status

- [x] **#4405** (issue tracker): 2c/2d/2e marked `[x]`, updated with "(PR #4485 merged, 148d0f63)", OPEN maintained
- [x] **#4405 mirror** (`.self-local/issues/4405.md`): synchronized
- [x] **#4259** (canonical status issue): Main hash → 148d0f63, Current status updated, Next step → Group 3b (§18.x disclaimer + page citation correction)
- [x] **#4259 mirror** (`.self-local/issues/4259.md`): synchronized

### Files Modified

- `docs/index.md`: 4 insertions, 2 deletions (group 2c/2d/2e documentation)


---

## PR #4486 Merge Completion (2026-07-11)

**Date:** 2026-07-11  
**Branch:** `docs/gj-18-label-disclaimer-and-page-fix` (deleted)  
**Commit:** `dc854c44f8d4a2f3d033ce05643549f9b1bd1d27`  
**Merged to main:** `6b6d5515`  

### Completed Tasks

- [x] **Group 3b**: "GJ §18.x" mislabel disclaimer + page citation audit — explicit disclaimer added to `docs/index.md` before the first "§18.x" row, stating the "§18.x" label is a project-internal analogy tag with correct FV citation (Friedli–Velenik §3.7.3 and §5.4/§5.7) and GJ cross-reference clarification.

### Three-Layer Sync Status

- [x] **#4405** (issue tracker): 3b marked `[x]`, updated with "(PR #4486 merged, 6b6d5515)", OPEN maintained
- [x] **#4405 mirror** (`.self-local/issues/4405.md`): synchronized
- [x] **#4259** (canonical status issue): Main hash → 6b6d5515, Current status updated, Next step → Groups 4a/4b
- [x] **#4259 mirror** (`.self-local/issues/4259.md`): synchronized

### Next Immediate Step

**Groups 4a/4b from #4405**: (4a) audit every "Done" row touched by Groups 1–3 items and correct any wording that overstates completeness (e.g. "Done (gated on hLogLip)" or "Done (lattice analog only)"). (4b) [USER DECISION] retract the "programme COMPLETE" framing in MEMORY.md per the governance findings.

### Files Modified

- `docs/index.md`: 18 insertions, 8 deletions (group 3b disclaimer + page citation corrections)

### INDEX.md Deduplification

- `.self-local/INDEX.md` **DELETED** (2026-07-11). Single source of truth = `.self-local/issues/INDEX.md` (this file).

---

## GROUP 4 COMPLETION AUDIT (2026-07-11, post-orchestrator re-audit)

**Date:** 2026-07-11  
**Context:** #4405 台帳の 群2/3/4 on-book タスク完了確認。

### Completed Tasks

- [x] **Group 4a** (docs/index.md overclaim audit): メインが #4405 UNRESOLVED TASK LEDGER 冒頭の Group 2/3 項目から `docs/index.md` 参照行を cross-checked。**Finding: 過大表現 0 件**。全ての Done 行は正確に修飾 (「gated on hLogLip」「lattice analog only」など既に明記)。追加修正不要で resolved.
- [x] **Group 4b** (MEMORY.md retraction note): ユーザー auto-memory MEMORY.md の冒頭 CURRENT entry の「🎉 programme COMPLETE / fully axiom-free」「本完成」過大表現をメインが検出・撤回済 (retraction prefix 追加、内容 60KB→約5KB 圧縮)。MEMORY.md はユーザー所有領域につき本タスクは「ユーザー/orchestrator による適用」で resolved。

### Three-Layer Sync Status (post-audit)

- [x] **#4259** (canonical status): Current status セクション更新 (on-book 群2/3/4 complete, 残は群1のみ), Next concrete step 本体矛盾是正 (旧「Group 3b from #4405…」→新「on-book complete — STOP-and-ask」).
- [x] **#4259 mirror** (`.self-local/issues/4259.md`): 同期済.
- [x] **#4405** (ledger issue): Group 4a/4b の checkboxes `[ ]` → `[x]`, OPEN 維持 (群1が残る).
- [x] **#4405 mirror** (`.self-local/issues/4405.md`): 同期済, 不要 `.bak` ファイル削除.
- [x] **#4405 cleanup**: `.self-local/issues/4405.md.bak` (ミラー backup) 削除.

### Governance Finding Summary

**on-book タスク群 (2/3/4) 枯渇状態**:
- 全 on-book 形式化 = COMPLETE (Thm 17.5.1 Option A, Thm 17.6.1 β/h directions, docs scope determinations)
- `docs/index.md` Partial/Not-started rows = 0
- 残る群1 (off-book OZ backbone, field-CE optional, Dobrushin monotone gate) は明示ユーザー認可が必須

**Next action = STOP-and-ask**: ユーザーに群1 (a/b/c) 認可の是非を仰ぐ.

---

## PR #4487 P2-i MERGE COMPLETION (2026-07-11, CI green + three-layer sync)

**Date:** 2026-07-11  
**Branch:** `feat/gj-17.5-oz-P2i-truncated4pt-mass` (deleted)  
**Merged to main:** `36705df3`  
**CI Status:** ✅ PASS (run 29154369815, build/GKS/sentinel all ✓, exit 0)  
**Axiom audit:** ✅ All 3 theorems axiom-free `[propext, Classical.choice, Quot.sound]`  
**Verify log:** `.self-local/reports/verify-4487-p2i.log` (build warning ≤ 0)

### Completed Tasks

- [x] **Group 1a P2-i (Step P2 minimum brick)**: PR #4487 merged — **Truncated-4pt mass second switching identity** (symmDiff form, `hxy : x ≠ y`, four-point system `hdisj`, nonnegativity). Critical-path entry of P2 backbone bijection completed. Lower-flavour only (does NOT bound hLogLip; upper-bound remains B3-gated).
- [x] **PR branch deleted**: `feat/gj-17.5-oz-P2i-truncated4pt-mass` cleaned.

### Three-Layer Sync Status (post-merge)

- [x] **#4418** (OZ thread issue): P2-i MERGED section added (main `36705df3`, axiom-free, verify log). P2-ii next (Aizenman Eq.(4.12), FFS §12 extraction, math-before-code required). #4418 remains OPEN.
- [x] **#4418 mirror** (`.self-local/issues/4418.md`): synchronized to GitHub #4418 body (逐語一致確認済).
- [x] **#4259** (canonical status): Main hash → `36705df3`, Current status updated with P2-i MERGED, Next concrete step → P2-ii deferred pending user authorization (math-before-code prerequisite: Aizenman 1982 Eq.(4.12) + FFS §12 extraction).
- [x] **#4259 mirror** (`.self-local/issues/4259.md`): synchronized to GitHub #4259 body.
- [x] **#4405** (ledger issue): Group 1a line 71 updated — "P2-i in progress" → "P2-i MERGED (PR #4487, main `36705df3`, axiom-free, verify log `.self-local/reports/verify-4487-p2i.log`). Next = P2-ii (Aizenman Eq.(4.12) weight bookkeeping, FFS §12 extraction—math-before-code必須); 明示再認可必須." #4405 remains OPEN.
- [x] **#4405 mirror** (`.self-local/issues/4405.md`): synchronized to GitHub #4405 body.

### Merge Governance

- **Merge method**: squash (`gh pr merge 4487 --squash --delete-branch`)
- **Close-on-merge keyword**: NOT USED — PR used `Addresses #4418` (non-closing) to avoid premature #4418 closure (multi-PR thread)
- **#4418 status**: OPEN (P2-ii/B3 deferred, requires explicit user authorization)

### Next Immediate Action

- **If P2-ii authorized in future session**: `lean-math-scribe` FIRST (math-before-code: Aizenman 1982 Eq.(4.12) extraction + FFS §12 PDF initial extraction required before code design/implementation).
- **Pending**: Explicit user re-authorization for P2-ii backbone-length research (current scope: Group 1a ONLY, as per #4259/#4418 governance).

---

## PR #4490 SL-C MERGE COMPLETION (2026-07-12, CI green + three-layer sync + SL-D₂ true core localized)

**Date:** 2026-07-12  
**Branch:** `feat/gj-17.5-oz-lemma51-SLC-avoiding` (deleted)  
**Merged to main:** `049a7841`  
**CI Status:** ✅ PASS (build/GKS/sentinel all ✓, exit 0)  
**Axiom audit:** ✅ Axiom-free (existing infra, wiring-only)  

### Completed Tasks

- [x] **Lemma 5.1 SL-C (avoiding set analysis & bridge-uniqueness)**: PR #4490 merged — **F1–F4 + avoiding Prop** (edge-pivotal decomposition + cluster-conditioning + bridge-uniqueness + avoiding constraint). Axiom-free via existing infra (`edgePivotal_arms`, `reachableCluster_closed`, `weight_edge_partition_factor`). **File** corrected to `IsingModel/Inequalities/ClusterConditioningPivotal.lean` (import cycle avoidance).

- [x] **SL-D STRUCTURAL ANALYSIS (true core localization)**: **CRITICAL FINDING — SL-D₂ is the irreducible research bottleneck**:
  - **SL-D₁ (product-index Fubini)**: Axiom-free, ~1 PR wiring, can land standalone.
  - **SL-D₂ (subgraph-conditioning switching collapse)**: **Genuine irreducible research step** = discharge the subgraph-conditioning switching bridge (Aizenman 1982 Lemma 4.1): `Z_xy(G, ∂={x,y}) = Z_∅(G ↿ {x↔y}, ∂=∅)` where `G ↿ {x↔y}` is the subgraph conditioned on x↔y. **NOT available in mathlib** (htSubgraph / transfer theorems do not apply). **No clean 1-PR entry** in current repo. This is the **proof-irreducible core** for Lemma 5.1.

- [x] **PR branch deleted**: `feat/gj-17.5-oz-lemma51-SLC-avoiding` cleaned.

### Three-Layer Sync Status (post-merge + true core localization)

- [x] **#4418** (OZ thread issue): 
  - SL-C marked ✅ MERGED (PR #4490, main `049a7841`, axiom-free)
  - File path corrected: `IsingModel/Inequalities/ClusterConditioningPivotal.lean`
  - **SL-D section rewritten**: split into SL-D₁ (Fubini, axiom-free) + **SL-D₂ (true irreducible core, Aizenman Lemma 4.1, subgraph-conditioning switching, not in mathlib, requires authorization)**
  - #4418 remains OPEN

- [x] **#4418 mirror** (`.self-local/issues/4418.md`): synchronized to GitHub #4418 body (逐語一致確認済).

- [x] **#4259** (canonical status):
  - Main hash → `049a7841`
  - Current status: "Lemma 5.1 SL-C ✅ MERGED (PR #4490, axiom-free)"
  - Next concrete step: "SL-D — SL-D₁ (Fubini, axiom-free) + **SL-D₂ (subgraph-conditioning switching, Aizenman Lemma 4.1, true irreducible core; no clean entry in repo, requires authorization)**"

- [x] **#4259 mirror** (`.self-local/issues/4259.md`): synchronized to GitHub #4259 body.

- [x] **#4405** (ledger issue): Group 1a "Lemma 5.1 ingredient thread" line updated — "SL-C completed" + "**SL-D₂ true irreducible core (subgraph-conditioning switching, Aizenman Lemma 4.1, absent from mathlib) localized as the authentic research bottleneck; SL-D₁ axiom-free wiring only**". #4405 remains OPEN.

- [x] **#4405 mirror** (`.self-local/issues/4405.md`): synchronized to GitHub #4405 body.

### Merge Governance

- **Merge method**: squash (`gh pr merge 4490 --squash --delete-branch`)
- **Draft→Ready**: `gh pr ready 4490` (draft flag removed before merge)
- **Close-on-merge keyword**: NOT USED — PR used `Addresses #4418` (non-closing) to avoid premature #4418 closure (multi-PR thread)
- **#4418 status**: OPEN (SL-D₁/SL-D₂ deferred, SL-D₂ requires explicit user authorization)

### Capstone Path & Decision Point

**SL-A ✅ → SL-B ✅ → SL-C ✅ → [DECISION POINT]**
- **SL-D₁ (Fubini)**: Axiom-free, can land standalone; no authorization barrier.
- **SL-D₂ (subgraph-conditioning switching)**: **Genuine irreducible research**, Aizenman Lemma 4.1, not in mathlib. Requires explicit user authorization + multi-session design (similar to P2-ii scope). Math-before-code written (`.self-local/tex/rc-oz-lemma51-SLD-collapse.tex`); awaiting user direction.

**SL-E (capstone assembly)** blocked on SL-D₁ ✅ + SL-D₂ resolution.

### Next Immediate Action

- **User decision required**: Proceed with SL-D₁ (standalone axiom-free Fubini), or defer entire Lemma 5.1 capstone pending SL-D₂ authorization?
- **If SL-D₂ authorized**: `lean-math-scribe` FIRST (math-before-code: `.self-local/tex/rc-oz-lemma51-SLD-collapse.tex` → `.self-local/tex/rc-oz-lemma51-SLD-switching.tex` expansion required for subgraph-conditioning switching identity extraction before code design).
- **Pending**: Explicit user decision on SL-D₂ research scope (compare: P2-ii track decision).

---

## PR #4494 SL-D₁b-part-2b MERGE COMPLETION (2026-07-12, CI green + SL-D₁ COMPLETE + SL-D₂ GATE ACTIVE)

**Date:** 2026-07-12  
**Branch:** `feat/gj-17.5-oz-lemma51-D1b-part2b-fubini` (deleted)  
**Merged to main:** `a004b977`  
**CI Status:** ✅ PASS (run 29176737359, build ✓, exit 0, 2026-07-12T02:28:05Z)  
**Axiom audit:** ✅ Axiom-free (`[propext, Classical.choice, Quot.sound]`)  

### Completed Tasks

- [x] **Lemma 5.1 SL-D₁b part 2b (final SL-D₁ ingredient)**: PR #4494 merged (draft→ready, squash-merge, Addresses #4418) — **gluing map Ψ + Equiv Φ : 𝓕_C ≃ 𝒜_int × 𝒜_ext + weight-level `tsum` Fubini `Σ_C = (βJ)·Ξ_int·Ξ_ext`**. Axiom-free via existing infra (`pivotalFiberSet`, `interiorBlockSet`, `exteriorBlockSet`, `glueBlocks`, `pivotalFiberEquiv`, `pivotalNumerator_fiber_factor`, new file `IsingModel/Inequalities/ClusterConditioningFiberFubiniSum.lean`, 823 lines).

- [x] **SL-D₁ COMPLETE**: D1a + D1b parts 1/2a/2b all MERGED, axiom-free. **Range-independence** ingredient chain complete: `SL-A ✅ → SL-B ✅ → SL-C ✅ → SL-D₁a ✅ → SL-D₁b(1/2a/2b) ✅`.

- [x] **SL-D₂ GATE ACTIVATION**: OZ wall (mass-continuity lower-bound residence) now **localized to single irreducible core = SL-D₂** (Aizenman Lemma 4.1, subgraph-conditioning switching: `Z_xy(G, ∂={x,y}) = Z_∅(G ↿ {x↔y}, ∂=∅)`). No clean 1-PR entry found (6-ways-confirmed, 2026-06-30 session). Math-before-code written (`.self-local/tex/rc-oz-lemma51-SLD-exterior.tex`). **Awaits explicit user authorization** (agent self-authorization prohibited).

- [x] **PR branch deleted**: `feat/gj-17.5-oz-lemma51-D1b-part2b-fubini` cleaned.

- [x] **Stale artifact removed**: `.self-local/issues/4418-status.json` (backbone-length P1/P2 era obsolete JSON) deleted.

### Three-Layer Sync Status (post-merge + SL-D₁ completion)

- [x] **#4418** (OZ thread issue): 
  - Status line: "**SL-D₁ COMPLETE** (SL-A through SL-D₁b all MERGED, axiom-free); **SL-D₂ GATE ACTIVE** (awaiting explicit user authorization); SL-E gated on SL-D₂ resolution."
  - SL-D₁b part 2b moved to ✅ Completed section (PR #4494, main `a004b977`, axiom-free)
  - SL-D₂ section rewritten: "GATE ACTIVE: Requires explicit user authorization" + full irreducible-core status + math-before-code written + no clean entry found (6-ways-confirmed)
  - #4418 remains OPEN (SL-D₂ awaiting authorization)

- [x] **#4418 mirror** (`.self-local/issues/4418.md`): synchronized to GitHub #4418 body (逐語一致確認済).

- [x] **#4405** (unresolved task ledger issue):
  - UPDATE (2026-07-12) section rewritten: "SL-D₁ COMPLETE, SL-D₂ authorization gate active"
  - All SL-A..D₁b checkboxes ✅, explicit `SL-D₁ COMPLETE` status + `SL-D₂ GATE ACTIVE` labeling
  - Group 1a dependency/authorization line: SL-D₁b part 2b ✅ MERGED (PR #4494, main `a004b977`, axiom-free) + SL-D₁ COMPLETE statement + SL-D₂ irreducible core status
  - #4405 remains OPEN (SL-D₂ gate active, resolution pending explicit user authorization)

- [x] **#4405 mirror** (`.self-local/issues/4405.md`): synchronized to GitHub #4405 body.

- [x] **#4259** (canonical status issue):
  - Main hash → `a004b977`
  - UPDATE (2026-07-12): "SL-D₁b PART 2b MERGED — SL-D₁ COMPLETE" + full SL-D₂ gate active description
  - Current status section title: "**Lemma 5.1 SL-D₁ COMPLETE; SL-D₂ GATE ACTIVE**"
  - SL-D₁b part 2b line updated: "✅ SL-D₁b PART 2b MERGED (PR #4494, main `a004b977`)"
  - Next concrete step section: "▶ GATE ACTIVE = SL-D₂" with full irreducible-core status + authorization requirement + math-before-code written + no clean entry
  - **Lemma 5.1 INCOMPLETE until SL-D₂ authorization + SL-E capstone**

- [x] **#4259 mirror** (`.self-local/issues/4259.md`): synchronized to GitHub #4259 body.

- [x] **INDEX.md** (this file): PR #4494 merge completion section added (this entry).

### Merge Governance

- **Merge method**: squash (`gh pr merge 4494 --squash --delete-branch`)
- **Draft→Ready**: `gh pr ready 4494` (draft flag removed before merge)
- **Close-on-merge keyword**: NOT USED — PR body uses body-param (non-closing) to avoid premature #4418 closure (multi-PR thread)
- **#4418 status**: OPEN (SL-D₂ gate active, SL-E blocked on SL-D₂ resolution)

### OZ Wall Localization & Critical Finding

**Session arc SL-A→D₁ (6 PR #4488–#4494)** has pinpointed the **single research bottleneck for Thm 17.5.1 lower-continuity**: the OZ wall (mass-continuity lower-bound residence) is now **provably localized to SL-D₂ only** (subgraph-conditioning switching, Aizenman Lemma 4.1). 

- SL-D₁ range-independence infrastructure is **complete and axiom-free**.
- SL-D₂ = **irreducible proof core**, not a convenience split: discharge of conditioned-switching identity is **proof-essential**, not a choice of implementation strategy.
- **No clean 1-PR entry** exists in current repo (mathlib lacks conditioned-mass transfer theorems; mesh-graph conditioning not in Fintype theory).
- SL-D₂ is structurally equivalent to the P2-ii research scope (Aizenman 1982 Eq.(4.12) weight bookkeeping, FFS §12): **multi-session from-scratch research + explicit user authorization required**.

### Next Immediate Action

- **User decision required**: Proceed with SL-D₂ research + SL-E capstone (Lemma 5.1 completion path), or defer/close Lemma 5.1 programme?
- **If SL-D₂ authorized**: `lean-math-scribe` FIRST (math-before-code: `.self-local/tex/rc-oz-lemma51-SLD-exterior.tex` is starter draft; subgraph-conditioning switching identity extraction for GJ p.312 required before code design).
- **Agent constraint**: SL-D₂ self-authorization is prohibited (AI運用原則 scope discipline). Only explicit user directive permits SL-D₂ entry.
- **Pending**: Explicit user authorization for SL-D₂ research + Lemma 5.1 capstone path (compare: Group 1a original authorization 2026-07-11, now SL-D₁ complete, SL-D₂ final gate active).

---

## GOVERNANCE PASS 2026-07-12 (cont.) — CIV03 tested, OZ 3-faces wall PARKED at honest capstone (user directive)

Two user-provided candidate primary sources for closing the OZ wall (Thm 17.5.1 everywhere-continuity / Thm 17.6.1 ∂/∂β full-range / Thm 17.6.1 ∂/∂h ∞-vol) have now both been tested and found insufficient:
- **Aizenman 1982**: BLACK (`.self-local/reports/research-aizenman1982-oz-feasibility.md`, `.self-local/tex/aizenman1982-gapcloser-verdict.tex`).
- **CIV03 (Campanino–Ioffe–Velenik 2003)**: fixed-β sharp OZ asymptotic WHITE, but β-continuity of the mass BLACK, h=0-only (BLACK for ∂/∂h) (`.self-local/reports/research-civ03-oz-feasibility.md`, `.self-local/tex/civ03-gapcloser-verdict.tex`).

**Per explicit user directive ("調査結果を明記の上で区切る"), the OZ wall is PARKED (not closed) in all four mirrors**: #4259 (canonical, Current status + Next concrete step both updated), #4405 (ledger, new section appended), #4386 (thread, new section appended), #4418 (OZ/random-current infra thread, new section appended). All four `gh issue edit --body-file` pushes verified byte-identical (trailing-newline-only diff, cosmetic) against the local mirrors above.

**Stale citation flagged (not corrected by issue-manager)**: `docs/index.md` still has **20 live hits** of "Aizenman ... Lemma 4.1" (nonexistent lemma; correct = §9 Lemma 9.2/9.3 or §3 Lemma 3.2), e.g. lines 1751–1755, 1764. A prior #4405 session entry (line ~543) incorrectly claimed this mis-citation was confined to historical `.self-local/tex/` notes only — that claim is corrected in this pass. Does not affect any Done/mathematical claim (rows correctly labeled "off-book optional"); flagged for `dev-docs-sync`.

**Governance disposition**: the whole-OZ-wall investigation is complete for this session; reopening requires either a new constructive β-analyticity reference or explicit multi-month from-scratch authorization naming the specific extension (not a general `/goal` reissuance).

---

## REFACTORING PHASE — TRACKER #4506 + ISSUES #4499–#4505 (2026-07-13)

**Date:** 2026-07-13  
**Authorization:** User-explicit directive: refactoring phase (gated, test-first, axiom-neutral, book-content sacred).  
**Scope:** Pure structural refactoring only. Two bases:
1. **① build-speed**: Reduce import overhead, parsing cost, incremental rebuild time.
2. **② simplification**: Consolidate duplication, reduce nesting depth, unify naming.

**Phase Strategy**: Sequenced in three phases (foundation → consolidation → unification) to minimize interference.

### Issues Created (Central Tracker + 7 Work Issues)

| # | Title | Basis | Phase | Effort | Priority | Status |
|---|-------|-------|-------|--------|----------|--------|
| **4506** | **[refactor] Refactoring phase tracker — build-speed + simplification** | ①② | All | — | High | OPEN (tracker) |
| 4499 | [refactor] Shake unused imports across hub modules (build-speed) | ① | Phase 1 | M+ | High | OPEN |
| 4502 | [refactor] Remove dead (zero-reference) declarations | ① | Phase 1 | S | Med | OPEN |
| ✓ 4505 | [chore] Fix stale 'vitaliPorter axiom' docs (now a proven theorem) | — | Phase 1 | S | High | **MERGED PR #4507** (2026-07-13 21:17:28Z) |
| 4503 | [refactor] Split oversized files along section boundaries | ① | Phase 2 | M | Med | OPEN |
| ✓ 4500 | [refactor] Consolidate PerStageComplex micro-file tree (OZ Montel/Vitali infra) | ①② | Phase 3 | L | High | **MERGED PR #4513** (2026-07-13 11:38:44Z, commit 8083830e) — 254→35 files consolidated |
| 4501 | [refactor] Unify triplicated Montel/Ascoli/Vitali compactness infra | ② | Phase 3 | L | High | OPEN (R2 complete; now ready to commence) |
| 4504 | [refactor] Consolidate finite/infinite-vol twins & _latticeGraph variant proliferation | ② | Phase 3 | L | Med | OPEN — **DOWNGRADED 2026-07-13** (premise invalid; blocked on user policy, see below) |

### Discipline (Per `lean-refactoring` Skill)

- **Test-first**: All changes require `lake build IsingModel` green + zero warnings.
- **Axiom-neutral**: `#print axioms` output must remain unchanged (same axioms before/after).
- **No sorry/admit/native_decide** introduced.
- **Book content sacred**: GJ §17–18 theorems/proofs untouched (pure structural refactoring only).
- **Incremental**: each PR self-contained (no multi-week accumulation).

### Completion Criteria (Tracker #4506)

- [x] All R1–R7 issues created and linked.
- [x] ✓ **R7 resolved** (PR #4507 merged 2026-07-13 21:17:28Z).
- [x] ✓ **R2 resolved** (PR #4513 merged 2026-07-13 11:38:44Z, 254→35 files consolidated).
- [ ] All Phase 1 issues resolved (~~R7~~, R4, R1).
- [ ] All Phase 2 issues resolved (R5).
- [ ] All Phase 3 issues resolved (~~R2~~, R3, R6).
- [ ] `lake build IsingModel` passes, zero warnings (baseline post-Phase 1).
- [ ] `#print axioms` unchanged from baseline.
- [ ] Incremental build time reduced by ≥10% (measured Phase 1 before/after).
- **Tracker closed once all phases complete.**

### Three-Layer Sync Status (Initial)

- [x] **#4506–#4499** (GitHub issues): created + mirrors in `.self-local/issues/`
- [x] **INDEX.md** (this file): new section added
- [x] **Mirror sync**: 8 `.md` files (4499–4506) created; body content byte-identical to GitHub

---

## PR #4510 BATCH 1 MERGE COMPLETION (2026-07-13)

**Date:** 2026-07-13  
**Branch:** `refactor/r1-shake-imports-batch1` (deleted)  
**Merged to main:** `94b946d3`  
**CI Status:** ✅ PASS (build, 31m11s, exit 0)  
**Axiom audit:** ✅ Axiom-neutral (imports-only, no proof changes)  

### Completed Tasks

- [x] **R1 Batch 1 (DONE)**: 40 files / 64 imports removed. Files touched (sample): GlobalBranchEndpoint, BetaDerivative, BetaDerivativeFieldJ, JDerivative, MagnetizationInfiniteHZeroJZero, etc. (full manifest in gh commit diff).
- [x] **Verification**: All touched files confirmed zero unused-import warnings post-shake analysis.
- [x] **PR branch deleted**: `refactor/r1-shake-imports-batch1` cleaned.

### Three-Layer Sync Status (post-merge)

- [x] **#4499** (R1 work issue): Progress section added — "Batch 1 (DONE): 40 files / 64 imports removed (PR #4510, merged 2026-07-13). Remaining: ~23 files (pure-removal, batch 2) + ~300 files (umbrella→child narrow scope—separate policy decision needed)."
- [x] **#4499 mirror** (`.self-local/issues/4499.md`): synchronized to GitHub #4499 body (Progress section added).
- [x] **#4506** (refactoring phase tracker): R1 status updated — "in progress (batch 1 merged, PR #4510, 2026-07-13)".
- [x] **#4506 mirror** (`.self-local/issues/4506.md`): synchronized to GitHub #4506 body (R1 line updated).

### Merge Governance

- **Merge method**: squash-merge + branch delete (`gh pr merge 4510 --squash --delete-branch`)
- **Close-on-merge keyword**: NOT USED — R1 is multi-batch (batch 2 pending, no Closes)
- **#4499 status**: OPEN (batch 2 pending)
- **#4506 status**: OPEN (Phase 1 ongoing: R1 in progress, R4/R7 pending/done; R2–R6 gated on Phase 1 stability)

### Next Immediate Action

- **Batch 2 (R1 continuation)**: ~23 pure-removal files, ready for next PR (no design/research required).
- **Policy decision pending**: Umbrella→child narrow scope (~300 files) requires explicit design + user approval (separate from R1 batch work). Current status: deferred (not in batch 2 scope).

---


## PR #4511 BATCH 2 MERGE COMPLETION (2026-07-13)

**Date:** 2026-07-13  
**Branch:** `refactor/r1-shake-imports-batch2` (deleted)  
**Merged to main:** `e37ef4bb4ed0514cdfc6d2fb844c47e40d57533e`  
**CI Status:** ✅ PASS (build, 49m6s, exit 0)  
**Axiom audit:** ✅ Axiom-neutral (imports-only, no proof changes)  

### Completed Tasks

- [x] **R1 Batch 2 (DONE)**: 32 files / 41 imports removed. Files touched: LatticeGraphBED, AmbientLattice.Analyticity, SpecialCases.HighTemperatureBounds, Concrete.IntLattice, Inequalities.FKG, AmbientFKG, and 26 others (full manifest in gh commit diff). 1 shake false-positive excluded (real simp-lemma dependency in BetaDerivativeMagnetization.lean).
- [x] **R1 Pure-Removal Scope COMPLETE**: 72 files / 105 imports total (PR #4510 + #4511). All touched files confirmed zero unused-import warnings post-shake analysis. Axiom-neutral; no proof changes.
- [x] **Umbrella→Child Narrow Scope (300 files) DEFERRED**: Requires separate policy decision (remove+add diffs, high cost/risk profile, shake false-positive risk).
- [x] **PR branch deleted**: `refactor/r1-shake-imports-batch2` cleaned.

### Three-Layer Sync Status (post-merge, 2026-07-13)

- [x] **#4499** (R1 work issue): Progress section updated — "Batch 1 (DONE): 40 files / 64 imports / PR #4510. Batch 2 (DONE): 32 files / 41 imports / PR #4511. R1 pure-removal scope COMPLETE (72 files / 105 imports). Umbrella→child narrow scope deferred (policy decision required)."
- [x] **#4499 mirror** (`.self-local/issues/4499.md`): synchronized to GitHub #4499 body (Progress section updated, umbrella narrowing decision deferred).
- [x] **#4506** (refactoring phase tracker): R1 status updated — "✓ COMPLETE (pure-removal batch1+2 merged, PR #4510 + #4511, 2026-07-13). Umbrella→child narrow scope (300 files) TBD (separate policy decision)."
- [x] **#4506 mirror** (`.self-local/issues/4506.md`): synchronized to GitHub #4506 body (R1 line updated, umbrella narrowing policy decision TBD).
- [x] **INDEX.md** (this file): PR #4511 merge completion section added (this entry).

### Merge Governance

- **Merge method**: squash-merge + branch delete (`gh pr merge 4511 --squash --delete-branch`)
- **Close-on-merge keyword**: NOT USED — R1 is complete; no Closes magic keyword used
- **#4499 status**: OPEN (umbrella→child narrow scope policy decision pending; R1 pure-removal complete)
- **#4506 status**: OPEN (R1 ✓ complete; Phase 2 activation pending stability confirmation; Phase 1 remaining: R4/R7 status review)

### Next Immediate Action

- **R4** (#4502 [refactor] Remove dead declarations): Phase 1 continuation (low risk, S effort).
- **R7 status**: Already resolved (PR #4507 merged 2026-07-13 21:17:28Z).
- **Umbrella→child narrow scope** (#4499 Remaining): Policy issue deferred; high cost/risk profile, requires separate user decision (not in batch 1/2 scope).

---


## PR #4512 R5 LAYERSPECTRAL SPLIT MERGE COMPLETION (2026-07-13)

**Date:** 2026-07-13  
**Branch:** `refactor/r5-split-layerspectral` (deleted)  
**Commit:** `ac76c45c` (refactor(layerspectral): split LayerSpectral into umbrella + 7 child modules — Addresses #4503)  
**Merged to main:** `4532067e`  
**CI Status:** ✅ PASS (run 29217252147, build 4m41s, all checks ✓)  

### Completed Tasks

- [x] **R5 Primary Phase (LayerSpectral.lean split)**: PR #4512 merged — 2238-line monolithic file split into 7 child modules (BalancedMatrix, BalancedSpectralGap, Conjugation, FlipParity, HermitianBridge, Positivity, SpectralGap) + umbrella re-export. Declaration count: 116 preserved. Backward-compatible re-exports; zero proof/theorem changes. Build green, warning-zero, axiom-unchanged.
- [x] **PR branch deleted**: `refactor/r5-split-layerspectral` cleaned.

### Three-Layer Sync Status (post-merge)

- [x] **#4503** (R5 issue): Primary task (LayerSpectral) marked ✅ COMPLETE (7 child modules + umbrella, PR #4512, commit 4532067e). Secondary tasks (8 other >900 LOC files) deferred to batch scheduling. #4503 remains OPEN (secondary batch pending user decision).
- [x] **#4503 mirror** (`.self-local/issues/4503.md`): synchronized to GitHub #4503 body (LayerSpectral COMPLETE annotation added, secondary batch note added).
- [x] **#4506** (refactoring phase tracker): R5 status updated — "in progress (LayerSpectral.lean done, PR #4512)".
- [x] **#4506 mirror** (`.self-local/issues/4506.md`): synchronized to GitHub #4506 body (Phase 2 R5 line updated).
- [x] **INDEX.md** (this file): PR #4512 merge completion section added (this entry).

### Merge Governance

- **Merge method**: squash-merge + branch delete (`gh pr merge 4512 --squash --delete-branch`)
- **Close-on-merge keyword**: NOT USED — R5 Primary done; Secondary batch remains; no Closes magic keyword used
- **#4503 status**: OPEN (Primary LayerSpectral ✓ done; Secondary 8 files pending)
- **#4506 status**: OPEN (Phase 2 R5 partially active; Phase 1 R4/R7 status to review)

### Next Immediate Action

- **R4 Phase 1 continuation** (#4502 [refactor] Remove dead declarations): Low risk, S effort.
- **R5 Secondary batch decision**: User choice required for 8 additional >900 LOC candidates (clear section boundaries identified; prioritization TBD).

---

## PR #4513 R2 PERSTAGECOMPLEX CONSOLIDATION MERGE COMPLETION (2026-07-13)

**Date:** 2026-07-13  
**Branch:** `refactor/r2-consolidate-perstagecomplex` (deleted)  
**Commit:** `c4bbc2bb` → squash-merged as `8083830e` (refactor(perstagecomplex): collapse 254 micro-files into 34 (depth 9→2) (#4513))  
**Merged to main:** `8083830e`  
**CI Status:** ✅ PASS (run 29221427923, build 3m38s, all checks ✓, exit 0)  
**Axiom audit:** ✅ Axiom-neutral (file reorganization only, no proof/theorem changes)  

### Completed Tasks

- [x] **R2 PerStageComplex Consolidation (DONE)**: PR #4513 merged — Deep micro-file tree (254 files, depth 9, mean 36 lines/file) collapsed into 35 cohesive modules (depth 2). 220 files deleted; all 101 declarations preserved with identical signatures. Backward-compatible umbrella re-export maintained. Zero proof changes, no theorem statement modifications, axiom count unchanged.
- [x] **Build verification**: Full repo build green (5466 jobs, build completed, all ✓, warning-zero).
- [x] **Downstream integrity**: Verified (external clients of PerStageComplex unaffected by umbrella re-export).
- [x] **Issue #4500 CLOSED** (completed: 254→35 files, PR #4513). Stale doc remnant noted (harmless); VitaliBridge leaf module deferred to R3.
- [x] **PR branch deleted**: `refactor/r2-consolidate-perstagecomplex` cleaned.

### Three-Layer Sync Status (post-merge)

- [x] **#4500** (R2 work issue): CLOSED (resolved: consolidation complete, PR #4513, commit 8083830e). Close comment notes stale docstring and VitaliBridge deferral. **Mirror 4500.md synchronized.**
- [x] **#4500 mirror** (`.self-local/issues/4500.md`): updated with completion status + notes.
- [x] **#4506** (refactoring phase tracker): R2 status updated — "✓ COMPLETE (PR #4513, commit 8083830e, 2026-07-13). 254→35 files consolidated (depth 9→2)". R3 now marked "Ready to commence."
- [x] **#4506 mirror** (`.self-local/issues/4506.md`): synchronized to GitHub #4506 body (R2 line marked ✓ COMPLETE, R3 status updated).
- [x] **INDEX.md** (this file): Refactoring phase table and completion criteria updated (R2 ✓, PR #4513 completion section added this entry).

### Consolidation Details

**File statistics:**
- Input: 254 files, max depth 9, mean 36 lines/file, 123 files <40 lines
- Output: 35 files, depth 2, improved readability + build-speed
- Declarations: All 101 preserved (zero-diff signature set)
- Build impact: 5466 jobs, 3m38s (full green)

**Quality measures:**
- Axiom audit: `#print axioms` = `[propext, Classical.choice, Quot.sound]` (unchanged)
- Proof integrity: No theorem statements modified, no sorry/admit/native_decide introduced
- Backward compat: All public names accessible from parent umbrella re-export

**Deferred items (noted in close comment):**
- Stale docstring ("split into…") from prior group-umbrella organization remains in consolidated file (harmless, no semantic impact)
- VitaliBridge module remains independent leaf (deferred to R3 refactoring assessment)

### Merge Governance

- **Merge method**: squash-merge + branch delete (`gh pr merge 4513 --squash --delete-branch`)
- **Close-on-merge keyword**: NOT USED — R2 is prerequisite for R3; Addresses #4500 used for traceability
- **#4500 status**: CLOSED (completed)
- **#4501 status**: OPEN (R3, now ready to commence, depends on R2 ✓ complete)
- **#4506 status**: OPEN (Phase 3 R2 complete; R3 now active-ready, R6 pending; Phase 1/2 ongoing)

### Next Immediate Action

- **R3 Phase 3 enablement** (#4501 [refactor] Unify Montel/Ascoli/Vitali infra): R2 prerequisite now complete; R3 may commence (highest consolidation gain, Effort L, high technical complexity).
- **Phase 1 stabilization check**: R4/R7 status review (Phase 1 closure gate for Phase 2/3 full throttle).

---

## R6 (#4504) DOWNGRADE — governance action (2026-07-13, dev-issue-manager)

**Design finding** (recorded by dev-issue-manager; full detail
`.self-local/reports/design-r6-downgrade-2026-07-13.md`): R6's consolidation premise is
**invalid**. `IsingModel.Ambient.*` (SimpleGraph/AmbientLattice/Exhaustion) is already the
canonical abstraction; `_latticeGraph` is a mechanical ℤ^d specialization wrapper over it
— nothing left to abstract. finite/infinite-vol twins are distinct types (`Finset`/
`truncated4` vs `Exhaustion`/`truncated4Infinite`), not mechanically derivable from each
other → **NOT mergeable, KEEP** (witness `IsingModel/.../PerStageZetaEta.lean:34,59`).
`_latticeGraph` inventory: 1200 decls, 419 zero-reference, of which 128 capstone-only
(766 docs/tex citations → KEEP) + 65 `*Infinite_latticeGraph` (GJ ℤ^d infinite-vol
capstones → KEEP by default), leaving only **153** isolated zero-reference ingredient
wrappers as the sole (optional, risky) removal candidate.

**Actions taken:**
- [x] **#4504** body rewritten: scope narrowed to optional 153-wrapper cleanup only;
  status = "DOWNGRADED — blocked on user policy decision" (ℤ^d layer shrink policy).
  Left **OPEN** (not closed); noted it should be closed not-planned if the policy answer
  is "do not shrink."
- [x] **#4506** tracker R6 line updated to reflect downgrade + same rationale +
  report pointer, so the tracker no longer misrepresents R6 as pending large-scope work.
- [x] **Mirrors synced**: `.self-local/issues/4504.md`, `.self-local/issues/4506.md`
  (byte-identical to GitHub bodies).
- [x] **KEEP guardrails recorded** in both issues: finite/infinite twins, 128
  capstone-only `_latticeGraph` decls, 65 `*Infinite_latticeGraph` decls are excluded
  from any future merge/removal absent separate explicit authorization.

**Open policy question (user decision, not engineering):** (a) allow the public
ℤ^d-named (`_latticeGraph`) layer to shrink at all, given heavy docs/tex dependency and
GJ stating results in ℤ^d terms? (b) treat the 65 `*Infinite_latticeGraph` wrappers as
dead code or GJ capstones (default here: capstone)?

- **#4504 status**: OPEN (downgraded, blocked on user policy)
- **#4506 status**: OPEN (R3 active-ready; R6 downgraded/blocked; Phase 1/2 ongoing)

---

## R3 (#4501) SCOPE CORRECTION — governance action (2026-07-13, dev-issue-manager)

**Design finding** (`dev-design` R3 sub-agent, returned as message only — harness did not
write a `.self-local/reports/` file for this run; conclusion transcribed verbatim into #4501
by dev-issue-manager, no additional judgment invented): the original #4501 premise
("large-scale duplication across 3 modules, `Concrete/ComplexAnalyticity.lean` ~6085 LOC /
`Concrete/AmbientComplexAnalyticity.lean` ~14180 LOC / `PerStageComplex/`") is an
**overstatement**. The 3 layers form an intentional import-linked abstraction ladder
(`ComplexAnalyticity` ← `AmbientComplexAnalyticity` [imports layer 1, 7 files] ←
`PerStageComplex` [imports Ambient, 6 files; 0 direct refs to `ComplexAnalyticity`]), not
independent siloes. LOC counts are accurate but the duplication *implication* is not.

**Only genuine duplication found**: bounded-holomorphic-family equicontinuity (Montel
pre-step), hand-formalized independently twice — `ComplexAnalyticity/VitaliPorter/
Equicontinuity.lean` (ℕ-indexed, `DifferentiableOn`, ~154 lines) and
`AmbientComplexAnalyticity/AscoliData/Constructors/AnalyticSideConditions.lean` (ι-indexed,
`AnalyticOnNhd`, ~242 lines) — ≈4 lemmas / ≈150 LOC. **This alone = R3 PR-1**, the only
warranted extraction.

**KEEP (no further consolidation)**: `AscoliData/Structures/*` (Lee-Yang branch-data),
`*Patches/*`, `CompactOpen/*`, `Vitali/*` (Ambient); `BranchAscoliCompactOpen/*` /
`RangeAscoliPatches/*` / `SubseqCompactOpen/*` specialization consumers (PerStageComplex);
layer-1 thin `ArzelaAscoli` wrapper. Genuinely different types/hypotheses/abstraction
levels; forcing consolidation = over-merge.

**Verification note**: `git branch -a` / `git log` (2026-07-13) show **no branch or commit**
exists yet for the claimed PR-1 extraction — the prior instruction's "実装中 (in progress)"
wording is corrected in #4501 to "planned/authorized, not yet started."

**Actions taken:**
- [x] **#4501** body rewritten: scope narrowed to PR-1 only (~150 LOC core extraction,
  Effort L→S); "Candidates"/"Acceptance Criteria" (full Montel/Ascoli/Vitali/compactOpen
  unification) marked superseded; KEEP list recorded; status corrected to
  "planned/authorized, not yet implemented" (no overclaim of in-progress work).
- [x] **#4506** tracker R3 line updated with the same corrected scope + status.
- [x] **META FINDING added to #4506**: R6 (2026-07-13 downgrade) and R3 (this correction)
  both show the same failure mode — simplification-audit premises derived from raw LOC/decl
  counts overstated true duplication. Lesson recorded: future refactor audits should judge
  by import-dependency structure + type/hypothesis isomorphism, not LOC volume alone.
- [x] **Mirrors synced**: `.self-local/issues/4501.md`, `.self-local/issues/4506.md`
  (byte-identical to GitHub bodies, verified via diff).

- **#4501 status**: OPEN (PR-1 planned, not started; close on merge)
- **#4506 status**: OPEN (R3 scope corrected; R6 downgraded/blocked; Phase 1/2 ongoing)

---

---

## R3 (#4501) PR-1 COMPLETION (2026-07-13, dev-pr-clerk)

**Date**: 2026-07-13  
**Branch**: refactor/r3-holomorphic-equicontinuity-core  
**Commit (squash-merge)**: 1641659a0db7543addf9fe2807d0c85de61158ad  
**Merged to main**: ✓ (PR #4514 merged)  
**#4501 status**: CLOSED (COMPLETED)

### Summary

R3 PR-1 (extract bounded-holomorphic-family equicontinuity core into canonical module `IsingModel/Analysis/HolomorphicEquicontinuity.lean`) merged successfully.

### Verification

- ✓ CI green (5467 jobs, SUCCESS)
- ✓ Warning-zero (lake build)
- ✓ `#print axioms` unchanged
- ✓ Downstream green
- ✓ Public names preserved (backward-compatible wrappers)

### Three-Layer Sync Status

- [x] **#4501**: CLOSED (COMPLETED), comment with merge details + rationale for no-further-consolidation
- [x] **#4506**: Updated with "✓ R3 COMPLETE (PR #4514, commit 1641659a)" + Phase Completion Summary section + R3 line concise summary
- [x] **#4501 mirror** (`.self-local/issues/4501.md`): new mirror with CLOSED state + completion details
- [x] **#4506 mirror** (`.self-local/issues/4506.md`): synchronized with updated body (Phase Completion Summary added)
- [x] **INDEX.md** (this section): R3 completion record

### Phase Status

**Core refactoring phase (R1–R7) substantially complete:**
- ✓ R1 (#4499) COMPLETE
- ✓ R2 (#4500) COMPLETE
- ✓ R3 (#4501) COMPLETE
- R4 (#4502) optional (not yet started)
- ✓ R5 (#4503) in progress (LayerSpectral done)
- R6 (#4504) DOWNGRADED (policy-gated)
- ✓ R7 (#4505) COMPLETE

**Tracker #4506 remains OPEN** (R6 policy decision and optional work TBD; no closure until all policy/optional items resolved).

**2026-07-15 #4519 rev19 STATIC_AUDIT_FAIL / RETIRED; fresh revision required**: static-audit root `.self-local/benchmarks/4519/20260715T085728Z-rev19-static` is **STATIC_AUDIT_FAIL / RETIRED**. The four blockers are: no external immutable anchor with distinct-key authority binding; no validator for the complete protocol/lifecycle/seal/evidence chain; insufficient adversarial full-chain tamper tests (including consistently resealed substitutions); and incomplete validation of the exact command and required captured evidence. No measurement, setup, review-root creation/review, run, build, calibration, freeze, result publication, or metric calculation is authorized. Rev19 is immutable: no change/retry/resume/repair/correction/reuse; a subsequent attempt requires a new revision, never a Rev19 rewrite. No admissible rows/medians/percentage deltas/>=10% verdict; #4519/#4506 remain OPEN and `docs/index.md` is unchanged.

GitHub rev19 STATIC_AUDIT_FAIL checkpoints: #4519 https://github.com/phasetr/ising-model/issues/4519#issuecomment-4978950056 / #4506 https://github.com/phasetr/ising-model/issues/4506#issuecomment-4978952046

**2026-07-15 #4519 rev20 STATIC_AUDIT_FAIL / RETIRED; fresh static revision required**: root
`.self-local/benchmarks/4519/20260715T092437Z-rev20-static` is retired and grants no setup,
review, run, build, or measurement authority. Manifest SHA-256 is
`0ea5bad2cc6e7ef0898193a27fb3e0d82843d227756da10bdd9130d668b5442a`; external gist commit is
`bf6f63edd39a18bf21d24844a0f0f7dd822bbc6d`; payload SHA-256 is
`9fcff98a79919ff11e1b241c5d3d32128296e638a2622dbac9db4acfddd159ec`. A separately authorized
fresh revision must bind the root anchor into the full chain; bind action A/B, inventory continuity,
and raw actions; re-derive warnings; bind terminal state to inventory without retry; and run an
actual signed-full-chain adversarial test. No docs changes are authorized. #4519/#4506 remain OPEN;
there are no admissible rows, metrics, or >=10% verdict.

GitHub rev20 STATIC_AUDIT_FAIL checkpoints: #4519 https://github.com/phasetr/ising-model/issues/4519#issuecomment-4979475449 / #4506 https://github.com/phasetr/ising-model/issues/4506#issuecomment-4979476838

**2026-07-15 #4519 rev21 STATIC_AUDIT_FAIL / RETIRED; fresh static revision required**:
static-audit root `.self-local/benchmarks/4519/20260715T102437Z-rev21-static` is
**STATIC_AUDIT_FAIL / RETIRED** and grants no measurement, setup, review, run, build,
calibration, freeze, publication, metric, or documentation authority. Its fixed external
root-anchor commit is `58a3a70a4b0efcdcded287fa97f577b731520828`; fixed raw payload SHA-256 is
`4a7fdead9184bdd5dc56e7dd0b160f4f0eca076e7efe94793dda1413029a40f6`. The audit found an
anchor-manifest mismatch (`ad8be7` versus current canonical `72fa`), an immutable-package-unbound
harness, terminal-state symlink acceptance, and **6/6 ERROR** static tests. Rev21 is immutable:
no change/retry/resume/repair/correction/reuse; a separately authorized fresh static revision is
required. #4519/#4506 remain OPEN, no admissible rows/medians/deltas/metrics/>=10% verdict exist,
and `docs/index.md` remains unchanged.

GitHub rev21 STATIC_AUDIT_FAIL checkpoints: #4519 https://github.com/phasetr/ising-model/issues/4519#issuecomment-4979666186 / #4506 https://github.com/phasetr/ising-model/issues/4506#issuecomment-4979667352

**2026-07-15 #4519 Rev22 STATIC_AUDIT_FAIL / RETIRED; fresh Rev23 required**: static-audit root
`.self-local/benchmarks/4519/20260715T113000Z-rev22-static` is **STATIC_AUDIT_FAIL / RETIRED**.
External root-anchor gist commit: `806537ed4023f09b9d64b8536bdc9db6ede5aa5e`; fixed raw payload
SHA-256: `fa73feafa2e6eb55744958c21bd1fe5b41ca7884427e607157fc8faa060de681`. The anchored actual
static suite result is **2 PASS / 1 ERROR** because the fixture executes `self.chain` twice and
the second execution recreates state, raising `FileExistsError`. Rev22 is immutable: no repair,
reanchor, retry, resume, correction, or reuse. A separately authorized fresh Rev23 is required;
Rev22 must not be rewritten. No measurement, setup, review, run, build, calibration, freeze,
publication, metric, or documentation authority exists. #4519/#4506 remain OPEN; no admissible
rows/medians/deltas/metrics/>=10% verdict exist, and `docs/index.md` is unchanged.

GitHub Rev22 STATIC_AUDIT_FAIL checkpoints: #4519 https://github.com/phasetr/ising-model/issues/4519#issuecomment-4979750222 / #4506 https://github.com/phasetr/ising-model/issues/4506#issuecomment-4979751432

---

## SpecialCases Family Consolidation Campaign (#4563, Master Issue)

**Campaign Overview**: Autonomous family-by-family consolidation of 46-family SpecialCases subtree per #4563 blanket authorization (2026-07-18). Quality gates: declaration preservation, attribute conservation, consumer repoint completeness, build green (zero warnings), axiom invariance, audit gates V1–V3, shake clean, facade preservation.

### Progress Summary

**Total families to consolidate**: 46  
**Families consolidated**: 18  
**Remaining**: 28

### Consolidation Log

| Cycle | Family | Modules (n→1) | PR | Commit | Date | Status |
|-------|--------|---------------|----|---------|----|--------|
| 11 | Magnetization* | 10→1 | #4564 | fa163e07 | 2026-07-18 | DONE |
| 12 | SusceptibilityConvergence | 2→1 | #4565 | a758058b | 2026-07-18 | DONE |
| 13 | PolymerFreeEnergyBasic | 2→1 | #4566 | 9441d49fb7 | 2026-07-19 | DONE |
| 14 | MayerFilterConnected | 2→1 | #4567 | 0947a5839c | 2026-07-19 | DONE |
| 15 | MayerRecurrenceHasSum | 2→1 | #4568 | 499fa926cd | 2026-07-18 | DONE |
| 16 | MayerVdIff | 2→1 | #4569 | cf913edf | 2026-07-19 | DONE |
| 17 | PartitionFunctionSymmetry | 2→1 | #4570 | e24b898af9 | 2026-07-19 | DONE |
| 18 | MayerEpsilonPositivity | 3→1 | #4572 | 0eed2fd6 | 2026-07-19 | DONE |
| 19 | MayerAnalyticity | 5→1 | #4573 | 45b770d7 | 2026-07-19 | DONE |
| 20 | FreeEnergyAnalyticity | 6→1 | #4574 | c660ec46 | 2026-07-19 | DONE |
| 21 | MayerBasicIdentities | 5→1 | #4575 | 4a4f4a53 | 2026-07-19 | DONE |
| 22 | MayerEdgeCases | 6→1 | #4576 | 3781a5e3 | 2026-07-19 | DONE |
| 23 | MayerStrictPositivity | 4→1 | #4577 | 2e057471 | 2026-07-19 | DONE |
| 24 | MayerVdBounds | 3→1 | #4578 | a47749e4 | 2026-07-19 | DONE |
| 25 | MayerTrivialCases | 3→1 | #4579 | efbc87de | 2026-07-19 | DONE |
| 26 | MayerTanhFerromagneticIff | 4→1 | #4580 | 0990fb12 | 2026-07-19 | DONE |
| 27 | PartitionFunctionGeneralAnalyticity | 3→1 | #4581 | a4c4bbf4 | 2026-07-19 | DONE |
| 28 | PartitionFunctionRegularity | 4→1 | #4582 | bc7d7ef8 | 2026-07-19 | DONE |

**Wave-1 (zero-red-flag)**: Cycles 11–17, 7 families COMPLETE.  
**Wave-2 (self-contained)**: Cycles 18–28, 11 families COMPLETE (+ 28 pending).  
**Wave-3 (escalation-prone/complex)**: ~9 families deferred pending design review.

### Standing Authorization

Blanket authorization (2026-07-18) for autonomous family-by-family consolidation with auto-merge eligibility upon all 8 quality gates PASS and no escalation conditions triggered. Escalation halts and escalates to issue-manager (do NOT auto-merge):
- Name collision (duplicate decls at merge target)
- Non-trivial attributes (logic beyond simple preservation)
- Cross-family dependencies (implicit inter-family usage)
- Olean/rebuild anomalies (performance degradation, recomputation issues)

### Next Steps

- Continue wave-2 self-contained families (high-confidence, zero-red-flag)
- Prepare wave-3 design review (escalation-prone families)
- Monitor build-speed / olean stability across wave-1/2 merges

---

## 2026-07-25 (dev-pr-clerk) — new issue #4712 + draft PR #4713 opened

`dev-perf` full-coverage (2011/2011 module) clean-build measurement at main `4b14a205`
found 2 new outliers not caught by the two prior 48/2011-coverage "exhausted" campaigns:
`CompleteGraphK4.lean:34` `decide` (VERIFIED -5.3s) and `HLSCorrelationCapstone.lean:185,189`
2x `positivity` (estimated -4..5s). Filed as issue #4712, branch
`refactor/buildtime-fullcoverage-outliers` opened with empty commit `f7b90286` and draft PR
#4713 (`Closes #4712`). Implementation not yet started — mirror `.self-local/issues/4712.md`
created. GitHub open issues now: #4704 / #4709 / #4642 / #4563 / #4559 / **#4712 (new)**.

---

## 2026-07-26 (dev-pr-clerk) — session end: PR #4722 merged (issue #4721 closed); PR #4714 put ON HOLD, restructured under #4704

**PR #4722 merged** (issue #4721, branch `refactor/buildtime-cast-positivity-fv`, squash-merged
to `main` `40315d38`; branch deleted). Gates confirmed independently before merge: CI green
(`build` pass, 3m53s @ the final commit `89b22161`, which added a governance fix restoring a
byte-faithful `.self-local/issues/4721.md` mirror after `dev-issue-manager` found it had been
silently paraphrased), `dev-verify` all 12 items PASS (independent re-measurement −3.34s),
`dev-review` + codex both APPROVE, `dev-audit-tier1` PASS, `dev-issue-manager` RESOLVED. Squash
body supplied explicitly via `--body-file` (not the default merge message) to keep the stale
"has not yet been merged with current main" sentence and a `# Conflicts:` block — both present
in the branch's own merge-commit history — out of `main`'s permanent log. Issue #4721 closed via
the squash body's `Closes #4721`.

**PR #4714 put ON HOLD** (not closed — close is a user-approval item): title prefixed
`[ON HOLD]`, body updated with the hold rationale (4x recurrence of a "disclaim unresolved
citations instead of counting them dangling" defect shape across the issue's original scan and
the PR's three commits; each round injected a new defect class into `tex/proof-guide.tex`;
headline count 157 vs. measured 268 mismatch). Branch/worktree preserved for reference. Work
restructured under issue #4704 into PR-1 (fail-closed citation checker, `scripts/`, no separate
authorization needed) then PR-2+ (batched repointing against the checker's monotonically
decreasing count). Full plan recorded in a comment on #4704 and in `.self-local/issues/4704.md`.

Handoff doc `.self-local/reports/handoff-2026-07-25-optionB-C1.md` was checked against the
"C1 authorized-but-not-started" claim reported stale by `dev-issue-manager`; the file already
correctly documents C1 as completed via PR #4707 in every relevant section (verified by grep for
all `C1`/`HLSSharpPairBound` occurrences) — no edit was needed there.

Session totals (this session, cumulative): **12 PRs merged** (including #4722 above), build-time
reduction **≈ −37s** aggregate across the session's build-speed items. #4714 is ON HOLD. Next
recommended step: PR-1 under #4704 (fail-closed citation checker).

---

## 2026-07-26 (dev-pr-clerk) — PR #4714 CLOSED per user instruction (not merged); R4 findings recorded on #4704

Per explicit user instruction, **PR #4714 was closed without merging** (comment with halt
rationale posted first:
https://github.com/phasetr/ising-model/pull/4714#issuecomment-5080691044). Branch
`docs/4704-tex-dangling-paths` (HEAD `a14f6830`) **preserved** (`--delete-branch` not used).

R4 halt findings (citation-format coverage table + 2 exoneration traps + self-reference/
collapsed-enumeration detector + reusable ephemeral scan assets) recorded as a comment on #4704:
https://github.com/phasetr/ising-model/issues/4704#issuecomment-5080692428, and mirrored in
`4704.md`. **#4704 stays OPEN**; next actionable step remains **PR-1 (fail-closed checker)**.
GitHub open issues: #4704 / #4709 / #4642 / #4563 / #4559 / #4712 (#4714 now closed, not counted).
Synced via short-lived PR **#4727** (`docs/4704-pr4714-close-sync`, `.self-local/` mirrors only).
## 2026-08-01 refactoring plan — #4830 hierarchy

- #4830 is the new canonical refactoring parent. Primary outcomes are coherent abstraction,
  simpler code, and retired technical debt; build speed is supporting evidence only.
- Formal GitHub subissues: #4837 P0 exhaustion family equations, #4831 finite Gibbs kernel, #4832 Ambient Defs/Core dependency
  direction, #4833 import-DAG contract, #4834 Lee--Yang/Ascoli composition, #4835 derivative
  abstractions/providers, and #4836 concept-coherent file/module cleanup.
- Every subissue is audit-gated and may close `not planned` with evidence. No source or dependency
  change is authorized merely by filing this hierarchy.
- #4786/#4788/#4789/#4791/#4792/#4793/#4794/#4795/#4796/#4801 (10 issues) are deleted on GitHub;
  their mirrors are historical. #4822/#4823/#4827/#4828/#4829 (5 issues) are closed `not planned`.
  `docs/plans/4506-refactoring-replan.md` remains an archived baseline.
- **2026-08-01 update**: #4837 (P0) CLOSED — stage A1 (PR #4839, `6147071c`) + stage A2
  (PR #4840, `e3a0dc01`) both merged. #4830 sub-issue progress now 1/7 (GitHub
  `sub_issues_summary` auto-tracked). Remaining open children: #4831/#4832/#4833/#4834/#4835/#4836.
- **2026-08-01 update**: #4831 CLOSED not planned (no coherent kernel boundary found), #4832
  CLOSED completed (PR #4843, merge commit `1830d2bb779126e6dc74701c7cf9ae371d35552f`, repointed
  `Defs/Core.lean` imports at real definer modules). #4830 sub-issue progress now 3/7 per GitHub
  `sub_issues_summary` (graphql-verified: `{"total":7,"completed":3,"percentCompleted":42}`).
  Remaining open children: #4833/#4834/#4835/#4836.
- **2026-08-01 update**: #4834 CLOSED not planned (KEEP verdict on all three Lee-Yang/Ascoli
  candidates, no pilot met the helper-extraction criterion; closing comment
  https://github.com/phasetr/ising-model/issues/4834#issuecomment-5151838852). A separate
  flagged-but-not-acted-upon finding (23 groups / 59 byte-identical theorem statements in
  `AmbientComplexAnalyticity/**/Patches/*.lean`) is recorded in `.self-local/issues/4834.md` for
  a human to decide on a future, separately authorized issue; no new issue opened. #4830
  sub-issue progress now 4/7 per GitHub `sub_issues_summary`
  (`{"total":7,"completed":4,"percent_completed":57}`). Remaining open children:
  #4833/#4835/#4836.
- **2026-08-01 update**: #4835 CLOSED not planned (both audit gates failed: parameter-slice
  regularity wrappers 7.3% feasible with net-zero savings; derivative-abstraction modules all
  load-bearing or cited capstones; closing comment
  https://github.com/phasetr/ising-model/issues/4835#issuecomment-5151917151). #4830 sub-issue
  progress now 5/7 per GitHub `sub_issues_summary`
  (`{"total":7,"completed":5,"percent_completed":71}`). Remaining open children: #4833/#4836.
- **2026-08-02 update**: #4836 CLOSED not planned (all-keep audit, no split/merge pilot cleared
  the concept-coherent consumer bar; closing comment
  https://github.com/phasetr/ising-model/issues/4836#issuecomment-5151990600). #4830 sub-issue
  progress now 6/7 per GitHub `sub_issues_summary`
  (`{"total":7,"completed":6,"percent_completed":85}`). Only remaining open child: #4833
  (PR-1 #4841 merged, PR-2 #4846 CI wiring still open as of 2026-08-02, `evaluate` check
  FAILURE). Progress-summary comment posted on #4830:
  https://github.com/phasetr/ising-model/issues/4830#issuecomment-5151992526. Parent #4830 not
  closed — deferred to holistic review once #4833 resolves.
- **2026-08-02 update**: #4833 CLOSED completed (PR-2 #4846 CI wiring merged, main
  `e9b457de`; closing comment
  https://github.com/phasetr/ising-model/issues/4833#issuecomment-5152045988). #4830
  sub-issue progress now 7/7 per GitHub `sub_issues_summary`
  (`{"total":7,"completed":7,"percent_completed":100}`). Final programme summary comment
  posted on #4830:
  https://github.com/phasetr/ising-model/issues/4830#issuecomment-5152048318. Parent #4830
  NOT closed by clerk — left as a checkpoint for the user/main session to review and close.
