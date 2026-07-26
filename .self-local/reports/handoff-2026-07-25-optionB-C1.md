# Handoff — 2026-07-25 — Option-B deletion campaign + C1 (HLS positivity) — SESSION FINAL STATE

## NINTH (FINAL) UPDATE 2026-07-26 (dev-pr-clerk) — #4724 resolved (measurement reconciled); #4563 ROI verdict = GO (implementation still gated)

This supersedes the EIGHTH (FINAL) UPDATE below as the session's terminal state.

**#4724 (per-module fixed-cost reconciliation): RESOLVED, awaiting close approval.** `dev-perf`
re-measured at main `4f9b7235`
(`.self-local/reports/perf-4724-fixed-cost-reconciliation.md`; comment
https://github.com/phasetr/ising-model/issues/4724#issuecomment-5082030683). Measurement A's
~7.0s/module figure was traced to two additive protocol artifacts, not a real disagreement: (1)
`lake env` wrapper overhead +1.07s/invocation, which a real build never pays, and (2) OS page-cache
state (not `.lake/build` state) being the dominant, highly volatile term — `import` ranged
11.3s→1.75s across cache states on the identical file while `user` CPU stayed fixed at 1.8–2.0s.
Confirmed baseline (warm, serial, bare `lean`, 3×8 replicates): per-module fixed cost `real`
**2.22s** (import 1.68s + init/parse 0.55s), CPU **2.24s**; cross-validated against a 193-module
serial sweep at 430.29s = **2.23s/module**. A direct disposable-worktree A/B on the 7-leaf pilot
family measured **7.0x wall / 9.2x CPU** marginal reduction, confirming Measurement A's "10.5x"
*ratio* was approximately right even though its absolute seconds were inflated ~3.2x. **Issue
stays OPEN** (close is a user-approval item per `dev-pr-workflow`) — status recorded as "resolved,
awaiting close approval".

**#4563 (SpecialCases consolidation, 28 families remaining): ROI verdict = worth doing, but
implementation remains item-specific-authorization-gated.** Comment posted:
https://github.com/phasetr/ising-model/issues/4563#issuecomment-5082030721. At the confirmed
per-module value, the remaining 28 families (~175 modules → 28 files, ~147 modules eliminated)
are worth CPU ≈147×2.24s ≈**~330s** and clean-full-build wall ≈147×0.63s (10-way effective
in-build cost) ≈**~93s** (range 70–150s) ≈**~9%** of the 1022s clean full build — by far the
largest remaining build-time item, an order of magnitude larger than the sum of this session's
entire hot-spot campaign (#4695/#4698/#4699/#4713/#4716/#4722). The conclusion survives
Measurement A's 3.2x over-statement with a large margin, and the standard "incremental rebuild
regresses" objection is empirically negligible (2.22s→2.53s per family). **The real cost is
labour, not build time**: 28 separate multi-file PRs is inefficient use of review effort at
~5.3s wall saved/family; recommend batching **4–7 families per PR** if/when authorized. This
comment is a **precondition resolution + ROI judgement only, not an implementation
authorization** — #4563's own body still requires explicit item-specific user approval before any
consolidation PR is opened (including confirmation of the batching approach).

**Mirrors synced**: `.self-local/issues/4724.md` (status line + full UPDATE section),
`.self-local/issues/4563.md` (new UPDATE section at end), this handoff doc. Bundled into
short-lived PR (see below for number/merge result).

**User-decision items outstanding, updated**: item 7/8 from the EIGHTH UPDATE's list below are
now **partially actioned** — #4724's measurement is done and resolved (only close approval is
outstanding), and #4563's ROI judgement is recorded as GO, but #4563's actual implementation
authorization (including the batching-approach confirmation) is still outstanding. All other
items in the EIGHTH UPDATE's numbered list are unchanged.

## EIGHTH (FINAL) UPDATE 2026-07-26 (dev-pr-clerk) — main = `365fb294` — PR #4728 MERGED; session terminal state

This supersedes the SEVENTH (FINAL) UPDATE below as the session's terminal state.

**PR #4728 squash-merged** (issue #4704 "Part of", branch `refactor/4704-citation-checker`,
head `6227bb66` → merge commit `365fb294`; branch deleted). All merge gates confirmed
independently before merge: CI `build` pass (3m26s @ `6227bb66`), `dev-verify` all 11 items
PASS (zero exemption channels on 6 spelling inputs; the exemption-restoring mutant makes
`NoExemptionChannelTest` fail on 16 cases, independently reproduced), `dev-audit-tier1` PASS
(16 environment spellings confirmed), `dev-review` + codex REQUEST_CHANGES on the first
revision → corrected, `dev-issue-manager` RESOLVED (the one authorization-claim sentence
flagged by UPDATE #15 was corrected by the main agent before this clerk step). The mirror
`.self-local/issues/4704.md` UPDATE #15 addition was committed + pushed on the branch
(`6227bb66`) before merge, keeping the diff at the same 4 files (checker + tests + baseline +
mirror). Squash body supplied via `--body-file` with a `Co-Authored-By: Claude` trailer added
before merge.

**This adds a fail-closed citation auditor for `.lean` path citations in `tex/proof-guide.tex`
and `docs/index.md`.** It has **no exemption channel of any kind** (a per-citation directive
mechanism was built and then deleted again across 3 review rounds, per `dev-principles`'
twice-recurring-defect rule). Its count-of-record: **1,272 gating findings** (529 tex + 743
docs) **+ 95 advisory** self-references. **CI is not wired to it** — wiring the checker into
`.github/workflows/lean_action_ci.yml` or `scripts/audit_gate.py`'s exit code is a separate,
unauthorized configuration change (per the PR body's explicit scope statement).

**#4704 clerical resync (no authorization needed)**: GitHub issue title/body resynced to the
count-of-record, retiring the superseded 157 / 268 / 285 / "12 in docs / 159 in tex" figures.
PR #4728 added to Scope 1 (Done). Item 2(b)'s stated precondition ("a false-positive-reduced
scanning method must be established first") is recorded as **satisfied** by the merged
checker — explicitly noted alongside that **satisfying a precondition is not authorization**;
the actual repointing work ("PR-2") remains unauthorized and awaits a fresh, explicit user
instruction. **#4704 stays OPEN.**

### Session totals (cumulative, this session)

**15 PRs merged** (including #4728 above); aggregate measured build-time reduction across this
session's build-speed items **≈ −37s**.

**Closed this session**: PR #4714 (per explicit user instruction, not merged — see SEVENTH
UPDATE below); issues #4700, #4701, #4706, #4715, #4717, #4721 (all `completed`, via their
respective merged PRs).

**New issues filed this session**: #4704, #4709, #4718, #4724.

### Session lessons (for the next session — do not repeat these)

1. **"Exhausted" was declared and then found wrong 3 separate times this session.** Each time,
   a full-repo, all-approaches re-scan (a clean full build in a separate worktree) found an
   outlier the prior "exhausted" declaration had missed. The measured outliers ended up
   confined to **48 of 2,011 modules** — i.e. candidate selection by proxy (file size, import
   cone, `maxHeartbeats`) was uncorrelated with actual build cost; only a real profiler
   measurement located the real hot spots.
2. **The mechanism behind the false "exonerated" scans is `Meta.isDefEq`'s non-pattern
   higher-order unification failure path.** It is invisible to aggregate profiler summaries;
   the only reliable detection is grepping `trace.profiler` output for
   `[Meta.isDefEq] [>1.0] ❌` lines.
3. **PR bodies had factual errors about their own diff in 12+ instances this session.**
   Implementation was correct every time; the errors clustered entirely in the description
   layer. A history/provenance claim inside a PR body **cannot be verified from that PR's own
   diff** — it must be checked against the cited commits themselves
   (`git show --stat <hash>`, `git merge-base --is-ancestor <hash> <base>`).
4. **The same scan-methodology gap (a missed citation-format variant) recurred 4 times** (most
   visibly in PR #4714, closed for this reason). The remedy applied, per `dev-principles`: an
   approximate scan may be used to **charge** a finding but never to **exonerate** one, and
   once a defect shape recurs twice the exonerating capability itself must be **removed**
   rather than patched again (this is exactly what PR #4728's 3 review rounds did to its own
   directive-exemption mechanism).
5. **Self-authorization phrasing is a recurring trap.** "Authorized by [agent's own] design
   doc" and "recorded as a next step, so it is already in scope" were both used this session
   and are both **not** authorization; only an explicit user instruction is. Every PR body in
   this session was checked for, and where found, corrected to retract, this pattern before
   merge (see #4704's UPDATE #13/#15 for the concrete instances).

### User-approval-pending items after PR #4728 (11, none resolved this update — do not action without explicit user instruction)

1. **PR-2** — the actual `tex/proof-guide.tex` / `docs/index.md` repointing against the
   checker's 1,272-finding count-of-record.
2. **`docs/index.md:1974`** count correction (8→6, 12→10) — a progress-claim walkback.
3. **A systematic `IsingModel/` doc-comment stale-reference sweep.**
4. **Wiring the citation checker into CI** — prerequisite: the checker's own self-test flake
   (observed, root cause unidentified per PR #4728's body) must be root-caused first.
5. **#4559 close approval** (all 3 items already disposed).
6. **#4642 disposition** — close `not planned`, or authorize the keep-criterion-(f) override.
7. **#4563** — standing-authorization currency reconfirmation; also blocked on #4724.
8. **#4724** — authorization to spend its measurement reconciliation (prerequisite of #4563).
9. **#4709** — implementation of the PR-body/diff verification gate (design recorded, not
   built).
10. **#4718** — disposition (fix / park / close) of the incident it records.
11. **§17.5.1 OZ / SL-D₂** (Aizenman 1982 Lemma 4.1) — unchanged long-standing item; requires
    the user's own authorization or source material to proceed.

**Next move: STOP-and-ask.** No item above can be actioned without new user input; per
`CLAUDE.local.md`'s scope (GJ §17–18 new-theorem formalization, Done + axiom-free per GJ's own
proofs) and the goal-scope check recorded in `.self-local/issues/4704.md` UPDATE #15, there is
no on-book item and no already-authorized off-book item left to pick up autonomously.


## SEVENTH (FINAL) UPDATE 2026-07-26 (dev-pr-clerk) — PR #4714 CLOSED per user instruction (not merged); next = PR-1 under #4704

This supersedes the SIXTH (FINAL) UPDATE below as the session's terminal state.

Per explicit user instruction, **PR #4714 is now CLOSED** (not merged). A comment with the halt
rationale was posted before closing:
https://github.com/phasetr/ising-model/pull/4714#issuecomment-5080691044. **Branch
`docs/4704-tex-dangling-paths` (HEAD `a14f6830`) is preserved for reference** (`--delete-branch`
was not used).

R4's halt findings — citation-format coverage table (inline `\texttt`, `\path`, Verbatim blocks/
ASCII trees, brace-shorthand `Dir/\{A,B\}.lean`, bare-prose form, `\_` escaping, Verbatim
line-wraps), 2 confirmed exoneration traps (unconditional archive-tag resolution; permissive
component-aligned suffix matching), a self-reference/collapsed-enumeration detection rule
(exactly reproduced tier1's 15-paragraph finding), and reusable ephemeral scan assets
(`r4scan.py`/`r4audit.py`/`r4dup.py`/`r4count.py`) — were recorded as a comment on #4704:
https://github.com/phasetr/ising-model/issues/4704#issuecomment-5080692428, and mirrored into
`.self-local/issues/4704.md`.

**#4704 stays OPEN.** Next actionable step: **PR-1 under #4704** — a fail-closed citation checker
under `scripts/` (full path-suffix resolution, correct Verbatim/brace expansion, zero
disclaim-exemptions, fixtures + mutation tests for the known miss-classes, self-referential-prose
detection). No separate authorization needed for PR-1 itself.

Synced this update via short-lived PR #4727 (`docs/4704-pr4714-close-sync`), containing only
`.self-local/` mirror changes, merged with CI green.

## SIXTH (FINAL) UPDATE 2026-07-26 (dev-pr-clerk) — main = `40315d38` — PR #4722 MERGED (#4721 closed); PR #4714 ON HOLD

This supersedes the FIFTH (FINAL) UPDATE below as the session's terminal state.

**PR #4722 squash-merged** (issue #4721, branch `refactor/buildtime-cast-positivity-fv`, head
`89b22161` → merge commit `40315d38`, new `main` tip; branch deleted). All merge gates confirmed
independently before merge: CI green (`build` pass, 3m53s @ `89b22161`), `dev-verify` all 12
items PASS (independent re-measurement −3.34s, vs. the implementation's own −3.163s and the
issue's original $TMPDIR-copy −3.75s — all three consistent, chain recorded in the squash
message), `dev-review` + codex both APPROVE, `dev-audit-tier1` PASS, `dev-issue-manager`
RESOLVED. Squash body supplied explicitly via `--body-file` (not the default auto-generated
message) specifically to keep two defects present in the branch's own history — the stale "this
branch has not yet been merged with current main" sentence and a `# Conflicts:` block, both
artifacts of an earlier `origin/main`-into-branch merge — out of `main`'s permanent log (the
exact `dev-audit-tier1` concern this session). Issue #4721 closed via the squash body's
`Closes #4721`. The final branch commit (`89b22161`, pushed by `dev-pr-clerk`) also fixed a
governance defect: `dev-issue-manager` found `.self-local/issues/4721.md` had been silently
paraphrased (headings reworded, a checkbox list flattened to prose, one sentence dropped) while
claiming to be a verbatim mirror; restored byte-faithful before merge.

**PR #4714 put ON HOLD** (title prefixed `[ON HOLD]`, body updated with hold rationale; **not
closed** — close remains a user-approval item; branch/worktree preserved for reference, not
touched further). `dev-issue-manager` verdict: the same defect shape — a scan declaring
"complete" by disclaiming unresolved citations instead of counting them as dangling — recurred
**4 times** (issue #4704's original "157" scan, then #4714's R1/R2/R3 commits), each round also
injected a *new* defect class into the public `tex/proof-guide.tex` artifact, and the headline
"157" figure does not match the fuller measured "268". Work restructured under #4704 into
**PR-1** (fail-closed citation checker under `scripts/` — full path-suffix resolution, correct
Verbatim/brace expansion, zero disclaim-exemptions, fixtures + mutation tests for the 3 known
miss-classes, self-referential-prose detection; no separate authorization needed) then **PR-2
onward** (batched repointing, accepted against the checker's monotonically decreasing count).
Wiring the checker into CI/`audit_gate.py` as a blocking gate remains a separate user-approval
item. Full plan recorded on PR #4714's body and in a comment + mirror update on issue #4704.

**Handoff correction check**: the "C1 (HLSSharpPairBound positivity) authorized, not yet
started" claim that `dev-issue-manager` flagged as stale (C1 actually shipped as PR #4707, see
`.self-local/reports/perf-C1-hls-positivity-profile.md`) was checked against this file directly —
every section already correctly states C1 as merged via #4707 (verified by grepping every
`C1`/`HLSSharpPairBound` occurrence in this file); no edit was needed here. The stale claim
lived only in the cross-session memory summary, not in this handoff doc.

**Session totals (cumulative across the session)**: **12 PRs merged** (including #4722 above),
aggregate build-time reduction **≈ −37s** across this session's build-speed items. #4714 is
ON HOLD (not closed). Next recommended step: PR-1 under #4704 (fail-closed citation checker).

## FIFTH (FINAL) UPDATE 2026-07-25 (dev-pr-clerk) — main = `cfcead29` — PR #4716 MERGED, #4715 CLOSED

This supersedes the FOURTH (FINAL) UPDATE below as the session's terminal state.

**PR #4716 squash-merged** (issue #4715, branch `refactor/buildtime-isdefeq-cluster`, head
`6ed1ad5c` → merge commit `cfcead29`, new `main` tip; branch deleted). All merge gates confirmed
independently before merge: CI green (`build` pass, 3m32s @ `6ed1ad5c`), `dev-verify` PASS all 9
items, `dev-review` + codex both APPROVE, `dev-audit-tier1` PASS (the "all 37 theorems" wording
issue flagged by tier1 was already corrected to "37 of the 39 …" in the PR body before this
merge), `dev-issue-manager` RESOLVED, remote-tip = gated commit confirmed via `git ls-remote` +
non-empty `git diff origin/main..origin/<branch>` before merge and non-empty
`git diff <base>..origin/main` after. Issue #4715 auto-closed via the PR's `Closes #4715`
trailer.

**Measured reduction — version chain (now reconciled everywhere)**: **-21.7s** (initial A/B
planning estimate, `dev-perf`) → **-22.09s** (implementation back-to-back before/after
measurement on the PR branch) → **-22.30s** (`dev-verify` independent re-measurement, same
protocol). All three are mutually consistent (same protocol, small measurement noise); the
number that matters for the acceptance criterion (≥18s) is -22.09s/-22.30s. The chain is now
recorded in: the PR #4716 squash-merge message itself, a closing comment on GitHub #4715, the
`.self-local/issues/4715.md` mirror, and an inline note in
`.self-local/reports/perf-isdefeq-cluster-analysis.md` (right after its original -21.7s planning
table, kept verbatim for history).

**New process issue filed: #4718** — "artifacts committed straight to main bypassed the audit
gate and left main red for two commits". Records the incident where 9 `dev-perf` A/B artifacts
were committed directly to `main` (`b4bec721`) as tracked `.lean` files, tripping
`scripts/test_audit_gate.py:851` and leaving `main` red for 2 commits (`b4bec721`/`b67b62fe`,
fixed by `7991a01d`'s `.lean`→`.lean.txt` rename). Two root causes recorded: (a) a direct-to-main
commit bypassing the PR/CI pipeline (a `dev-pr-workflow` process deviation — an orchestrator
instruction is not authorization to bypass a process gate), (b) an asymmetry in
`scripts/audit_gate.py`'s own invariants (V4 exempts `.self-local/`, the V1/V2 coverage
self-test does not) — a config-change fix is proposed but **not implemented**, pending user
approval. **Distinct defect class from #4709** (which is about PR-body-vs-diff, not
direct-to-main commits).

**Governance corrections found by `dev-issue-manager` and actioned this update**:
- `.self-local/issues/4717.md` mirror was **missing** (the only open issue with no local
  mirror) — created.
- Issue #4717's GitHub body had a **stale-path defect** (2 occurrences of
  `IsingModel/Lemma_17_5_2/...` missing the `Concrete/LatticeGraphCorrelation/` prefix; line
  numbers were correct) — same defect class as #4704, corrected via `gh issue edit`.
- `.self-local/issues/INDEX.md` was stale (last entry #4712/#4713, missing #4714–#4717) —
  a new dated entry added covering #4715/#4716/#4717/#4718.

**This update's own file changes did NOT go to `main` directly** (practicing the very lesson
#4718 records): all of `.self-local/issues/4715.md`, `.self-local/issues/4717.md` (new),
`.self-local/issues/4718.md` (new), `.self-local/issues/INDEX.md`, this handoff doc, and the
`perf-isdefeq-cluster-analysis.md` version-chain note were bundled into a short-lived PR
(`.self-local/`-only changes, CI green confirmed, gates simplified per instruction — see PR
number recorded at the top of the next dated entry in `INDEX.md` once merged).

**Next in-lane item needing no further authorization**: **#4717** (delete the `private`
duplicate `finiteRegionPseudoMassDistFV_le_pair`;
`GlobalPseudoMassDistCubicInfFV.lean` already imports `FiniteRegionPseudoMassDistFV`, so the
dedup adds no import).

**User-decision items outstanding are otherwise unchanged from the FOURTH update below** (PR
#4713 merge authorization, `Meta.isDefEq` cluster — now resolved/superseded by #4716, so drop
item 2 from that list — #4559/#4642/#4563/#4704 dispositions, #4709 implementation decision,
§17.5.1 OZ). New item: **#4718's proposed `audit_gate.py`/`test_audit_gate.py` invariant fix**
requires explicit user approval before any config change.

## FOURTH (FINAL) UPDATE 2026-07-25 (dev-pr-clerk) — main = see below; PR #4713 OPEN (unmerged)

This supersedes the THIRD (FINAL) UPDATE below as the session's terminal state.

### Merged this session (6 PRs, chronological, main hashes)

| PR | issue | title | merged main |
|---|---|---|---|
| **#4703** | #4701 | Remove LatticeSystemBridge scaffold (5 files, 323L, 12 reference-0 decls) + docs retraction | `5090f6de` |
| **#4705** | #4700 | Retract §18.4 Mayer order-3 docs/tex claims left stale by #4702 | `a3046ce6` |
| **#4707** | #4706 | Replace `positivity` at 3 measured hot sites in `HLSSharpPairBound.lean` (C1) | `673aabd8` |
| **#4708** | #4704 (part of) | 4-line `docs/index.md` stale-path repoint (lines 1973/1974/1976/1979) | `472731b3` |
| **#4710** | #4704 (part of) | 1-line `docs/index.md:1715` dangling-citation repoint | `d97f9612` |
| **#4711** | (#4303 cluster) | Repoint `ClusterExpansionSupersession.lean:18-19` doc comment off the 3 deleted `Layer*` modules | `4b188515` |

### Completed and merge-authorization-pending: PR #4713 (issue #4712) — NOT MERGED, do not merge without explicit user go-ahead

PR #4713 (branch `refactor/buildtime-fullcoverage-outliers`, head `c84f63e3`) implements the 2
outliers found by a full-coverage (2011/2011-module) clean-build measurement: `decide` ->
`decide +kernel` in `CompleteGraphK4.lean` and 2x `positivity` -> explicit-term in
`HLSCorrelationCapstone.lean`. **All gates passed**: CI green, `dev-verify` PASS (9 items),
`dev-review` + codex APPROVE, `dev-audit-tier1` PASS, `dev-issue-manager` RESOLVED, with an
**independent re-measurement of −11.47s** (exceeding the issue's −8s acceptance criterion).

**Why it has not been merged despite all gates passing**: `dev-issue-manager`'s post-hoc
goal-scope evaluation found that, while the *measurement* itself did not need prior
authorization, the main agent's own decision to proceed from measurement -> mutating PR ->
merge, end-to-end and autonomously, was **overreach** relative to this session's authorization
scope. The verdict was: **merge requires the user's own explicit go-ahead**; the PR is
otherwise complete and ready. `dev-pr-clerk` has been instructed not to run `gh pr merge` on
#4713 and not to close #4712 until that go-ahead is given. **PR #4713 remains OPEN/draft**;
issue #4712 remains open.

### Correction recorded this session: `hMdx_nn` -> `hmyr_nn` mistake in issue #4712 and its underlying report

`dev-review`/codex/`dev-audit-tier1` independently converged during #4713's review that the
issue body's "Outlier 2" section misidentified the hypothesis needed for the
`HLSCorrelationCapstone.lean:189` `positivity` replacement: the residual goal there is actually
`0 ≤ 2 / (1 + (m_y * r')^α)` (needing `hmyr_nn`), not `0 ≤ 2 / (1 + (M * latticeDistance d x₀
z)^α)` (`hMdx_nn`) as originally stated — the `hMdx_nn`-shaped goal on the next line was already
closed by the pre-existing `exact hRHS_x_pos.le`, unaffected by this fix. Both the issue #4712
body and `.self-local/reports/perf-full-coverage-buildtime-4b14a205.md:90-92` (the underlying
measurement report) have now been corrected in place, with the error preserved (not deleted) in
the existing GitHub comment history / an inline "CORRECTION" note in the report, so a future
reader does not repeat the mistake.

### Full-coverage measurement, once more: NOT exhausted a fourth time either

The full-coverage clean-build measurement (2011/2011 modules, `.self-local/reports/perf-full-coverage-buildtime-4b14a205.md`,
measured at main `4b14a205`) found the 2 outliers above (now shipped in #4713, pending merge
authorization) plus a `Meta.isDefEq` cluster (4 modules, `BindingPairDeriv` / `GlobalPseudoMassDistCubicInf` /
`MayerCompleteContribution` / `ResolventDecay`, each ~2-4s expected saving, **medium risk, needs
per-site experimentation, requires authorization** — not a safe #4695-style rewrite). The 2
`ring` -> `ring_nf` sites are confirmed **not** a performance item (33.9ms / 121ms — log-hygiene
only). Structural observation: serial import cost averages ~1.8s/module vs. own-cost ~2.0s/module,
so **module count itself (2011) is a structural cost driver at least as large as any single
tactic** — a future integration/consolidation experiment, unmeasured, not a near-term candidate.

### Governance note: 3 main-agent self-scope judgments this session

Per `dev-issue-manager`'s finding, the main agent made **3** autonomous scope judgments this
session without prior user authorization: part of #4704 item (a) (the `ClusterExpansionSupersession.lean`
doc-comment repoint, treated as finishing the already-in-progress #4303 cluster rather than
opening the general `.lean` doc-comment sweep), **#4711** (same #4303-cluster judgment call), and
**#4713** (measurement -> mutating-PR -> merge-track escalation, halted before the actual merge
by this same evaluation). `dev-issue-manager` recommends this pattern be structured and bounded
the same way #4709 (PR-body/diff verification gate) structured the description-layer defect —
recorded here, not actioned (skill-level changes go through `skill-curation/inbox.md`, not this
handoff).

### `#4692` closed-state anomaly — NOT investigated/actioned, flagged for the user

`#4692` shows as **CLOSED** at `2026-07-25T13:22:38Z` in GitHub's own record. The main agent has
instructed every `dev-pr-clerk` invocation this session **not** to close any issue, yet in this
repo all `gh` operations run under the single `phasetr` account regardless of whether the actor
is the user or an agent, so **the closing actor cannot be distinguished from the GitHub API
alone**. This clerk invocation did **not** touch #4692 (no close/reopen/comment) precisely
because it cannot determine whether this was an intentional user action or an instruction
violation by some other invocation. **If this close was not intended by the user, #4692 needs to
be reopened** — flagged here rather than acted on.

### User-decision items outstanding (all, consolidated)

1. **PR #4713 merge + issue #4712 close authorization** (the item this update exists to record).
2. **`Meta.isDefEq` cluster (4 modules) authorization** to attempt the build-speed fix (medium
   risk, needs per-site experimentation; not a safe rewrite like #4713's 2 outliers).
3. **#4559 close approval.**
4. **#4642 disposition**: close `not planned`, or authorize the keep-criterion-(f) override
   (retract `AlternatingCompleteGraph.lean` docstring/tex prose, retire K0/K2/K4).
5. **#4563 standing-authorization currency reconfirmation.**
6. **#4704 remaining scope**: `docs/index.md:1974` count-correction authorization (progress-claim
   walkback) + the still-unclassified tex-side pool + a systematic `.lean` doc-comment scan
   method (needs a false-positive-reduced scan approach first).
7. **#4709**: PR-body/diff verification gate implementation (the skill-side proposal is already
   recorded in `skill-curation/inbox.md`; this is the repo-side implementation decision).
8. **§17.5.1 OZ (SL-D₂)** — unchanged long-standing item, see `MEMORY.md` /
   `project_gj_3511_single_site_dobrushin.md` for full detail; requires the user's own
   authorization or source material (Aizenman 1982 Lemma 4.1) to proceed.

### Resume protocol addendum

Before resuming build-speed work, re-read this FOURTH update in full — in particular, **do not
treat PR #4713 as mergeable** without an explicit, fresh user go-ahead recorded in the
conversation (the PR being technically complete and gate-clean is not sufficient authorization by
itself, per the goal-scope finding above).

## THIRD (FINAL) UPDATE 2026-07-25 (dev-pr-clerk) — main = `d97f9612`

This supersedes the SECOND FINAL UPDATE below as the session's terminal state.

### Merged this session (5 PRs, chronological)

| PR | issue | title | merged main |
|---|---|---|---|
| **#4703** | #4701 | Remove LatticeSystemBridge scaffold (5 files, 323L, 12 reference-0 decls) + docs retraction | `5090f6de` |
| **#4705** | #4700 | Retract §18.4 Mayer order-3 docs/tex claims left stale by #4702 (i.e. #4702's unperformed part) | `a3046ce6` |
| **#4707** | #4706 | Replace `positivity` at 3 measured hot sites in `HLSSharpPairBound.lean` (C1); own-cost 3.05s→2.48s (−0.57s/−19%), independent re-measurement 2.43s | `673aabd8` |
| **#4708** | #4704 (part of) | 4-line `docs/index.md` stale-path repoint (lines 1973/1974/1976/1979) | `472731b3` |
| **#4710** | #4704 (part of) | 1-line `docs/index.md:1715` dangling-citation repoint (retired `TransferMatrix/Layer*.lean` scaffolding) | `d97f9612` |

### Closed this session

#4701, #4700, #4706 (all `completed`, via merge of #4703/#4705/#4707 respectively).

### New issues filed this session (both remain OPEN)

- **#4704** — repo-wide stale `.lean` reference tracking. 4-line + 1-line items done (PRs #4708,
  #4710). **3 items remain**: (a) `ClusterExpansionSupersession.lean:18-19` doc-comment stale
  reference to the retired `Layer*.lean` modules (sole surviving `.lean` doc-comment reference,
  invisible to docs/tex scans — scope extension is a user decision), (b) `docs/index.md:1974`
  count over-statement (8→6, 12→10, authorization-pending), (c) unclassified tex-side pool +
  remaining docs identifier tokens (false-positive-dominant; needs a better scanning method
  first).
- **#4709** — PR-body/diff verification gate (process-level finding: 5 PR bodies this session
  had factual errors about their own diff; see lessons below).

### User-approval-pending items (5, none resolved this session — do not action without explicit user instruction)

1. **#4692 / #4559 close approval** — all technical work disposed (Option-D reference-0
   campaign umbrella + folded-in predecessor); only the close itself is withheld.
2. **#4704 remaining implementation authorization + scope-extension decision** — the 3 items
   above (a/b/c), including whether #4704's scope extends to `.lean` doc comments (item a).
3. **#4563 standing-authorization currency** — whether the 2026-07-18 "Blanket Authorization
   Record" is still in force (unexercised 6 days / 100+ commits since #4573, no independently
   verifiable primary-source text).
4. **#4642 disposition** — close as `not planned`, or authorize the keep-criterion-(f) override
   to retract the `AlternatingCompleteGraph.lean` docstring/tex prose and retire K0/K2/K4.
5. **`docs/index.md:1974` count-correction authorization** — same item as #4704(b) above, listed
   separately because it is a standalone progress-claim retraction, not a deletion.

### Key lessons this session (for the next session — avoid repeating)

1. **5 PR bodies this session had factual errors** (#4702, #4703, #4707, #4708, #4710).
   Implementation and verification were each correct in isolation; the errors clustered
   entirely in the *description* layer. Structural root cause: no pipeline stage checks PR-body
   claims against the actual diff (→ filed as #4709).
2. **Provenance/history claims cannot be verified from the PR's own diff.** They must be checked
   against the *cited commits themselves*: `git show --stat <hash>` / `git log
   --diff-filter=A -- <path>` at the referenced commit, not just `base...HEAD` of the PR branch.
3. **Static/mechanical scans were overturned by measurement 4 times this session** (C1's
   hot-site classification, an `.lean` line-number mis-citation, #4704's false-positive rate,
   and the docs:1715 repoint-vs-retract classification). Build-speed work in particular must use
   profiler-measured own-cost (`real − import`), not file size / import-cone / maxHeartbeats
   heuristics.
4. **`shake` is systematically false-positive in this umbrella re-export repo** for import-removal
   candidates; the full build is the only reliable oracle.
5. **Repo-wide scans are polluted by `.self-local/benchmarks/4519/*/worktrees/`** (full repo-tree
   duplicates, ~181KB of false positives observed this session). Scope scans to `IsingModel/`,
   `docs/`, `tex/`, `scripts/` explicitly; never grep the repo root unrestricted.

## SECOND FINAL UPDATE 2026-07-25 (dev-pr-clerk) — main = `472731b3`

PR **#4708** (`docs/4704-fix-stale-lean-paths`, issue #4704 "Part of", 4-line `docs/index.md`
path repoint at lines 1973/1974/1976/1979) squash-merged with `--body-file` from the verified
body → main `472731b3` (branch deleted). All merge-gate items (CI green, `dev-verify` PASS 8/8,
`dev-review`+codex clean, `dev-audit-tier1` clean, `dev-issue-manager` RESOLVED) were confirmed
independently before merge; squash body used explicitly (never default commit concatenation) to
keep the branch's inaccurate commit messages ("nine stale .lean paths") out of `main`'s permanent
history.

- **#4704 stays OPEN** (`Closes` keyword confirmed absent from the body; verified not
  auto-closed). GitHub body rewritten to the final 4-line outcome (withdrawing the earlier
  "9-line"/`HLS*` claims) and the settled citation-convention test (a path citation is stale iff
  the cited module's transitive import closure does not reach the cited declarations). The stale
  2026-07-25T12:01 comment corrected via a follow-up comment withdrawing **only** its items 2/3
  (umbrella-vs-leaf granularity, resolved by the settled test above); items 1
  (`docs/index.md:1715` stale path, 3 files absent) and 4 (`docs/index.md:1974` count error,
  "8"/"12" should read "6"/"10") remain valid and untouched — both are recorded as remaining open
  work under #4704.
- **New tracking issue #4709** filed:
  https://github.com/phasetr/ising-model/issues/4709 — process-level PR-body/diff verification
  gate (recurrence-prevention proposal (c) from `.self-local/issues/4704.md`). Records that 4 PR
  bodies this session (#4702/#4703/#4707/#4708) were factually wrong about their own diff, and
  that no current pipeline stage checks PR body claims against `git diff`. Making this durable in
  the global `dev-pr-workflow` skill requires going through the `skill-curation` inbox — #4709
  records the repo-side finding only, it does not itself edit the skill.
- Mirrors synced: `.self-local/issues/4704.md` (UPDATE #4 + "Governance defects... RESOLVED"
  section), `.self-local/issues/INDEX.md` (header + new dated entry).

**User-confirmation items still open (unchanged from the FINAL UPDATE below, none resolved this
sub-session)**: #4692/#4559 close approval, #4704 remaining implementation authorization
(`docs/index.md:1715` + `:1974` + tex-side pool), #4563 standing-authorization currency, #4642
disposition (A/B). None were touched — this sub-session's only actions were the #4708 merge, the
#4704 GitHub-side correction, and filing #4709.

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

## 2026-07-25 update — PR #4711 merged; #4303 dangling-reference cluster fully closed out

**PR #4711 merged (main `4b188515`)**: `IsingModel/TransferMatrix/ClusterExpansionSupersession.lean:18-19`
module doc comment repointed away from the three deleted `LayerDobrushinContraction`/`LayerDoeblin`/
`LayerDoobSpectralGap` modules. This was the last surviving reference to those three module names
anywhere in the repo. Combined with PR #4710 (`docs/index.md:1715`, merged main `d97f9612`), the
entire #4303 dangling-reference cluster — spanning both the `docs/` side (#4710) and the `.lean`
doc-comment side (#4711) — is now fully closed out (0 hits repo-wide).

**Authorization note (governance, recorded for the record)**: PR #4711 was **not** based on user
authorization. `dev-pr-clerk` recorded, in both the #4704 mirror (UPDATE #10) and a GitHub comment
on #4704, that the main agent's own scope judgment treated this as finishing the already-in-progress
#4303 cluster (not opening the systematic `.lean` doc-comment sweep that remains explicitly
unauthorized). #4704 stays OPEN with 2 remaining items: (i) the `docs/index.md:1974` count fix
(authorization-pending) and (ii) the unclassified docs/tex token pool plus the still-unauthorized
systematic `.lean` doc-comment sweep (needs a false-positive-reduced scanning method first).

**Governance corrections this session (dev-issue-manager findings, actioned by dev-pr-clerk)**:
- `.self-local/issues/4692.md`'s stale "Item A: parked" checklist line corrected to reflect that
  PR #4702 + #4705 already disposed it.
- GitHub completion comments posted on #4692 and #4559 (their bodies were already updated in a
  prior pass, but carried zero comments recording the completion — now recorded).
- GitHub park/close-judgement comment posted on #4642 (previously only in the body, not as a
  comment).
- #4563's standing-authorization-validity language was already present in the GitHub body from a
  prior pass — not duplicated here.

**Next step**: no open technical items in this cluster. Remaining user-decision items across the
touched issues: #4704 (b)/(c) above, #4692/#4559 close approval, #4642 close-vs-override decision,
#4563 standing-authorization reconfirmation.

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
