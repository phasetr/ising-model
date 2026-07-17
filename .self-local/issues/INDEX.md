# ローカルミラー・インデックス (2026-07-17 更新 — #4506/#4519/#4535/#4538/#4541/#4544/#4547/#4550 CLOSED completed (refactor cycles 1-6))

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
| current-main bottleneck profile | #4533 | **OPEN — v10 TERMINAL INVALID; v11 exact registration and approval complete, execution authority absent** | Attempt `v11-41a5ea8c54e4524153c9599ffe188d92`; no M0 execution. [registration](https://github.com/phasetr/ising-model/issues/4533#issuecomment-4993733856) / [approval](https://github.com/phasetr/ising-model/issues/4533#issuecomment-4993754940) | `4533.md` |

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
