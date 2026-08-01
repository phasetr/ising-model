# Design: pure-removal refactor PR (H1 decoration cluster + M2 import hygiene) — 2026-07-17

Source audit: `.self-local/reports/audit-tier2-sweep-2026-07-17.md` (findings H1, M2).
Scope: pure removal only. Out of scope: H2 gate, M1 splits, mathlib finer-import swaps.
Method: every candidate verified by `git grep -w` across `IsingModel/`, `test/`, `docs/`,
`tex/`, `IsingModel.lean`. Reference-graph fixpoint computed to capture cascades
(a decl is removable iff every referrer, minus itself, is also removable and there is no
external/live referrer). Scripts: scratchpad `deadfix.py`, `attrs.py`, `imp.py`.

## 1. H1 — exact removal list (94 theorem/lemma decls, 5 files)

All 94 are `theorem` (0 `def`/`abbrev`), carry **no attributes** (`@[simp]`/`gcongr`/… =
none — verified), and **no KEPT survivor references any of them** (0 survivor proof edits
needed). Split = 78 leaf ref-0 + 16 cascade-dead (only referrers are other removed decls).
Delete all 94 in one commit (cascade lemmas must go together with their dead referrers,
else they re-appear as fresh ref-0 next audit).

### 1a. `IsingModel/PseudoMass/FromParamsBounds/Intervals.lean` — 21 (WHOLE FILE DEAD → delete file)
All 21 decls dead ⇒ delete the file entirely AND remove its only import:
`IsingModel/PseudoMass/FromParamsBounds.lean:1  import IsingModel.PseudoMass.FromParamsBounds.Intervals`.
(No `IsingModel.lean` umbrella entry; no other importer.)
Names: pseudoMassFromParamsAtPair_{at_J_zero_distinct_mem_Iio_log_two_div,
at_J_zero_distinct_mem_Iio_two_sub_tanh_sq, at_J_zero_distinct_mem_Ioo_zero_log_two_div,
at_J_zero_distinct_mem_Ioo_zero_two_sub_div, at_h_zero_ge_pseudoMass_one_uniform,
at_h_zero_mem_Ici_zero, at_h_zero_mem_Iio_log_two_div, at_h_zero_mem_Ioo_zero_log_two_div,
at_h_zero_mem_Ioo_zero_two_sub_div, at_h_zero_pos_iff_ne_zero, eq_pseudoMassExt_iff_corr_eq,
ge_pseudoMassExt_iff_corr_le, gt_pseudoMassExt_iff_corr_lt, le_pseudoMassExt_iff_le_corr,
le_zero_iff_eq_zero, lt_pseudoMassExt_iff_lt_corr, mem_Ici_zero, mem_Ioi_zero_of_corr_mem,
not_lt_zero, not_mem_Iio_zero, pos_iff_ne_zero}.

### 1b. `IsingModel/AmbientLattice/TruncatedFunctions/TwoPoint.lean` — 14
truncated2Infinite_{le_zero_iff_eq_zero, lt_two, mem_Icc_zero_one, mem_Ici_zero,
mem_Ico_zero_two, mem_Iic_one, mem_Iio_two, mem_Ioc_zero_one_of_pos, mem_Ioo_zero_two_of_pos,
not_lt_zero, not_mem_Iio_zero, not_mem_Ioi_one, not_mem_Ioi_two, pos_iff_ne_zero}.

### 1c. `IsingModel/AmbientLattice/CorrelationInfinite/Bounds.lean` — 13
correlationInfinite_{le_zero_iff_eq_zero, mem_Icc_neg_one_one, mem_Icc_zero_one,
mem_Icc_zero_two, mem_Ici_zero, mem_Ico_zero_two, mem_Iic_one, mem_Iio_two,
mem_Ioc_zero_one_of_pos, not_lt_zero, not_mem_Iio_zero, not_mem_Ioi_one, pos_iff_ne_zero}.

### 1d. `IsingModel/PseudoMass/Ext.lean` — 31
neg_pseudoMassExt_{monotoneOn, monotoneOn_Ioc_zero_one, strictMonoOn,
strictMonoOn_Ioc_zero_one, strictMonoOn_Ioo_zero_one};
pseudoMassExt_{antitoneOn_Ioc_zero_one, antitoneOn_Ioo_zero_one, continuousOn,
differentiableOn, eq_iff_of_mem, le_iff, le_zero_iff_eq_zero, lt_iff, mem_Ici_zero,
mem_Iio_log_two_div, mem_Iio_two_sub_div, mem_Ioi_iff_mem, mem_Ioi_zero_of_mem,
mem_Ioo_zero_log_two_div, mem_Ioo_zero_two_sub_div, ne_zero_of_mem, not_lt_zero,
not_mem_Iio_zero, of_nonpos, of_two_le, pos_iff_ne_zero, strictAntiOn_Ioc_zero_one,
strictAntiOn_Ioo_zero_one, tanh_sq_strictAntiOn_Ioi_zero, two, zero}.

### 1e. `IsingModel/PseudoMass/Basic.lean` — 15
pseudoMass_{eq_iff_eq, gt_iff_pseudoMassG_gt, le_iff, lt_iff, lt_iff_pseudoMassG_lt,
mem_Ici_zero, mem_Iio_log_two_div, mem_Iio_two_sub_div, mem_Ioi_zero,
mem_Ioo_zero_log_two_div, mem_Ioo_zero_two_sub_div, mul_r_le_log_two_div,
mul_r_lt_log_two_div, ne_zero, not_mem_Iio_zero}.

### 1f. The 16 cascade-dead (must delete together; only referrers are 1a–1e dead decls)
neg_pseudoMassExt_strictMonoOn, neg_pseudoMassExt_strictMonoOn_Ioc_zero_one,
pseudoMassExt_eq_iff_of_mem, pseudoMassExt_le_iff, pseudoMassExt_lt_iff,
pseudoMassExt_strictAntiOn_Ioc_zero_one, pseudoMassExt_strictAntiOn_Ioo_zero_one,
pseudoMass_eq_iff_eq, pseudoMass_le_iff, pseudoMass_lt_iff, pseudoMass_mem_Iio_log_two_div,
pseudoMass_mem_Iio_two_sub_div, pseudoMass_mem_Ioo_zero_log_two_div,
pseudoMass_mem_Ioo_zero_two_sub_div, truncated2Infinite_lt_two,
truncated2Infinite_pos_iff_ne_zero.

## 2. Rejected candidates (KEPT — live external refs)
52 decls in the 5 files are KEPT because live code references them. Notable decorations
kept (do NOT delete — referenced by live `Concrete/LatticeGraphCorrelation/*` wrappers or
`TransferMatrix/*`): abs_truncated2Infinite_le_one, neg_one_le_truncated2Infinite,
truncated2Infinite_apply, truncated2Infinite_J_zero_diagonal,
truncated2Infinite_le_correlationInfinite, truncated2Infinite_nonneg_of_eq,
truncated2Infinite_sq_le_one, truncated2Infinite_symm, correlationInfinite_sq_le_one,
abs_correlationInfinite_le_of_forall_abs_correlationAlongExhaustion_le,
correlationInfinite_mem_Ioo_zero_two_of_pos (refd by PseudoMassFromParamsHighTempSandwich),
pseudoMassExt_differentiableAt, pseudoMassExt_hasStrictDerivAt, pseudoMassExt_eq_zero_iff,
pseudoMassExt_eq_iff_of_mem→kept? NO (that is dead 1f). Plus all genuine math lemmas
(pseudoMass_nonneg/pos/spec/strictAnti, correlationInfinite_nonneg, truncated2Infinite_h_zero…).

## 3. Optional extension — 3 audit-named `_apply` alias lemmas (verified ref-0, no attrs)
Each a 1-decl unfold/alias, ref-0 (self only), lives in a LIVE file; safe single deletion:
- `IsingModel/AmbientLattice/MagnetizationAlongExhaustion.lean:134  susceptibilityAlongExhaustion_apply`
- `IsingModel/AmbientLattice/MagnetizationInfiniteSusceptibility.lean:61  susceptibilityInfinite_apply` (alias of `susceptibilityInfinite_eq_ciSup`)
- `IsingModel/AmbientLattice/SpontaneousMagnetization.lean:215  spontaneousMagnetization_apply`
Including these ⇒ 97 total. NOT recommended without extra check: `cubicMayerClusterFreeEnergyComplexRestrict_apply`,
`layerCylinderConfigEquiv_symm_apply`, `layerOpenSlabConfigEquiv_symm_apply` (also ref-0 but
in CE / transfer subtree and `_symm_apply` equiv-generated → verify `@[simp]`/automation first).

## 4. Doc / tex sync
- `docs/index.md`, `tex/proof-guide.tex`: **zero** mentions of any removed name (verified).
- In-repo `.lean` comment mentions of removed names: the only real one is
  `Intervals.lean:15` (module doc, inside the file being deleted → moot). The
  `pseudoMassExt_two` "hits" in `LatticeMassPseudoMassTransferTanhPowDist*.lean` are
  substring false positives of the LIVE `pseudoMassExt_twoPointFunction_*` family (`-w`
  ref-count = 0). No comment cleanup required.

## 5. M2 — import removals
### Pinned (safe, exact) — 2
- `IsingModel/TransferMatrix/CycleGraphLink.lean:3  import Mathlib.Tactic`  (full umbrella —
  HIGHEST risk of the 8; rebuild CycleGraphLink + all downstream importers to confirm the
  tactics it uses are still provided by `SimpleGraph.Circulant`/`.Finite`).
- `IsingModel/Inequalities/WalkSum.lean:4  import Mathlib.Tactic.Positivity`  (rebuild WalkSum
  + downstream; confirm `positivity` is unused or transitively available).

### Remaining ~6 intra-repo redundants — DO NOT hand-pick; regenerate with shake
Audit named the files (`AmbientLattice/BetaDerivativeMagnetization.lean`,
`Concrete/LatticeGraphCorrelation/SiteIndepMag*.lean`,
`Concrete/.../PerStageComplex/EventualClosedBallPatches/ClosedBallLocal.lean`) but NOT exact
lines. A textual transitive-closure heuristic **over-reports** (it flagged core modules like
`LatticeGraphBED`/`IntLattice`/`PhaseTransition` that the files actually use) and must not be
used. `lake exe shake` is the authority but currently reports "out of date oleans" — dev-verify
must `lake exe cache get` / `lake build` to a consistent cache, then
`lake exe shake <Module …>` (report-only, no `--fix`) to enumerate the precise `remove`
(no-`instead`) lines, then delete only those. These are "pure redundant" (no downstream churn),
but still rebuild each edited file.

## 6. Verification plan (dev-verify)
1. `lake build` — zero warnings (warningAsError=true catches unused-var/deprecation).
2. `grep -rn "sorry\|admit\|native_decide" IsingModel/` = 0 (unchanged).
3. `lake exe GKSTest` — computational cross-check green.
4. `#print axioms` on a couple of Simon-Lieb / correlation capstones — must equal
   `[propext, Classical.choice, Quot.sound]`; pure dead-lemma removal touches no capstone
   proof so axioms are trivially invariant (spot-check only).
5. Subtree builds per audit caveat: PseudoMass/* (Simon-Lieb subtree) after the Ext/Basic/
   Intervals edits; AmbientLattice/TruncatedFunctions + CorrelationInfinite after those edits.
6. Import step: after each import deletion rebuild that file + its importers (shake with a
   consistent cache is the gate for the 6 intra-repo ones).

## 7. Pitfalls / risks
- **Whole-file delete of Intervals.lean** ⇒ must also drop its import in `FromParamsBounds.lean`
  (only importer; no umbrella entry). Forgetting = build error (import of missing module).
- **Cascade coupling**: the 16 (§1f) are only dead because their sole referrers are in §1a–1e.
  Delete all 94 in one commit; deleting a referrer but leaving a cascade lemma = new ref-0.
- **No `@[simp]`/attributes** on any of the 94 or the 3 `_apply` (verified) ⇒ no silent simp-set
  breakage. (Contrast: the 3 deferred `_symm_apply`/CE `_apply` in §3 are NOT attribute-checked.)
- **Mathlib.Tactic umbrella** removal is the single riskiest edit; full downstream rebuild
  required, not just the file.
- **shake cache staleness**: current oleans out-of-date; do not trust shake output until a
  clean `lake build`/`cache get`.
- No `def`/`abbrev`/`structure`/instance in the removal set (all plain theorems) ⇒ no
  definitional/instance-resolution fallout.

## 8. PR shape (single pure-removal PR, as requested)
One PR, logically ordered commits:
1. Remove the 94 dead decls incl. deleting `Intervals.lean` + fixing `FromParamsBounds.lean`
   import. (Optionally fold in the 3 §3 `_apply` aliases → 97.)
2. Remove the 2 pinned mathlib imports (§5).
3. After shake re-run on a consistent cache, remove the confirmed intra-repo redundant imports.
Do NOT bundle H2/M1. "메인 요판단": whether to include the §3 optional `_apply` extension
(3 verified) and whether to chase the 3 deferred riskier `_apply` after an attribute check.
