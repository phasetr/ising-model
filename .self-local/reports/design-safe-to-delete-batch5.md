# Design — #4746 Item A, safe-to-delete batch 5

Author: `dev-design` (independent re-measurement; nothing below is taken from the issue on trust).
Date: 2026-07-28.

## 0. Measurement provenance (reproduce before implementing)

| item | value |
|---|---|
| commit measured | `7bb3c48b` (`origin/main`; `ecdaf2e5` = PR #4759 + `7bb3c48b` mirror-only commit) |
| scanner blob | `git hash-object scripts/dead_candidate_scan.py` = **`746b34e8`** (was `7f47c6bd` pre-#4759) |
| command | `python3 scripts/dead_candidate_scan.py --pattern '.' --report-only --json out.json` (scanner unmodified) |
| scanned declarations | 10,837 (census via `dead_candidate_scan.load_tree` = 10,887; 50 anonymous) |
| runtime | 120 s |

Local `main` was 4 commits behind `origin/main` at the start of this pass; every figure below is
measured in a detached worktree at `origin/main`, not in the primary checkout.

## 1. The lane is 120 modules, not 146 — PR #4759 shrank it by 26

Fully-dead is applied exactly as issue #4746 defines it: for module `M`, `scanned(M) == census(M)`
and **every** declaration reads `safe-to-delete`.

| quantity | main `323725d2` (recorded) | main `7bb3c48b` (**this measurement**) |
|---|---|---|
| `safe-to-delete` declarations, whole tree | 1091 | **1063** |
| fully-dead modules, raw | 199 (633 decls / 16,452 lines) | **167** (526 decls / 14,157 lines) |
| excluding `Lemma_17_5_2` | 194 (605 / 14,507) | **162** (498 / 12,212) |
| **lane-eligible** after the path allow-list | 146 (523 / 11,488) | **120** (424 decls / 9,467 lines) |

The drop is the intended effect of PR #4759 (`MAX_CHARGED_GLOB_MATCHES = 10`): narrow globs that
were charged to nobody now protect their members, so 26 modules left the fully-dead set. The
`146 / 523 / 11,488` figures in the issue body are one scanner-blob stale and must be restated.

Composition of the 120 (all inside the fail-closed allow-list):

| cluster | modules | decls | lines |
|---|---|---|---|
| `LatticeGraphCorrelation/HighTemperature*` | 15 | 44 | 1112 |
| `LatticeGraphCorrelation/Mayer*` | 14 | 44 | 1093 |
| `LatticeGraphCorrelation/UniformMag*` | 13 | 44 | 727 |
| `LatticeGraphCorrelation/PolymerFreeEnergy*` | 10 | 34 | 781 |
| **`PseudoMass/FromParams*` (batch 5)** | **10** | **63** | **1801** |
| `LatticeGraphCorrelation/TwoPoint*` | 9 | 28 | 575 |
| `LatticeGraphCorrelation/FreeEnergySpecialCases*` | 8 | 25 | 497 |
| `LatticeGraphCorrelation/Base*` | 7 | 25 | 414 |
| `LatticeGraphCorrelation/{Joint,PartitionFunction}*` | 6 + 6 | 20 + 21 | 373 + 367 |
| `LatticeGraphCorrelation/FreeEnergyAnalyticity*` | 4 | 13 | 248 |
| `LatticeGraphCorrelation/{LatticeMass,Magnetization,PartitionFreeEnergy,PerStage}*` | 3 each | 9/12/10/12 | 337/201/189/249 |
| `LatticeGraphCorrelation/{CorrelationSymmetry,FiniteVolumeBasics}*` | 2 each | 6 each | 135 / 91 |
| `Concrete/CenteredSlab/Consistency.lean`, `LatticeGraphCorrelation/Translation*` | 1 each | 5 / 3 | 216 / 61 |
| **total** | **120** | **424** | **9467** |

## 2. Standing exclusion derived from Item F's open residuals (fail-closed)

Item F's two unrepaired residuals were re-measured directly rather than assumed:

* **F-1 (nested braces).** `expand_braces` does not recurse: **178** doc tokens still expand to
  something containing `{`. Charged against a fail-closed *recursive* expander they would protect
  **30** declarations.
* **New residual (zero-resolution namespace-qualified glob).** `_resolve_fragment` anchors the
  regex against the whole token but matches only the final path component, so an
  `IsingModel.…{a,b}_foo_*` token resolves to zero, charges nobody, and is not even filed as a
  family label. Measured: **29** occurrences / **20** distinct source tokens; read by final
  component (and subject to the same `MAX_CHARGED_GLOB_MATCHES = 10` policy) they would protect
  **50** declarations.

Intersecting both shadow sets with the 120-module lane gives exactly **2 tainted modules**:

| module | residual | site |
|---|---|---|
| `IsingModel/Concrete/LatticeGraphCorrelation/PerStageSubgraphConvergent.lean` | new residual | `tex/proof-guide.tex:3861` `IsingModel.{magnetization,truncated2,susceptibility,magnetization_total}_convergent_*` |
| `IsingModel/Concrete/LatticeGraphCorrelation/PartitionFunctionSymmetryLogCubic.lean` | F-1 | `docs/index.md:1381` `log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_{neg_h,eq_abs_h,monotone_{J,h,beta,abs_h}}` |

Two consequences.

1. **The record needs a correction**: the issue states F-1 covers "0 declarations in the lane".
   At `7bb3c48b` it covers one lane module (`PartitionFunctionSymmetryLogCubic.lean`). F-1 is
   live, not merely latent, for deletion purposes.
2. **Operative guard.** These 2 modules are added to the fail-closed exclusion list and may not be
   deleted by any batch until Item F's residuals are repaired or the sites are rewritten. That is
   a 2-module cost, not a lane-wide block: the remaining 118 are provably outside both shadow
   sets. This design therefore proposes proceeding with batch 5 under the exclusion, rather than
   waiting for a scanner fix. **Main to decide** — the alternative (block batch 5 until the
   residual is fixed, as F-2/F-3 blocked it) is defensible but costs a full scanner PR first.

## 3. Batch 5 selection: the `PseudoMass/FromParams*` trivial-slice chain (10 modules)

Selected because it is the only cluster in the lane that is simultaneously (a) a *complete* subtree
clearance, (b) cascade-confined to its own directory, and (c) documentation-free.

### 3.1 Delete set (10 fully-dead modules, 63 declarations, 1801 lines)

| module | decls | lines |
|---|---|---|
| `IsingModel/PseudoMass/FromParamsBasic/JZeroEquiv.lean` | 6 | 171 |
| `IsingModel/PseudoMass/FromParamsBasic/MonotonicityBounds.lean` | 8 | 276 |
| `IsingModel/PseudoMass/FromParamsBounds/LogBounds.lean` | 14 | 280 |
| `IsingModel/PseudoMass/FromParamsBounds/TendstoAndLower.lean` | 7 | 195 |
| `IsingModel/PseudoMass/FromParamsBounds/HZeroComparisons.lean` | 5 | 159 |
| `IsingModel/PseudoMass/FromParamsBounds/JZeroComparisons.lean` | 5 | 146 |
| `IsingModel/PseudoMass/FromParamsHZero/HZeroTruncatedBounds.lean` | 8 | 225 |
| `IsingModel/PseudoMass/FromParamsHZero/JZeroValues.lean` | 2 | 74 |
| `IsingModel/PseudoMass/FromParamsHZero/JZeroBetaRegularity.lean` | 2 | 112 |
| `IsingModel/PseudoMass/FromParamsHZero/JZeroHRegularity.lean` | 6 | 163 |
| **total** | **63** | **1801** |

Every declaration is a `theorem` named `IsingModel.pseudoMassFromParamsAtPair_*` (plus one
`pseudoMassExt_tendsto_zero_at_two`) stating a **degenerate-slice** fact — `J = 0`, `h = 0`, or a
comparison/iff transport at those slices. GJ Lemma 17.5.2 needs the *general* pair pseudo-mass;
the live §17.5 chain is `Concrete/LatticeGraphCorrelation/**` + `Lemma_17_5_2/**`, both untouched
here. Full declaration list: `JZeroEquiv` 6 × `_at_J_zero_*` / `_at_h_zero_eq`;
`MonotonicityBounds` 8 × `_at_J_zero_*` / `_at_h_zero_*` / `_le_of_corr_ge` / `_ge_of_corr_le`;
`HZeroComparisons` 5 × `_at_h_zero_{lt,gt,le,ge,eq}_pseudoMass_iff_*_truncated2`;
`JZeroComparisons` 5 × `_at_J_zero_distinct_{lt,gt,le,ge,eq}_pseudoMass_iff_*_tanh_sq`;
`LogBounds` 14 × `_{lt,le,mul_r_le,mem_Ioo,…}_log_two_div_*`; `TendstoAndLower` 7;
`HZeroTruncatedBounds` 8 × `_at_h_zero_*_truncated2_*`; `JZeroBetaRegularity` 2 (`continuousAt` /
`differentiableAt` at `β > 0`); `JZeroHRegularity` 6 (`{continuous,differentiable}{At,On}` in
`β`/`h`); `JZeroValues` 2.

### 3.2 Import structure — the whole cluster is one linear chain

```
BasicSlices → JZeroEquiv → MonotonicityBounds → GeneralProperties → FromParamsBasic.lean(umbrella)
  → HZeroTruncatedBounds → JZeroValues → JZeroBetaRegularity → JZeroHRegularity
  → FromParamsHZero.lean(umbrella) → LogBounds → TendstoAndLower → HZeroComparisons
  → JZeroComparisons  (terminal: no importer at all)
```

Verified by `grep -rn "^import IsingModel.PseudoMass.FromParams" IsingModel/ test/`: **no module
outside this chain imports any of the 10**. Survivors in the chain are `BasicSlices.lean` and
`GeneralProperties.lean` only.

Required edits beyond the 10 deletions:

1. `IsingModel/PseudoMass/FromParamsBasic/GeneralProperties.lean:1` — repoint
   `…FromParamsBasic.MonotonicityBounds` → `…FromParamsBasic.BasicSlices` (the chain's Mathlib
   path is preserved; `GeneralProperties` references no declaration of the deleted modules, which
   is what "fully dead" means).
2. `IsingModel/PseudoMass/FromParamsHZero.lean` (21 lines) — its **only** import is the deleted
   `JZeroHRegularity`, and its only importer is the deleted `LogBounds`. **Delete the file.**
3. `IsingModel/PseudoMass/FromParamsBounds.lean` (6 lines) — a doc-only stub with no imports,
   describing a directory that becomes empty; its only importer is
   `IsingModel/PseudoMass.lean:1`. **Delete it and drop that import line.** (Keeping it would
   leave a module whose doc comment — "retained as a stable import path in the pseudo-mass
   parameter bound layer" — is false. **Main to decide** if the reviewer prefers to keep the
   compatibility path; the batch is correct either way.)

Total diff: **12 files deleted**, 1 import repointed, 1 import line removed, 1828 lines.

The `FromParamsHZero.lean` doc block claims umbrella reachability for the capstone audit; check V3
reads `scripts/audit/capstones.txt`, which contains **no** `pseudoMassFromParams*` name (33
entries checked), so V3 is unaffected.

### 3.3 Cascade (declarations that become reference-0 as a consequence — **not** deleted here)

7 declarations, **all inside `IsingModel/PseudoMass/`**, none in `ClusterExpansion`,
`Inequalities`, `RandomCurrent`, `Peierls`, `AmbientLattice` or `Lemma_17_5_2`:

| declaration | file | verdict today |
|---|---|---|
| `pseudoMass_lt_two_sub_div_mul_r`, `pseudoMass_le_two_sub_div_mul_r`, `pseudoMass_lt_log_two_div`, `pseudoMass_antitone` | `PseudoMass/Basic.lean` | `uncertain` (module-cited in docs **and** tex) |
| `pseudoMassExt_tanh_sq_continuousAt_pos`, `pseudoMassExt_tanh_sq_differentiableAt_pos` | `PseudoMass/Ext.lean` | `uncertain` (module-cited in docs) |
| `pseudoMassFromParamsAtPair_diag_h_zero` | `FromParamsBasic/BasicSlices.lean` | already `safe-to-delete` today (pre-existing, not created by this batch) |

Six of the seven stay fail-closed protected by module citations, so no later batch can sweep them
without an explicit docs decision. This is the smallest cascade of any candidate grouping measured
(compare: `UniformMag*` 27, `Mayer*` 41, `Polymer*` 27, `PartitionFunction/PerStage` 24 — all into
`AmbientLattice`).

### 3.4 Documentation invariance — pre-check (condition (v))

* `grep` of `docs/index.md`, `tex/proof-guide.tex`, `README.md`, `test/`, `scripts/` for
  `FromParamsBasic` / `FromParamsBounds` / `FromParamsHZero`: **0 hits**. No module-directory
  bullet, no `\texttt{*.lean}` file reference, no `\path{…}`.
* `scripts/audit/citation_baseline.tsv`: **0** rows mention `FromParams`.
* None of the 63 declaration names is cited exactly or by brace expansion in any documentation
  (that is what their `safe-to-delete` verdict asserts, and the family-label sites touching them
  are only generic library-wide suffix labels `_pos` / `_eq` / `_sq` at `docs/index.md:620-640`,
  which name no concrete result and lose no count).
* No prose count claim in `docs/index.md` or `tex/proof-guide.tex` covers these wrappers: every
  §17.5 pseudo-mass row cites `Concrete/LatticeGraphCorrelation/**` declarations (rows 1804-1807,
  1812-1813, 1818-1825, 1835, 1840, 1859-1886), none of which is in the delete set.

**Expected docs/tex diff for batch 5: empty.** Condition (v)'s double sweep (pre-deletion library
× pre-PR docs, and pre-deletion library × post-PR docs) is therefore expected to compare identical
inputs and report 0 verdict changes / 0 violations. It must still be *run and reported* — an empty
predicted diff is a prediction, not evidence, and it is exactly the check that would catch the
prediction being wrong.

### 3.5 Name-collision trap (the one real hazard in this batch)

A boundary-aware raw-substring scan of the 63 names over every tracked file finds **6 hits outside
the delete set**, all of them a **prefix collision with a surviving book-content declaration**:

* `pseudoMassFromParamsAtPair_ge_of_corr_le` (deleted, `MonotonicityBounds.lean:204`) is a strict
  prefix of `pseudoMassFromParamsAtPair_ge_of_corr_le_pseudoMassG` (**kept**,
  `Concrete/LatticeGraphCorrelation/Lemma_17_5_2/HLSBridgeFromCubicTanhCore.lean:194`), which is
  used at `Lemma_17_5_2/PerActivePairRateFromUniformTransfer.lean:18/74/86`,
  `HLSBridgeFromCubicTanhCore.lean:238` and cited at `docs/index.md:2031`.

A naive `grep -rn` / `sed` cleanup on the deleted names would corrupt GJ Lemma 17.5.2 content.
**Every reference sweep in this PR must be boundary-aware** (reject a match followed by
`[A-Za-z0-9_']`). Code references after excluding the collision: **0**.

### 3.6 Ratchet (`scripts/test_audit_gate.py`) — no floor is touched

Measured at `7bb3c48b`: `iter_checked_files()` = **1984** (floor 1957), `iter_lib_files()` =
**1977** (floor 1950). Deleting 12 files gives 1972 / 1965, i.e. slack 15 / 15; the assertions are
`assertGreater`, so both still pass. `V4_FILE_FLOOR = 1977` against ~2014 leaves ~25.
**Do not lower the floors in this PR** — the standing decision at
`scripts/test_audit_gate.py:837-840` (the batch that would actually trip a floor must land F1
instead of recalibrating) remains in force, and this batch does not trip one. Note the 12-file
diff (not 10) consumes slack slightly faster than the issue's ten-per-batch projection: after
batch 5 the next ten-module batch leaves 5, so **F1 is due before batch 7** and possibly before a
large batch 6.

## 4. Alternatives considered (and why not)

| grouping | modules / decls / lines | cascade | doc surface | verdict |
|---|---|---|---|---|
| `PseudoMass/FromParams*` (chosen) | 10 / 63 / 1801 | **7, all in `PseudoMass/`** | **0 sites** | selected |
| `Base*` + `CorrelationSymmetryMagnetization*` | 9 / 31 / 549 | 3 (`AmbientLattice`) | 90 family sites, incl. `tex:24504 spontaneousCorrelation_*` | good fallback, smaller payoff |
| `FreeEnergySpecialCases*` + `FreeEnergyAnalyticity*` | 12 / 38 / 745 | 9 | 54 sites incl. 4 count-bearing `freeEnergyAlongExhaustion_*` labels | high docs cost |
| `TwoPoint*` | 9 / 28 / 575 | 11 | 61 sites | medium |
| `UniformMag*` / `Mayer*` / `Polymer*` | 13 / 14 / 10 | 27 / 41 / 27 | large | later batches |

**Fallback if a smaller diff is wanted**: delete only `FromParamsBounds/**` + `FromParamsHZero/**`
(8 modules / 49 decls / 1354 lines + the two umbrella stubs). That variant needs **no**
`GeneralProperties` repoint, and leaves `JZeroEquiv` + `MonotonicityBounds` for batch 6. The
10-module form is preferred because it clears the whole chain in one logical unit.

## 5. PR plan (one PR — this is one logical unit)

`refactor(dead-code): delete the fully-dead PseudoMass FromParams* trivial-slice chain (#4746 Item A, batch 5)`

1. Branch + empty commit + push + **draft PR first** (repo rule), then implement.
2. Delete the 10 modules + `FromParamsHZero.lean` + `FromParamsBounds.lean`.
3. Repoint `GeneralProperties.lean:1` to `BasicSlices`; drop `IsingModel/PseudoMass.lean:1`.
4. Correct any in-library doc comment that names a deleted module as a residence
   (`grep -n "FromParams" IsingModel/PseudoMass/**/*.lean` on the surviving files — batches 3 and
   4 both found this class late; `FromParamsBasic.lean`'s "re-exports the split … wrappers" and
   `GeneralProperties`' header must still be true after the repoint).
5. Docs/tex: expected empty; assert it, do not assume it.
6. Gates, then merge, then mirror + issue comment with the corrected lane figures from §1 and the
   F-1 correction from §2.

Do **not** bundle the Item F scanner fix into this PR.

## 6. Test / verification plan (the PR body must carry all five)

* **(i)** `dead_candidate_scan.py --lean` on a **green pre-deletion build**, over the 63 names —
  must report that no consumer seen by Lean was missed on a `safe-to-delete` verdict. Batch 3
  omitted this from the body and had to have it reconstructed by the tier-1 audit; do not repeat.
* **(ii)** Boundary-aware reference sweep of the 63 names over every tracked file, pre- and
  post-deletion, explicitly separating prefix collisions (§3.5 predicts exactly 6, all
  `_ge_of_corr_le_pseudoMassG`) from real references (predicts 0).
* **(iii)** `lake build` exit 0 with **0 warning / 0 error** (`warningAsError = true` since #4756
  means warnings now fail the build). Job count must drop by exactly the number of deleted
  modules relative to the pre-deletion tip — quote both numbers and the base commit.
  `lake exe GKSTest` exit 0.
* **(iv)** `audit_gate.py --full` PASS; `test_audit_gate.py` OK **without lowering any floor**;
  `citation_audit.py` PASS with gating findings **960** unchanged and ratchet 0/0;
  `dead_candidate_scan.py --self-test` OK; `#print axioms` on the capstones =
  `[propext, Classical.choice, Quot.sound]`.
* **(v)** Documentation-invariance **double sweep**, run from scratch with the unmodified scanner
  (record blob `746b34e8`): (①) pre-deletion library × pre-PR docs/tex, (②) pre-deletion library ×
  post-PR docs/tex. Assert no declaration outside the delete set moves *into* `safe-to-delete`.
  On the synthesized tree the 63 names must read
  `published-result 0 / load-bearing 0 / uncertain 0 / safe-to-delete 63`, coverage warnings 0,
  both canaries PASS.
* Regression guard specific to this batch: after the repoint, `GeneralProperties.lean` and every
  `Lemma_17_5_2/**` module that reaches `BasicSlices` must still build; that is covered by (iii),
  but the PR body should name it, because the repoint is the only behavioural change in the diff.

## 7. Open decisions for main

1. **Proceed under the §2 fail-closed 2-module exclusion, or block batch 5 until Item F's
   zero-resolution residual is fixed?** This design recommends proceeding; the exclusion is
   measured, not assumed.
2. **Delete the two empty-directory umbrella stubs** (`FromParamsBounds.lean`,
   `FromParamsHZero.lean`) or keep them as compatibility paths? Recommendation: delete.
3. The issue body's Item A figures (`146 / 523 / 11,488`) and its F-1 claim ("0 in the lane") are
   both stale/wrong at `7bb3c48b` and should be corrected by `dev-issue-manager` when batch 5 is
   recorded.
