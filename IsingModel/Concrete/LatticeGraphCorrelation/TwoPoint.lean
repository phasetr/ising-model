/- TwoPoint.lean
Two-point, truncated two-point, three-point, four-point functions on ℤ^d,
together with their free-energy and correlation monotonicity wrappers.
All definitions and theorems are concrete specialisations of the abstract
`IsingModel.Ambient.*` results to `(IsingModel.latticeGraph d, Ambient.cubicExhaustion d)`.
-/
import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.Translation
import IsingModel.Concrete.LatticeGraphCorrelation.TranslationVaddTruncatedTranslation
import IsingModel.Concrete.LatticeGraphCorrelation.TranslationSiteIndep
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.AmbientLattice.SpecialCases.InfiniteVolume

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ## Two-point function on ℤ^d -/

/-- **Two-point function on ℤ^d** (Finset-based):
`twoPointFunction d p r := correlationInfinite (latticeGraph d)
(cubicExhaustion d) p {0, r}`.

**Caveat (Finset vs physics).** Under ferromagnetic parameters and
for `r ≠ 0`, this equals the physical two-point correlation
`⟨σ_0 σ_r⟩_∞` and depends only on the separation `r`. At `r = 0`,
however, the `Finset` literal `{0, 0}` collapses to `{0}`, so
`twoPointFunction d p 0 = correlationInfinite ... {0}
= magnetizationInfinite ... 0`, *not* the physical `⟨σ_0^2⟩_∞ = 1`.
This is the same `Finset` caveat that already appears in
`susceptibility_J_zero` (`PhaseTransition.lean`). Consumers interpreting
this as the "physical" two-point function should restrict to `r ≠ 0`. -/
noncomputable def twoPointFunction (d : ℕ) (p : IsingParams ℝ)
    (r : Fin d → ℤ) : ℝ :=
  correlationInfinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p {(0 : Fin d → ℤ), r}

/-- **Unfolding of `twoPointFunction`**: `= correlationInfinite ... {0, r}`. -/
theorem twoPointFunction_apply (d : ℕ) (p : IsingParams ℝ) (r : Fin d → ℤ) :
    twoPointFunction d p r
      = correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p {(0 : Fin d → ℤ), r} := rfl

/-- **`twoPointFunction` equals `correlationInfinite` under any Exhaustion**
(ferromagnetic): `twoPointFunction d p r = correlationInfinite (latticeGraph d) Λ' p {0, r}`. -/
theorem twoPointFunction_eq_correlationInfinite_any_exhaustion
    (d : ℕ) (Λ' : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    twoPointFunction d p r
      = correlationInfinite (IsingModel.latticeGraph d) Λ' p {(0 : Fin d → ℤ), r} := by
  rw [twoPointFunction_apply]
  exact correlationInfinite_indep_exhaustion (IsingModel.latticeGraph d)
    _ Λ' p hf _

/-- **Pair correlation equals `twoPointFunction` at the separation**:
for ferromagnetic `p` and any `i, j : Fin d → ℤ`,

`correlationInfinite (latticeGraph d) (cubicExhaustion d) p {i, j}
  = twoPointFunction d p (j - i)`.

Proof: translate the pair `{i, j}` by `-i` using
`correlationInfinite_latticeGraph_cubicExhaustion_vaddFinset`;
`vaddFinset (-i) {i, j} = {-i + i, -i + j} = {0, j - i}`. -/
theorem correlationInfinite_latticeGraph_pair_eq_twoPointFunction
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p {i, j}
      = twoPointFunction d p (j - i) := by
  unfold twoPointFunction
  -- Apply translation by `-i`: `{i, j}` becomes `{0, j - i}`.
  have h_translate := correlationInfinite_latticeGraph_cubicExhaustion_vaddFinset
    d (-i) p hf {i, j}
  -- `vaddFinset (-i) {i, j} = {-i + i, -i + j} = {0, j - i}`.
  have h_finset : vaddFinset (-i) ({i, j} : Finset (Fin d → ℤ))
      = {(0 : Fin d → ℤ), j - i} := by
    rw [vaddFinset_pair]
    have h1 : (-i) +ᵥ i = (0 : Fin d → ℤ) := by
      change -i + i = 0; abel
    have h2 : (-i) +ᵥ j = j - i := by
      change -i + j = j - i; abel
    rw [h1, h2]
  rw [h_finset] at h_translate
  -- Now `h_translate : correlationInfinite ... {0, j - i} = correlationInfinite ... {i, j}`.
  exact h_translate.symm

/-! ## Moved: ℤ^d twoPointFunction_symm

The sign-inversion symmetry wrapper now lives in `TwoPointSymm.lean`. -/


/-- **Truncated two-point function on ℤ^d**:
`truncated2TwoPoint d p r := truncated2Infinite ... p 0 r`.

Packages the site-independence / separation-dependence of the ∞-vol
truncated 2-point correlation on the translation-invariant ℤ^d
Ising model. -/
noncomputable def truncated2TwoPoint (d : ℕ) (p : IsingParams ℝ)
    (r : Fin d → ℤ) : ℝ :=
  truncated2Infinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p 0 r

/-- **Unfolding of `truncated2TwoPoint`**: `= truncated2Infinite ... 0 r`. -/
theorem truncated2TwoPoint_apply (d : ℕ) (p : IsingParams ℝ) (r : Fin d → ℤ) :
    truncated2TwoPoint d p r
      = truncated2Infinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p 0 r := rfl

/-- **`truncated2TwoPoint` equals `truncated2Infinite` under any Exhaustion**
(ferromagnetic). -/
theorem truncated2TwoPoint_eq_truncated2Infinite_any_exhaustion
    (d : ℕ) (Λ' : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    truncated2TwoPoint d p r
      = truncated2Infinite (IsingModel.latticeGraph d) Λ' p 0 r := by
  rw [truncated2TwoPoint_apply]
  exact truncated2Infinite_indep_exhaustion (IsingModel.latticeGraph d)
    _ Λ' p hf 0 r

/-- **Truncated 2-point correlation depends only on the separation**:
for ferromagnetic `p` and any `i, j : Fin d → ℤ`,

`truncated2Infinite ... p i j = truncated2TwoPoint d p (j - i)`.

Proof: apply `truncated2Infinite_latticeGraph_cubicExhaustion_translation`
with `t := -i`, giving `truncated2Infinite ... (-i + i) (-i + j)
= truncated2Infinite ... i j`. Simplify `-i + i = 0`, `-i + j = j - i`. -/
theorem truncated2Infinite_latticeGraph_cubicExhaustion_eq_twoPoint
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    truncated2Infinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p i j
      = truncated2TwoPoint d p (j - i) := by
  have h := truncated2Infinite_latticeGraph_cubicExhaustion_translation
    d (-i) p hf i j
  -- `h : truncated2Infinite ... ((-i) +ᵥ i) ((-i) +ᵥ j) = truncated2Infinite ... i j`.
  have h1 : (-i) +ᵥ i = (0 : Fin d → ℤ) := by change -i + i = 0; abel
  have h2 : (-i) +ᵥ j = j - i := by change -i + j = j - i; abel
  rw [h1, h2] at h
  exact h.symm

/-! ## Moved: ℤ^d truncated2TwoPoint_symm

The sign-inversion symmetry wrapper now lives in `TwoPointSymm.lean`. -/


/-! ## Moved: ℤ^d two-point quantities at `r = 0` (Finset-collapse)

The two wrappers
`twoPointFunction_zero`, `truncated2TwoPoint_zero` now live in
`TwoPointZeroCollapse.lean`. -/


/-! ## Three-point function on ℤ^d -/

/-- **Truncated three-point (Ursell) function on ℤ^d**:
`truncated3TwoPoint d p r s := truncated3Infinite ... p 0 r s`.

Packages the translation invariance of the ∞-volume truncated 3-point
correlation: `truncated3Infinite ... p i j k` depends only on the
two differences `(j - i, k - i)`. -/
noncomputable def truncated3TwoPoint (d : ℕ) (p : IsingParams ℝ)
    (r s : Fin d → ℤ) : ℝ :=
  truncated3Infinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p 0 r s

/-- **Unfolding of `truncated3TwoPoint`**: `= truncated3Infinite ... 0 r s`. -/
theorem truncated3TwoPoint_apply (d : ℕ) (p : IsingParams ℝ)
    (r s : Fin d → ℤ) :
    truncated3TwoPoint d p r s
      = truncated3Infinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p 0 r s := rfl

/-- **`truncated3TwoPoint` equals `truncated3Infinite` under any Exhaustion**
(ferromagnetic). -/
theorem truncated3TwoPoint_eq_truncated3Infinite_any_exhaustion
    (d : ℕ) (Λ' : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (r s : Fin d → ℤ) :
    truncated3TwoPoint d p r s
      = truncated3Infinite (IsingModel.latticeGraph d) Λ' p 0 r s := by
  rw [truncated3TwoPoint_apply]
  exact truncated3Infinite_indep_exhaustion (IsingModel.latticeGraph d)
    _ Λ' p hf 0 r s

/-! ## Moved: ℤ^d truncated3/4Infinite swap wrappers

The 6 concrete ℤ^d `truncated3Infinite_latticeGraph_swap_{ij,jk,ik}`
and `truncated4Infinite_latticeGraph_swap_{ij,jk,kl}` symmetry
wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.TwoPointTruncatedSwaps`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: truncated3Infinite_latticeGraph_cubicExhaustion_eq_threePoint

The translation-invariance wrapper now lives in
`TwoPointEqSeparations.lean`. -/


/-! ## Four-point function on ℤ^d -/

/-- **Lebowitz truncated four-point function on ℤ^d**:
`truncated4TwoPoint d p r s u := truncated4Infinite ... p 0 r s u`.

Packages the translation invariance of the ∞-volume truncated 4-point
correlation: `truncated4Infinite ... p i j k l` depends only on the
three differences `(j - i, k - i, l - i)`. -/
noncomputable def truncated4TwoPoint (d : ℕ) (p : IsingParams ℝ)
    (r s u : Fin d → ℤ) : ℝ :=
  truncated4Infinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p 0 r s u

/-- **Unfolding of `truncated4TwoPoint`**: `= truncated4Infinite ... 0 r s u`. -/
theorem truncated4TwoPoint_apply (d : ℕ) (p : IsingParams ℝ)
    (r s u : Fin d → ℤ) :
    truncated4TwoPoint d p r s u
      = truncated4Infinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p 0 r s u := rfl

/-- **`truncated4TwoPoint` equals `truncated4Infinite` under any Exhaustion**
(ferromagnetic). -/
theorem truncated4TwoPoint_eq_truncated4Infinite_any_exhaustion
    (d : ℕ) (Λ' : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (r s u : Fin d → ℤ) :
    truncated4TwoPoint d p r s u
      = truncated4Infinite (IsingModel.latticeGraph d) Λ' p 0 r s u := by
  rw [truncated4TwoPoint_apply]
  exact truncated4Infinite_indep_exhaustion (IsingModel.latticeGraph d)
    _ Λ' p hf 0 r s u

/-! ## Moved: truncated4Infinite_latticeGraph_cubicExhaustion_eq_fourPoint

The translation-invariance wrapper now lives in
`TwoPointEqSeparations.lean`. -/


/-! ## Moved: ℤ^d truncated2TwoPoint = twoPointFunction - M²

The wrapper
`truncated2TwoPoint_eq_twoPointFunction_sub_magnetization_sq` now
lives in `TwoPointTruncated2EqSubMagSq.lean`. -/


/-! ## Moved: ℤ^d truncated3/4TwoPoint trivial-slice wrappers

The 5 concrete ℤ^d `truncated3TwoPoint` and `truncated4TwoPoint`
trivial-slice wrappers (`truncated3TwoPoint_h_zero_of_distinct`,
`truncated3TwoPoint_J_zero_of_distinct`,
`truncated4TwoPoint_J_zero_of_distinct`,
`truncated4TwoPoint_beta_zero`, `truncated3TwoPoint_beta_zero`)
now live in
`IsingModel.Concrete.LatticeGraphCorrelation.TwoPointTruncatedTrivialSlices`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: ℤ^d twoPointFunction trivial-slice wrappers

The 3 concrete ℤ^d `twoPointFunction_zero_params`,
`twoPointFunction_beta_zero`, and `twoPointFunction_J_zero_of_ne_zero`
trivial-slice wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.TwoPointFunctionTrivialSlices`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: freeEnergy / magnetizationInfinite cubicExhaustion wrappers

The 31 ℤ^d `freeEnergyAlongExhaustion_latticeGraph` /
`freeEnergyInfinite_latticeGraph` / cubicExhaustion convergence,
trivial-slice, monotonicity, and bound wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.TwoPointFreeEnergy`.
The 3 `freeEnergyAlongExhaustion_latticeGraph_{J_zero_tendsto_of_hcard_add,
beta_zero_tendsto_of_hcard_add, tendsto_of_eventually_const}` wrappers
of the same family were deleted; no consumer of them was found in this
repository.
The 2 `spontaneousMagnetization_latticeGraph_cubicExhaustion_monotone_*`
and 3 `magnetizationInfinite_latticeGraph_cubicExhaustion_monotone_*`
variants were further narrowed in PR #2026 into
`IsingModel.Concrete.LatticeGraphCorrelation.TwoPointMagnetizationMonotone`
(see the next Moved block).
The earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: ℤ^d magnetization monotonicity wrappers

The 5 concrete ℤ^d `spontaneousMagnetization_latticeGraph_cubicExhaustion_monotone_{J,beta}`
and `magnetizationInfinite_latticeGraph_cubicExhaustion_monotone_{J,h,beta}`
wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.TwoPointMagnetizationMonotone`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: ambient-subgraph monotonicity + bot wrappers

The 24 ℤ^d wrappers covering ambient-subgraph monotonicity from
`⊥` to `latticeGraph d` (`inducedGraph_latticeGraph_bot`,
`*_bot_le_latticeGraph`, and
`*_latticeGraph_monotone_ambient_subgraph` for `freeEnergy*`,
`partitionFunction*`, `correlation*`, `magnetization*`,
`spontaneous*`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.TwoPointAmbientBot`.
The earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: truncatedInfinite_latticeGraph wrappers

The 16 ℤ^d `truncated2Infinite_latticeGraph_*` wrappers (bounds,
nonneg, symmetry, trivial slices `J_zero` / `β_zero` / `h_zero`),
`truncated3Infinite_latticeGraph_apply`, and
`truncated4Infinite_latticeGraph_apply` now live in
`IsingModel.Concrete.LatticeGraphCorrelation.TwoPointTruncatedInfinite`.
The earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: truncated3/4Infinite_latticeGraph trivial-slice wrappers

The 18 ℤ^d `truncated3Infinite_latticeGraph_*` and
`truncated4Infinite_latticeGraph_*` trivial-slice + nonpos +
exhaustion-independence wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.TwoPointTruncatedHigher`.
The earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: ℤ^d correlationInfinite wrappers

The 7 concrete ℤ^d `correlationInfinite_latticeGraph_*` wrappers
(`_le_one`, `_nonneg`, `_indep_exhaustion`,
`_cubicExhaustion_monotone_h`, `_beta`, `_J`, `_gks_second`) now
live in
`IsingModel.Concrete.LatticeGraphCorrelation.TwoPointCorrelationInfinite`.
The earlier import path is preserved by re-importing the new child.
-/


end Ambient
end IsingModel
