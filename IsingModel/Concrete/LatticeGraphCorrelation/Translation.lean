import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
/- Translation.lean
Concrete translation invariance theorems for the ℤ^d Ising model:
finite-volume, along-exhaustion, and infinite-volume wrappers for
correlations, partition functions, free energy, truncated 2/3/4-point
functions, and spontaneous correlation/magnetization.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ## Moved: ℤ^d vaddFinset / translation-invariance wrappers

The 11 ℤ^d translation-invariance wrappers
(`correlationInfinite_latticeGraph_cubicExhaustion_vaddFinset`,
4 `*_latticeGraph_cubicExhaustion_translation` for `magnetizationInfinite`
and `truncated{2,3,4}Infinite`,
`correlationInfinite_latticeGraph_vaddFinset_of_translationInvariant`,
5 `*_latticeGraph_translation` for `spontaneousCorrelation`,
`spontaneousMagnetization`, and `truncated{2,3,4}Infinite`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.TranslationVadd`.
The earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: ℤ^d shift / vaddFinset_eq wrappers

The 8 ℤ^d shift / vaddFinset_eq wrappers
(`freeEnergyAlongExhaustion_latticeGraph_shift_eq`,
`freeEnergyInfinite_latticeGraph_shift_eq`,
`freeEnergyInfinite_latticeGraph_cubicExhaustion_shift`,
`correlationAlongExhaustion_latticeGraph_shift_vaddFinset_eq`,
`correlationΛ_latticeGraph_vaddFinset_eq`,
`partitionFunctionΛ_latticeGraph_vaddFinset_eq`,
`freeEnergyΛ_latticeGraph_vaddFinset_eq`,
`log_partitionFunctionΛ_latticeGraph_vaddFinset_eq`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.TranslationShifts`.
The earlier import path is preserved by re-importing the new child.
-/

/-! ## Concrete `spontaneousCorrelation` on ℤ^d -/

/-- **Nonnegativity of `spontaneousCorrelation` on ℤ^d**. -/
theorem spontaneousCorrelation_latticeGraph_cubicExhaustion_nonneg
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) :
    0 ≤ spontaneousCorrelation (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β A :=
  spontaneousCorrelation_nonneg (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ A

/-- **Upper bound on `spontaneousCorrelation` on ℤ^d**. -/
theorem spontaneousCorrelation_latticeGraph_cubicExhaustion_le_one
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β A ≤ 1 :=
  spontaneousCorrelation_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ A

/-- **ℤ^d `spontaneousMagnetization ≤ magnetizationInfinite`** at positive `h`. -/
theorem spontaneousMagnetization_le_magnetizationInfinite_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    {h : ℝ} (hh : 0 < h) (i : Fin d → ℤ) :
    spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i
      ≤ magnetizationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) i :=
  spontaneousMagnetization_le_magnetizationInfinite
    (IsingModel.latticeGraph d) Λ hJ hβ hh i

/-- **Infimum bound** `spontaneousCorrelation ≤ correlationInfinite ⟨J, h, β⟩`
for `h > 0` on ℤ^d. -/
theorem spontaneousCorrelation_le_correlationInfinite_latticeGraph
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) {h : ℝ} (hh : 0 < h)
    (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β A
      ≤ correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) ⟨J, h, β⟩ A :=
  spontaneousCorrelation_le_correlationInfinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ hh A

/-- **ℤ^d `spontaneousCorrelation ≤ correlationInfinite`** for `h > 0`
(any Exhaustion). -/
theorem spontaneousCorrelation_le_correlationInfinite_latticeGraph_general
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) {h : ℝ} (hh : 0 < h)
    (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) A :=
  spontaneousCorrelation_le_correlationInfinite (IsingModel.latticeGraph d)
    Λ hJ hβ hh A

/-! ## Moved: ℤ^d tendsto correlationInfinite/magnetizationInfinite → spontaneous

The three wrappers
`tendsto_correlationInfinite_spontaneousCorrelation_latticeGraph`,
`tendsto_correlationInfinite_spontaneousCorrelation_latticeGraph_any`,
`tendsto_magnetizationInfinite_spontaneousMagnetization_latticeGraph_any`
now live in `TranslationTendstoSpontaneous.lean`. -/


/-! ## Moved: spontaneousCorrelation cubicExhaustion translation + monotone

The three wrappers
`spontaneousCorrelation_latticeGraph_cubicExhaustion_{translation,monotone_J,monotone_beta}`
now live in `TranslationCubicMonotone.lean`. -/

/-! ## Moved: site-independence / exhaustion-independence wrappers

The three `spontaneousCorrelation_latticeGraph_indep_exhaustion`,
`magnetizationInfinite_latticeGraph_cubicExhaustion_eq`,
`spontaneousMagnetization_latticeGraph_cubicExhaustion_eq` wrappers now
live in `TranslationSiteIndep.lean`. -/



end Ambient
end IsingModel
