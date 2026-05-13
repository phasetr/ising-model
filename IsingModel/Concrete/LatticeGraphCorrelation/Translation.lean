/- Translation.lean
Concrete translation invariance theorems for the ℤ^d Ising model:
finite-volume, along-exhaustion, and infinite-volume wrappers for
correlations, partition functions, free energy, truncated 2/3/4-point
functions, and spontaneous correlation/magnetization.
-/
import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.TranslationVadd

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
The legacy import path is preserved by re-importing the new child.
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
The legacy import path is preserved by re-importing the new child.
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

/-- **Right-limit** `correlationInfinite ⟨J, h, β⟩ → spontaneousCorrelation J β`
as `h → 0⁺` on ℤ^d. -/
theorem tendsto_correlationInfinite_spontaneousCorrelation_latticeGraph
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) :
    Filter.Tendsto
      (fun h : ℝ => correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ A)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (spontaneousCorrelation (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β A)) :=
  tendsto_correlationInfinite_spontaneousCorrelation_nhdsGT
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) hJ hβ A

/-- **Right-limit** `correlationInfinite ⟨J, h, β⟩ → spontaneousCorrelation J β`
as `h → 0⁺` on ℤ^d (any-Exhaustion). -/
theorem tendsto_correlationInfinite_spontaneousCorrelation_latticeGraph_any
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) :
    Filter.Tendsto
      (fun h : ℝ => correlationInfinite (IsingModel.latticeGraph d) Λ
        ⟨J, h, β⟩ A)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A)) :=
  tendsto_correlationInfinite_spontaneousCorrelation_nhdsGT
    (IsingModel.latticeGraph d) Λ hJ hβ A

/-- **Right-limit** `magnetizationInfinite ⟨J, h, β⟩ → spontaneousMagnetization J β`
as `h → 0⁺` on ℤ^d (any-Exhaustion). -/
theorem tendsto_magnetizationInfinite_spontaneousMagnetization_latticeGraph_any
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    Filter.Tendsto
      (fun h : ℝ => magnetizationInfinite (IsingModel.latticeGraph d) Λ
        ⟨J, h, β⟩ i)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i)) :=
  tendsto_magnetizationInfinite_spontaneousMagnetization_nhdsGT
    (IsingModel.latticeGraph d) Λ hJ hβ i

/-! ## Moved: spontaneousCorrelation cubicExhaustion translation + monotone

The three wrappers
`spontaneousCorrelation_latticeGraph_cubicExhaustion_{translation,monotone_J,monotone_beta}`
now live in `TranslationCubicMonotone.lean`. -/

/-- **Exhaustion-independence of `spontaneousCorrelation` on ℤ^d**. -/
theorem spontaneousCorrelation_latticeGraph_indep_exhaustion
    (d : ℕ) (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A
      = spontaneousCorrelation (IsingModel.latticeGraph d) Λ' J β A :=
  spontaneousCorrelation_indep_exhaustion (IsingModel.latticeGraph d)
    Λ Λ' hJ hβ A

/-- **Site-independence of ℤ^d ∞-vol magnetization**:
for ferromagnetic `p` and any two sites `i, j : Fin d → ℤ`,

`magnetizationInfinite (latticeGraph d) (cubicExhaustion d) p i
  = magnetizationInfinite (latticeGraph d) (cubicExhaustion d) p j`.

Consequence of translation invariance: set `t := j - i`; then
`t + i = j` and `magnetizationInfinite_..._translation` gives the
equality. Physical content: on the translation-invariant ℤ^d lattice,
the magnetization is spatially uniform. -/
theorem magnetizationInfinite_latticeGraph_cubicExhaustion_eq
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p i
      = magnetizationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p j := by
  -- Apply `magnetizationInfinite_..._translation` with `t := j - i`.
  have h := magnetizationInfinite_latticeGraph_cubicExhaustion_translation
    d (j - i) p hf i
  -- `h : magnetizationInfinite ... ((j - i) +ᵥ i) = magnetizationInfinite ... i`.
  -- On the self-action, `(j - i) +ᵥ i = (j - i) + i = j`.
  have hvadd : (j - i) +ᵥ i = j := by
    change (j - i) + i = j
    abel
  rw [hvadd] at h
  exact h.symm

/-- **Site-independence of ℤ^d spontaneous magnetization**: for `0 ≤ J`,
`0 < β`, and any two sites `i j : Fin d → ℤ`,
`spontaneousMagnetization (latticeGraph d) (cubicExhaustion d) J β i
  = spontaneousMagnetization (latticeGraph d) (cubicExhaustion d) J β j`.

Proof: set `t := j - i`; `spontaneousMagnetization_translation` gives
`... (t +ᵥ i) = ... i`, and `t +ᵥ i = j` on ℤ^d by `abel`. -/
theorem spontaneousMagnetization_latticeGraph_cubicExhaustion_eq
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i j : Fin d → ℤ) :
    spontaneousMagnetization (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β i
      = spontaneousMagnetization (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) J β j := by
  have h := spontaneousMagnetization_translation (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) (j - i) hJ hβ i
  have hvadd : (j - i) +ᵥ i = j := by
    change (j - i) + i = j
    abel
  rw [hvadd] at h
  exact h.symm

end Ambient
end IsingModel
