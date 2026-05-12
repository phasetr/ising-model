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

/-- **ℤ^d freeEnergyAlongExhaustion shift translation invariance**:
`freeEnergyAlongExhaustion (Λ.shift t) n = freeEnergyAlongExhaustion Λ n`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_shift_eq
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (t : Fin d → ℤ)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      ((Λ.shift t).volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) (Λ.shift t) p n
      = freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n :=
  freeEnergyAlongExhaustion_shift_eq (IsingModel.latticeGraph d) Λ t p n

/-- **ℤ^d freeEnergyInfinite shift translation invariance**:
`freeEnergyInfinite (Λ.shift t) = freeEnergyInfinite Λ`. -/
theorem freeEnergyInfinite_latticeGraph_shift_eq
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (t : Fin d → ℤ)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      ((Λ.shift t).volume n)).edgeSet]
    (p : IsingParams ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d) (Λ.shift t) p
      = freeEnergyInfinite (IsingModel.latticeGraph d) Λ p :=
  freeEnergyInfinite_shift_eq (IsingModel.latticeGraph d) Λ t p

/-- **ℤ^d free-energy shift invariance**:
`freeEnergyInfinite (latticeGraph d) ((cubicExhaustion d).shift t) p
  = freeEnergyInfinite (latticeGraph d) (cubicExhaustion d) p`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_shift
    (d : ℕ) (t : Fin d → ℤ) (p : IsingParams ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).shift t) p
      = freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p :=
  freeEnergyInfinite_shift_eq (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) t p

/-- **ℤ^d correlationAlongExhaustion shift translation invariance**:
`correlationAlongExhaustion (Λ.shift t) (vaddFinset t A) n = correlationAlongExhaustion Λ A n`. -/
theorem correlationAlongExhaustion_latticeGraph_shift_vaddFinset_eq
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (t : Fin d → ℤ)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      ((Λ.shift t).volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) (Λ.shift t) p
        (vaddFinset t A) n
      = correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n :=
  correlationAlongExhaustion_shift_vaddFinset_eq
    (IsingModel.latticeGraph d) Λ t p A n

/-- **ℤ^d correlationΛ translation invariance**:
`⟨σ^{vadd A}⟩_{t +ᵥ Λ}(p) = ⟨σ^A⟩_Λ(p)` on ℤ^d. -/
theorem correlationΛ_latticeGraph_vaddFinset_eq
    (d : ℕ) (t : Fin d → ℤ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ) (A : Finset (↑Λ : Type _)) :
    correlationΛ (IsingModel.latticeGraph d) (vaddFinset t Λ) p
        (A.map (vaddSubtypeEquiv t Λ).toEmbedding)
      = correlationΛ (IsingModel.latticeGraph d) Λ p A :=
  correlationΛ_vaddFinset_eq (IsingModel.latticeGraph d) t Λ p A

/-- **ℤ^d partitionFunctionΛ translation invariance**:
`Z_{t +ᵥ Λ}(p) = Z_Λ(p)` on ℤ^d. -/
theorem partitionFunctionΛ_latticeGraph_vaddFinset_eq
    (d : ℕ) (t : Fin d → ℤ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) (vaddFinset t Λ) p
      = partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_vaddFinset_eq (IsingModel.latticeGraph d) t Λ p

/-- **ℤ^d freeEnergyΛ translation invariance**:
`f_{t +ᵥ Λ}(p) = f_Λ(p)` on ℤ^d. -/
theorem freeEnergyΛ_latticeGraph_vaddFinset_eq
    (d : ℕ) (t : Fin d → ℤ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) (vaddFinset t Λ) p
      = freeEnergyΛ (IsingModel.latticeGraph d) Λ p :=
  freeEnergyΛ_vaddFinset_eq (IsingModel.latticeGraph d) t Λ p

/-- **ℤ^d log_partitionFunctionΛ translation invariance**:
`log Z_{t +ᵥ Λ}(p) = log Z_Λ(p)` on ℤ^d. -/
theorem log_partitionFunctionΛ_latticeGraph_vaddFinset_eq
    (d : ℕ) (t : Fin d → ℤ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
        (vaddFinset t Λ) p)
      = Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) := by
  rw [partitionFunctionΛ_latticeGraph_vaddFinset_eq d t Λ p]

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

/-- **Translation invariance of `spontaneousCorrelation` on ℤ^d**:
for `0 ≤ J`, `0 < β` and any `t : Fin d → ℤ`,
`spontaneousCorrelation ... J β (vaddFinset t A) = spontaneousCorrelation ... J β A`. -/
theorem spontaneousCorrelation_latticeGraph_cubicExhaustion_translation
    (d : ℕ) (t : Fin d → ℤ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β (vaddFinset t A)
      = spontaneousCorrelation (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) J β A :=
  spontaneousCorrelation_translation (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) t hJ hβ A

/-- **J-monotonicity of `spontaneousCorrelation` on ℤ^d**. -/
theorem spontaneousCorrelation_latticeGraph_cubicExhaustion_monotone_J
    (d : ℕ) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun J : ℝ => spontaneousCorrelation (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β A)
      (Set.Ici 0) :=
  spontaneousCorrelation_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hβ A

/-- **β-monotonicity of `spontaneousCorrelation` on ℤ^d**. -/
theorem spontaneousCorrelation_latticeGraph_cubicExhaustion_monotone_beta
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun β : ℝ => spontaneousCorrelation (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β A)
      (Set.Ioi 0) :=
  spontaneousCorrelation_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ A

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
