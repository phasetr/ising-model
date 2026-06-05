import IsingModel.Inequalities.GKSBoundaryConditionII

/-!
# Two-point clustering bounds for the `+` boundary state (FV §3.7, Issue #3613)

Finite-volume consequences of the `+` boundary GKS inequalities for two-point
functions, towards the high-temperature vanishing of the spontaneous magnetization.

* `symmDiff_pair` — `{i} ∆ {j} = {i, j}` for `i ≠ j`.
* `gibbsExpectationBC_plus_spinProduct_pair_nonneg` — `⟨σ_i σ_j⟩⁺_Λ ≥ 0` (GKS-I).
* `gibbsExpectationBC_plus_two_point_ge_product` — the clustering bound
  `⟨σ_i⟩⁺_Λ · ⟨σ_j⟩⁺_Λ ≤ ⟨σ_i σ_j⟩⁺_Λ` (GKS-II).

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7; Theorem 3.49 (GKS).
-/

namespace IsingModel

open Finset
open scoped symmDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- **Symmetric difference of two singletons**: `{i} ∆ {j} = {i, j}` for `i ≠ j`. -/
theorem symmDiff_pair {i j : ι} (hij : i ≠ j) :
    (({i} : Finset ι) ∆ {j}) = {i, j} := by
  ext a
  simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
  constructor
  · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact Or.inl ⟨rfl, hij⟩
    · exact Or.inr ⟨rfl, fun h => hij h.symm⟩

/-- **GKS-I for the pair correlation**: `⟨σ_i σ_j⟩⁺_Λ ≥ 0`. -/
theorem gibbsExpectationBC_plus_spinProduct_pair_nonneg (G : SimpleGraph ι)
    [Fintype G.edgeSet] {β J h : ℝ} (hβ : 0 < β) (hJ : 0 ≤ J) (hh : 0 ≤ h)
    (Λ : Finset ι) (i j : ι) :
    0 ≤ gibbsExpectationBC G β (fun _ => J) h Λ (plusConfig ι) (spinProduct {i, j}) :=
  gibbsExpectationBC_plus_spinProduct_nonneg G hβ hJ hh Λ {i, j}

/-- **GKS-II two-point clustering bound for the `+` boundary state**: for `i ≠ j`,
`⟨σ_i⟩⁺_Λ · ⟨σ_j⟩⁺_Λ ≤ ⟨σ_i σ_j⟩⁺_Λ`. -/
theorem gibbsExpectationBC_plus_two_point_ge_product (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J h : ℝ} (hβ : 0 < β) (hJ : 0 ≤ J) (hh : 0 ≤ h) (Λ : Finset ι) {i j : ι}
    (hij : i ≠ j) :
    gibbsExpectationBC G β (fun _ => J) h Λ (plusConfig ι) (spinProduct {i}) *
        gibbsExpectationBC G β (fun _ => J) h Λ (plusConfig ι) (spinProduct {j}) ≤
      gibbsExpectationBC G β (fun _ => J) h Λ (plusConfig ι) (spinProduct {i, j}) := by
  have h := gibbsExpectationBC_plus_gks_second G hβ hJ hh Λ {i} {j}
  rwa [symmDiff_pair hij] at h

end IsingModel
