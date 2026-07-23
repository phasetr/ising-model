import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d Λ-direct Z ratio-bound wrappers

Narrow child module for four ℤ^d Λ-direct
`partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_bound*`
wrappers extracted from `HighTemperatureBoundsRatioBounds.lean`:

* `_ratio_bound`,
* `_ratio_bound_beta_zero`,
* `_ratio_bound_ferromagnetic`,
* `_ratio_bound_beta_zero_ferromagnetic`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ Z ratio upper bound at J=0**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_bound
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ Z ratio upper bound at β=0**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_bound_beta_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_beta_zero
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ ferromagnetic Z ratio upper bound at J=0**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_bound_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ

/-- **ℤ^d Λ ferromagnetic Z ratio upper bound at β=0**. -/
theorem
partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_bound_beta_zero_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_beta_zero_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ

end Ambient
end IsingModel
