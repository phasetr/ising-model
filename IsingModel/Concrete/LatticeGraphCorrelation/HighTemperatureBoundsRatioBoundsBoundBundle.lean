import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete Λ-direct partitionFunctionΛ ratio_bound_bundle wrappers

Narrow child module for 2 ℤ^d Λ-direct
`partitionFunctionΛ_latticeGraph_*_ratio_bound_bundle` wrappers
extracted from `HighTemperatureBoundsRatioBoundsBound.lean`:

* `partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_bound_bundle`,
* `partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_bound_bundle_ferromagnetic`.

Each result is a thin pass-through of the corresponding ambient
`partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_bundle*`
lemma at `G := IsingModel.latticeGraph d`. The theorem names are
unchanged from the former `HighTemperatureBoundsRatioBoundsBound`
declarations.
-/

namespace IsingModel
namespace Ambient



/-- **ℤ^d Λ Z ratio upper bound bundle**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_bound_bundle
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) ∧
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_bundle
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ ferromagnetic Z ratio upper bound bundle**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_bound_bundle_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) ∧
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_bundle_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ


end Ambient
end IsingModel
