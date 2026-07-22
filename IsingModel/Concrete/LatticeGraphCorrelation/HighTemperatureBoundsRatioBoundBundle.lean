import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d Λ-direct log Z ratio_bound_bundle wrappers at h = 0

Narrow child module for the concrete (`latticeGraph d`) Λ-direct
`log_partitionFunction` ratio_bound_bundle wrappers at h = 0 (with
ferromagnetic variant) extracted from
`HighTemperatureBoundsRatioLogFe.lean`:

* `log_partitionFunctionΛ_*_ratio_bound_bundle` (direct + `_ferromagnetic`).

The theorem names are unchanged from the former
`HighTemperatureBoundsRatioLogFe` declarations. The two companion
`freeEnergyΛ_latticeGraph_*_ratio_bound_bundle` wrappers were removed as
unused conjunction bundles.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]


/-- **ℤ^d Λ log Z ratio bound bundle**. -/
theorem log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_bound_bundle
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ))
        - Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ))
        ≤ β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card ∧
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ))
        - Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ))
        ≤ β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_bundle
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ ferromagnetic log Z ratio bound bundle**. -/
theorem
log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_bound_bundle_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ))
        - Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ))
        ≤ β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card ∧
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ))
        - Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ))
        ≤ β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_bundle_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ

end Ambient
end IsingModel
