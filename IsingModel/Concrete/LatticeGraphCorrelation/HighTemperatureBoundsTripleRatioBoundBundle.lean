import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete §18.3-§18.4 Λ-direct triple-ratio bound-bundle wrappers

Narrow child module for 3 ℤ^d Λ-direct
`partitionFunctionΛ_*_triple_ratio_bound_bundle` wrappers extracted
from `HighTemperatureBoundsTripleRatio.lean`:

* `partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_triple_ratio_bound_bundle`,
* `*_beta_zero` variant,
* `*_ferromagnetic` variant.

Each result is a thin pass-through of the corresponding ambient
`partitionFunctionΛ_high_temp_expansion_h_zero_triple_ratio_bound_bundle*`
lemma at `G := IsingModel.latticeGraph d`. The theorem names are
unchanged from the former `HighTemperatureBoundsTripleRatio`
declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]


/-- **ℤ^d Λ triple (Z + log Z + f) ratio bound bundle at J=0**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_triple_ratio_bound_bundle
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) ∧
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ))
        - Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ))
        ≤ β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card ∧
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
            Λ.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_triple_ratio_bound_bundle
    (IsingModel.latticeGraph d) Λ J β hβJ hne

/-- **ℤ^d Λ triple ratio bound bundle at β=0**. -/
theorem
partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_triple_ratio_bound_bundle_beta_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) ∧
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ))
        - Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ))
        ≤ β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card ∧
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
            Λ.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_triple_ratio_bound_bundle_beta_zero
    (IsingModel.latticeGraph d) Λ J β hβJ hne

/-- **ℤ^d Λ ferromagnetic triple ratio bound bundle at J=0**. -/
theorem
partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_triple_ratio_bound_bundle_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) ∧
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ))
        - Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ))
        ≤ β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card ∧
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
            Λ.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_triple_ratio_bound_bundle_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ hne

end Ambient

end IsingModel
