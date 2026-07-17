import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharper
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviation
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBounds
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBoundsBoundOnly
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeFreeEnergyBoundOnly
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeLogBoundOnlySingletons

/-!
# Ambient alongExhaustion triple-ratio bound_bundle wrappers at h = 0

Narrow child module for three §18.3-§18.4 ambient alongExhaustion
`triple_ratio_bound_bundle` wrappers extracted from
`HighTemperatureBoundsTripleRatio.lean`. Each wrapper packages the
`Z`, `log Z`, and `freeEnergy` ratio bounds in a single
conjunctive statement. Theorem names are unchanged from the former
`HighTemperatureBoundsTripleRatio` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex triple (Z + log Z + f) ratio bound bundle at J=0, stage `n`**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_triple_ratio_bound_bundle
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
        ≤ Real.exp (β * J *
            (inducedGraph G (Λ.volume n)).edgeFinset.card) ∧
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨0, 0, β⟩ : IsingParams ℝ) n)
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card ∧
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  ⟨partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound
     G Λ J β hβJ n,
   log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound
     G Λ J β hβJ n,
   freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound G Λ J β hβJ n hne⟩

/-- **Along-ex triple ratio bound bundle at β=0, stage `n`**. -/
theorem
partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_triple_ratio_bound_bundle_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
        ≤ Real.exp (β * J *
            (inducedGraph G (Λ.volume n)).edgeFinset.card) ∧
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ) n)
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card ∧
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  ⟨partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_beta_zero
     G Λ J β hβJ n,
   log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_beta_zero
     G Λ J β hβJ n,
   freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound_beta_zero
     G Λ J β hβJ n hne⟩

/-! ## Moved: 1 ferromagnetic triple ratio bound_bundle wrapper

The ferromagnetic `triple_ratio_bound_bundle_ferromagnetic` Z
wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsTripleRatioBoundBundleFerro`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient

end IsingModel
