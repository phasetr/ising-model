import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityPartitionGeneralHDifferentiableAt

/-!
# Ambient partitionFunctionAlongExhaustion general-h pointwise wrappers

Narrow child module for 4 ambient
`partitionFunctionAlongExhaustion_*_general_h` ContinuousAt /
DifferentiableAt pointwise wrappers extracted from
`PartitionFreeEnergyPointwiseRegularity.lean`:

* `partitionFunctionAlongExhaustion_continuousAt_beta_general_h`,
* `partitionFunctionAlongExhaustion_continuousAt_J_general_h`,
* `partitionFunctionAlongExhaustion_differentiableAt_beta_general_h`,
* `partitionFunctionAlongExhaustion_differentiableAt_J_general_h`.

Each result is a thin pass-through lifting the corresponding Λ-level
`partitionFunctionΛ_{continuous,differentiable}_{beta,J}_general_h`
lemma to AlongExhaustion via `.continuousAt` / `.differentiableAt`.
The theorem names are unchanged from the former
`PartitionFreeEnergyPointwiseRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-- **partitionFunctionAlongExhaustion ContinuousAt β at general h**. -/
theorem partitionFunctionAlongExhaustion_continuousAt_beta_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun β' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h, β'⟩ n) β :=
  (partitionFunctionΛ_continuous_beta_general_h G (Λ.volume n) J h).continuousAt

/-- **partitionFunctionAlongExhaustion ContinuousAt J at general h**. -/
theorem partitionFunctionAlongExhaustion_continuousAt_J_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun J' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J', h, β⟩ n) J :=
  (partitionFunctionΛ_continuous_J_general_h G (Λ.volume n) β h).continuousAt

/-! ## Moved: 2 partitionFunction_differentiableAt general-h wrappers

The two `DifferentiableAt ℝ` pointwise general-h wrappers
(`partitionFunctionAlongExhaustion_differentiableAt_beta_general_h`,
`partitionFunctionAlongExhaustion_differentiableAt_J_general_h`)
now live in
`IsingModel.AmbientLattice.SpecialCases.`
`PartitionFreeEnergyPointwiseRegularityPartitionGeneralHDifferentiableAt`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from `Legacy.lean`.
-/

end Ambient
end IsingModel
