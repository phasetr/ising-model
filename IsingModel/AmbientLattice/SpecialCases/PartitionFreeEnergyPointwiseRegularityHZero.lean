import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityHZeroDifferentiableAt

/-!
# Ambient partitionFunctionAlongExhaustion h = 0 pointwise wrappers

Narrow child module for 4 ambient
`partitionFunctionAlongExhaustion_*_h_zero` ContinuousAt /
DifferentiableAt pointwise wrappers extracted from
`PartitionFreeEnergyPointwiseRegularity.lean`:

* `partitionFunctionAlongExhaustion_continuousAt_beta_h_zero`,
* `partitionFunctionAlongExhaustion_continuousAt_J_h_zero`,
* `partitionFunctionAlongExhaustion_differentiableAt_beta_h_zero`,
* `partitionFunctionAlongExhaustion_differentiableAt_J_h_zero`.

Each result is a thin pass-through lifting the corresponding Λ-level
`partitionFunctionΛ_{continuous,differentiable}_{beta,J}_h_zero` lemma
to AlongExhaustion via `.continuousAt` / `.differentiableAt`. The
theorem names are unchanged from the former
`PartitionFreeEnergyPointwiseRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-- **partitionFunctionAlongExhaustion ContinuousAt β at h = 0**. -/
theorem partitionFunctionAlongExhaustion_continuousAt_beta_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    ContinuousAt (fun β' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, 0, β'⟩ n) β :=
  (partitionFunctionΛ_continuous_beta_h_zero G (Λ.volume n) J).continuousAt

/-- **partitionFunctionAlongExhaustion ContinuousAt J at h = 0**. -/
theorem partitionFunctionAlongExhaustion_continuousAt_J_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    ContinuousAt (fun J' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J', 0, β⟩ n) J :=
  (partitionFunctionΛ_continuous_J_h_zero G (Λ.volume n) β).continuousAt

/-! ## Moved: 2 partitionFunction_differentiableAt h = 0 wrappers

The two `DifferentiableAt ℝ` pointwise h = 0 wrappers
(`partitionFunctionAlongExhaustion_differentiableAt_beta_h_zero`,
`partitionFunctionAlongExhaustion_differentiableAt_J_h_zero`) now
live in
`IsingModel.AmbientLattice.SpecialCases.`
`PartitionFreeEnergyPointwiseRegularityHZeroDifferentiableAt`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/


end Ambient
end IsingModel
