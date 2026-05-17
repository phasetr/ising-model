import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PartitionFunctionGeneralAnalyticityAnalyticAtH

/-!
# Ambient partition-function pointwise `AnalyticAt` β/J general-h wrappers

Narrow child module for the two ambient
`partitionFunctionAlongExhaustion_analyticAt_*_general_h` pointwise
analyticity wrappers extracted from
`PartitionFunctionGeneralAnalyticity.lean`:

* `partitionFunctionAlongExhaustion_analyticAt_beta_general_h`
* `partitionFunctionAlongExhaustion_analyticAt_J_general_h`

The corresponding `h`-direction wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.PartitionFunctionGeneralAnalyticityAnalyticAtH`
and is re-imported through this parent module. Each wrapper is a
thin pass-through to the corresponding Λ-level
`partitionFunctionΛ_analyticAt_*` lemma. Theorem names are
unchanged from the former `PartitionFunctionGeneralAnalyticity`
declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: partitionFunction `AnalyticAt ℝ` in `β` at general
`h`**. -/
theorem partitionFunctionAlongExhaustion_analyticAt_beta_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h, β'⟩ n) β :=
  partitionFunctionΛ_analyticAt_beta_general_h G (Λ.volume n) J h β

/-- **Along-ex: partitionFunction `AnalyticAt ℝ` in `J` at general
`h`**. -/
theorem partitionFunctionAlongExhaustion_analyticAt_J_general_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β h J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J', h, β⟩ n) J :=
  partitionFunctionΛ_analyticAt_J_general_h G (Λ.volume n) β h J

/-! ## Moved: 1 AnalyticAt h wrapper

The `partitionFunctionAlongExhaustion_analyticAt_h` h-direction
wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.PartitionFunctionGeneralAnalyticityAnalyticAtH`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel
