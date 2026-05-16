import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient partition-function pointwise `AnalyticAt` general-h wrappers

Narrow child module for the three ambient
`partitionFunctionAlongExhaustion_analyticAt_*` general-h pointwise
analyticity wrappers extracted from
`PartitionFunctionGeneralAnalyticity.lean`:

* `partitionFunctionAlongExhaustion_analyticAt_beta_general_h`
* `partitionFunctionAlongExhaustion_analyticAt_J_general_h`
* `partitionFunctionAlongExhaustion_analyticAt_h`

Each wrapper is a thin pass-through to the corresponding Λ-level
`partitionFunctionΛ_analyticAt_*` lemma. Theorem names are unchanged
from the former `PartitionFunctionGeneralAnalyticity` declarations.
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

/-- **Along-ex: partitionFunction `AnalyticAt ℝ` in `h`**. -/
theorem partitionFunctionAlongExhaustion_analyticAt_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β h : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun h' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h', β⟩ n) h :=
  partitionFunctionΛ_analyticAt_h G (Λ.volume n) J β h

end Ambient
end IsingModel
