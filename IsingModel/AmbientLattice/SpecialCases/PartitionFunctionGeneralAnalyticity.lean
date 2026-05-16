import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PartitionFunctionGeneralAnalyticityAnalyticAt

/-!
# Ambient partition-function joint and general-h analyticity wrappers

This module contains general-graph joint `Continuous` / `Differentiable` APIs
and general-h `AnalyticAt` APIs for per-stage
`partitionFunctionAlongExhaustion`. It is split out of the original ambient
special-cases module so concrete partition-function wrappers can depend on a
narrower child path.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### Along-exhaustion partition-function joint and general-h analyticity -/

/-- **Along-ex: partitionFunction jointly `Continuous` in
`(β, J, h)`**. -/
theorem partitionFunctionAlongExhaustion_continuous_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      partitionFunctionAlongExhaustion G Λ
        ⟨p.2.1, p.2.2, p.1⟩ n) :=
  partitionFunctionΛ_continuous_joint G (Λ.volume n)

/-- **Along-ex: partitionFunction jointly `Differentiable ℝ` in
`(β, J, h)`**. -/
theorem partitionFunctionAlongExhaustion_differentiable_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      partitionFunctionAlongExhaustion G Λ
        ⟨p.2.1, p.2.2, p.1⟩ n) :=
  partitionFunctionΛ_differentiable_joint G (Λ.volume n)

/-! ## Moved: 3 partitionFunction_analyticAt general-h wrappers

The three pointwise `AnalyticAt` wrappers
(`partitionFunctionAlongExhaustion_analyticAt_beta_general_h`,
`partitionFunctionAlongExhaustion_analyticAt_J_general_h`,
`partitionFunctionAlongExhaustion_analyticAt_h`) now live in
`IsingModel.AmbientLattice.SpecialCases.PartitionFunctionGeneralAnalyticityAnalyticAt`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel
