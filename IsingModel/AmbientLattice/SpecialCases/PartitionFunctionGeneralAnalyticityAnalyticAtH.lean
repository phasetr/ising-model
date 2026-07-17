import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaSection186

/-!
# Ambient partition-function `AnalyticAt` h-direction wrapper

Narrow child module for the ambient
`partitionFunctionAlongExhaustion_analyticAt_h` h-direction
pointwise analyticity wrapper extracted from
`PartitionFunctionGeneralAnalyticityAnalyticAt.lean`. The wrapper
is a thin pass-through to the Λ-level
`partitionFunctionΛ_analyticAt_h` lemma. The theorem name is
unchanged from the former `PartitionFunctionGeneralAnalyticity`
declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

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
