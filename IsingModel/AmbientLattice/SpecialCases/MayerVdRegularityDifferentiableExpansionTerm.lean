import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMayer

/-!
# Mayer `mayerExpansionTerm` Differentiable wrapper along an exhaustion

Narrow child module for the along-exhaustion
`mayerExpansionTermAlongExhaustion_differentiable` wrapper
extracted from `MayerVdRegularityDifferentiable.lean`. The wrapper
is a thin pass-through to `mayerExpansionTerm_Λ_differentiable`.
The theorem name is unchanged from the former
`MayerVdRegularity` declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: `mayerExpansionTerm` is `Differentiable ℝ`**. -/
theorem mayerExpansionTermAlongExhaustion_differentiable
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (n : ℕ) :
    Differentiable ℝ (fun t : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k t) :=
  mayerExpansionTerm_Λ_differentiable G (Λ.volume n) k

end Ambient
end IsingModel
