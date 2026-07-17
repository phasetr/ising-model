import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMayerRecurrenceEpsilon

/-!
# `allPolymers = ∅` on edgeless induced graphs along an exhaustion

Narrow child module for the §18.5 along-exhaustion
`allPolymersAlongExhaustion_eq_empty_of_edgeFinset_empty` wrapper
extracted from `MayerEpsilonInfrastructure.lean`. The wrapper is a
thin pass-through to `allPolymers_Λ_eq_empty_of_edgeFinset_empty`.
The theorem name is unchanged from the former
`MayerEpsilonInfrastructure` declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: allPolymers = ∅ on edgeless induced graphs**. -/
theorem allPolymersAlongExhaustion_eq_empty_of_edgeFinset_empty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_empty : (inducedGraph G (Λ.volume n)).edgeFinset = ∅) :
    IsingModel.allPolymers (inducedGraph G (Λ.volume n)) = ∅ :=
  allPolymers_Λ_eq_empty_of_edgeFinset_empty G (Λ.volume n) h_empty

end Ambient
end IsingModel
