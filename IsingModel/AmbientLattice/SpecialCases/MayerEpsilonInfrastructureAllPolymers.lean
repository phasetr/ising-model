import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMayerRecurrenceEpsilon

/-!
# The polymer universe of an edgeless stage subgraph, along an exhaustion

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

When the stage subgraph has an empty edge finset, its polymer universe
`IsingModel.allPolymers` is the empty finset.
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
