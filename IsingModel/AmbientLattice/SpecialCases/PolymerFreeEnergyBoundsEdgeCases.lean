import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaPolymerBounds

/-!
# Vanishing of the polymer free energy on a degenerate stage subgraph

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

When the polymer set of the stage subgraph equals `∅`, and likewise when its edge finset
equals `∅`, the polymer free energy of that subgraph is `0` at every activity `t : ℝ`: the
activity is universally quantified over all of `ℝ`, with no sign or size restriction, so the
function vanishes identically. The stated emptiness equation is the only Prop-valued
hypothesis of each statement.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: `polymerFreeEnergy = 0` for empty-polymer induced
graphs** (§18.5 along-ex wrap of Step 621). -/
theorem polymerFreeEnergyAlongExhaustion_eq_zero_of_no_polymers
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ)
    (h_no : IsingModel.allPolymers
      (inducedGraph G (Λ.volume n)) = ∅) (t : ℝ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t = 0 :=
  polymerFreeEnergy_Λ_eq_zero_of_no_polymers G (Λ.volume n) h_no t

/-- **Along-ex: `polymerFreeEnergy = 0` for edgeless induced
graphs** (§18.5 along-ex wrap of Step 623). -/
theorem
polymerFreeEnergyAlongExhaustion_eq_zero_of_edgeFinset_empty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ)
    (h_empty : (inducedGraph G (Λ.volume n)).edgeFinset = ∅)
    (t : ℝ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t = 0 :=
  polymerFreeEnergy_Λ_eq_zero_of_edgeFinset_empty
    G (Λ.volume n) h_empty t

end Ambient
end IsingModel
