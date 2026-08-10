import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaPolymerBounds

/-!
# Monotonicity of the polymer free energy on the nonnegative activity ray

Stage-`n` statement for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. It takes `DecidableEq V` and
the stagewise `Fintype` instance on that subgraph's edge set, and carries no Prop-valued
hypothesis.

As a function of the activity, the polymer free energy of the stage subgraph is monotone on
`Set.Ici 0`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: `polymerFreeEnergy` is `MonotoneOn (Set.Ici 0)`**
(§18.5 along-ex wrap). -/
theorem polymerFreeEnergyAlongExhaustion_monotoneOn_Ici_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    MonotoneOn (fun t : ℝ =>
        IsingModel.polymerFreeEnergy
          (inducedGraph G (Λ.volume n)) t) (Set.Ici 0) :=
  polymerFreeEnergy_Λ_monotoneOn_Ici_zero G (Λ.volume n)

end Ambient
end IsingModel
