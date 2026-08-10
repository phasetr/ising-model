import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMayerPfeEdgeBounds

/-!
# A ferromagnetic sandwich for the polymer free energy at a `tanh` activity

Stage-`n` statement for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. It takes `DecidableEq V` and
the stagewise `Fintype` instance on that subgraph's edge set, and its Prop-valued hypotheses
are exactly `0 ≤ J` and `0 < β`.

Writing `|E|` for the edge count of the stage subgraph, the polymer free energy at the
activity `Real.tanh (β * J)` lies between `0` and
`|E| * Real.log (1 + Real.tanh (β * J))`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: ferromagnetic polymerFreeEnergy_tanh sandwich**. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_sandwich_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    0 ≤ IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
          (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.log (1 + Real.tanh (β * J)) :=
  polymerFreeEnergy_Λ_tanh_sandwich_ferromagnetic
    G (Λ.volume n) hJ hβ

end Ambient
end IsingModel
