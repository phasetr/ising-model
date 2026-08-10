import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaPolymerBounds

/-!
# The `|E| * log 2` upper bound on the polymer free energy

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Writing `|E|` for the edge count of the stage subgraph, the polymer free energy is at most
`|E| * Real.log 2` at an activity `t` with `0 ≤ t` and `t ≤ 1` as the Prop-valued hypotheses,
and at the activity `Real.tanh (β * J)` with `0 ≤ β * J` as the only Prop-valued hypothesis.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: `polymerFreeEnergy ≤ |E|·log 2` for `0 ≤ t ≤ 1`**
(§18.5 along-ex wrap of Step 642). -/
theorem polymerFreeEnergyAlongExhaustion_le_card_log_two_of_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.log 2 :=
  polymerFreeEnergy_Λ_le_card_log_two_of_le_one
    G (Λ.volume n) ht ht1

/-- **Along-ex: `polymerFreeEnergy_tanh ≤ |E|·log 2` under `0 ≤ β·J`**
(§18.5 along-ex wrap of Step 643). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_le_card_log_two
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.log 2 :=
  polymerFreeEnergy_Λ_tanh_le_card_log_two G (Λ.volume n) hβJ

end Ambient
end IsingModel
