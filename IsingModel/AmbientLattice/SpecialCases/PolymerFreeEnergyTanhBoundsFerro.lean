import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhBoundsFerroSandwich

/-!
# Ferromagnetic upper bounds on the polymer free energy at a `tanh` activity

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set, and its
Prop-valued hypotheses are exactly `0 ≤ J` and `0 < β`.

Writing `|E|` for the edge count of the stage subgraph, the polymer free energy at the
activity `Real.tanh (β * J)` is at most `|E| * Real.tanh (β * J)`, and at most
`|E| * Real.log 2`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: ferromagnetic polymerFreeEnergy_tanh ≤ |E|·tanh**. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_le_card_mul_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.tanh (β * J) :=
  polymerFreeEnergy_Λ_tanh_le_card_mul_ferromagnetic
    G (Λ.volume n) hJ hβ

/-- **Along-ex: ferromagnetic polymerFreeEnergy_tanh ≤ |E|·log 2**. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_le_card_log_two_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.log 2 :=
  polymerFreeEnergy_Λ_tanh_le_card_log_two_ferro G (Λ.volume n) hJ hβ

end Ambient
end IsingModel
