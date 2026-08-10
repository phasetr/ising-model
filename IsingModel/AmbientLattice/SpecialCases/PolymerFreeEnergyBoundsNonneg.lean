import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsNonnegBase

/-!
# Edge-count upper bounds on the polymer free energy at a nonnegative activity

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set, and has
`0 ≤ t` as its only Prop-valued hypothesis.

Writing `|E|` for the edge count of the stage subgraph, the polymer free energy at activity
`t` is at most `|E| * Real.log (1 + t)` and at most `|E| * t`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: `polymerFreeEnergy ≤ |E| · log(1 + t)` under
`t ≥ 0`** (§18.5 along-ex wrap). -/
theorem
polymerFreeEnergyAlongExhaustion_le_card_log_one_plus_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.log (1 + t) :=
  polymerFreeEnergy_Λ_le_card_log_one_plus_of_nonneg
    G (Λ.volume n) ht

/-- **Along-ex: `polymerFreeEnergy ≤ |E| · t` under `t ≥ 0`**
(§18.5 along-ex wrap). -/
theorem polymerFreeEnergyAlongExhaustion_le_card_mul_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card * t :=
  polymerFreeEnergy_Λ_le_card_mul_of_nonneg G (Λ.volume n) ht

end Ambient
end IsingModel
