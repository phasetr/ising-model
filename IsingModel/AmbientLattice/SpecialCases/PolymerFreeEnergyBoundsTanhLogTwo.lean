import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaPolymerBounds

/-!
# Ambient polymerFreeEnergyAlongExhaustion `≤ |E|·log 2` wrappers

Narrow child module for the two ambient
`polymerFreeEnergyAlongExhaustion_*_log_two_*` bound wrappers
extracted from `PolymerFreeEnergyBoundsTanh.lean`:

* `polymerFreeEnergyAlongExhaustion_le_card_log_two_of_le_one`
* `polymerFreeEnergyAlongExhaustion_tanh_le_card_log_two`

Each result is a thin pass-through of the corresponding Λ-level
`polymerFreeEnergy_Λ_*` lemma giving the `≤ |E|·log 2` upper bound
in either the general `0 ≤ t ≤ 1` slice or the `tanh(β·J)` form
under `0 ≤ β·J`. Theorem names are unchanged from the former
`PolymerFreeEnergyBounds` declarations.
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
