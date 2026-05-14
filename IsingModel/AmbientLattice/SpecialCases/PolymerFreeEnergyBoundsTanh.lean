import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient polymerFreeEnergyAlongExhaustion tanh-form bound wrappers

Narrow child module for 4 ambient
`polymerFreeEnergyAlongExhaustion_*` tanh / log_two bound wrappers
extracted from `PolymerFreeEnergyBounds.lean`:

* `polymerFreeEnergyAlongExhaustion_tanh_sandwich`,
* `polymerFreeEnergyAlongExhaustion_le_card_log_two_of_le_one`,
* `polymerFreeEnergyAlongExhaustion_tanh_le_card_log_two`,
* `polymerFreeEnergyAlongExhaustion_tanh_double_bound`.

Each result is a thin pass-through of the corresponding Λ-level
`polymerFreeEnergy_Λ_*` lemma. The theorem names are unchanged from
the former `PolymerFreeEnergyBounds` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-- **Along-ex: `polymerFreeEnergy` tanh-form sandwich** (§18.5
along-ex wrap of Step 632). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_sandwich
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    0 ≤ IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.log (1 + Real.tanh (β * J)) :=
  polymerFreeEnergy_Λ_tanh_sandwich G (Λ.volume n) hβJ

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

/-- **Along-ex: `polymerFreeEnergy_tanh` double bound** (§18.5
along-ex wrap of Step 645). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_double_bound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.tanh (β * J) ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.log 2 :=
  polymerFreeEnergy_Λ_tanh_double_bound G (Λ.volume n) hβJ

end Ambient
end IsingModel
