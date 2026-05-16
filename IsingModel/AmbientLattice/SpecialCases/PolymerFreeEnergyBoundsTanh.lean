import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsTanhLogTwo

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

/-! ## Moved: 2 `≤ |E|·log 2` wrappers

The two `polymerFreeEnergyAlongExhaustion_*_log_two_*` upper bound
wrappers (`_le_card_log_two_of_le_one`, `_tanh_le_card_log_two`)
now live in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsTanhLogTwo`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella.
-/

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
