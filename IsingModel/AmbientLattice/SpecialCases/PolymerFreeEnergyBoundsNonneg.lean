import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient polymerFreeEnergyAlongExhaustion nonneg-conditioned bound wrappers

Narrow child module for 3 ambient
`polymerFreeEnergyAlongExhaustion_*_of_nonneg` bound wrappers extracted
from `PolymerFreeEnergyBounds.lean`:

* `polymerFreeEnergyAlongExhaustion_nonneg_of_nonneg`,
* `polymerFreeEnergyAlongExhaustion_le_card_log_one_plus_of_nonneg`,
* `polymerFreeEnergyAlongExhaustion_le_card_mul_of_nonneg`.

Each result is a thin pass-through of the corresponding Λ-level
`polymerFreeEnergy_Λ_*_of_nonneg` lemma. The theorem names are
unchanged from the former `PolymerFreeEnergyBounds` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-- **Along-ex: `polymerFreeEnergy ≥ 0` under `t ≥ 0`** (§18.5
along-ex wrap). -/
theorem polymerFreeEnergyAlongExhaustion_nonneg_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t :=
  polymerFreeEnergy_Λ_nonneg_of_nonneg G (Λ.volume n) ht

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
