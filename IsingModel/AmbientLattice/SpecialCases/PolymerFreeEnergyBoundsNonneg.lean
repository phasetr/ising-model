import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsNonnegBase

/-!
# Ambient polymerFreeEnergyAlongExhaustion `≤` upper-bound wrappers

Narrow child module for the two ambient
`polymerFreeEnergyAlongExhaustion_le_*_of_nonneg` upper-bound
wrappers extracted from `PolymerFreeEnergyBounds.lean`:

* `polymerFreeEnergyAlongExhaustion_le_card_log_one_plus_of_nonneg`,
* `polymerFreeEnergyAlongExhaustion_le_card_mul_of_nonneg`.

The corresponding base lower-bound wrapper
(`_nonneg_of_nonneg`) now lives in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsNonnegBase`
and is re-imported through this parent module. Each wrapper is a
thin pass-through of the corresponding Λ-level
`polymerFreeEnergy_Λ_*_of_nonneg` lemma. Theorem names are
unchanged from the former `PolymerFreeEnergyBounds` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-! ## Moved: 1 nonneg_of_nonneg wrapper

The `polymerFreeEnergyAlongExhaustion_nonneg_of_nonneg` wrapper
now lives in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsNonnegBase`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

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
