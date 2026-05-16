import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsRegularity
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsNonneg
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsTanh
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsEdgeCases

/-!
# Polymer free-energy bound wrappers along an exhaustion

Narrow child module for along-exhaustion `polymerFreeEnergy` regularity,
bounds, comparison, and edge-case wrappers. This keeps callers that only need
these forwarders out of the monolithic legacy special-cases module.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ## Moved: polymerFreeEnergyAlongExhaustion regularity wrappers

The four `polymerFreeEnergyAlongExhaustion_*` regularity wrappers
(`continuousAt`, `differentiableAt`, `continuousOn_Ici_zero`,
`differentiableOn_Ici_zero`) now live in
`PolymerFreeEnergyBoundsRegularity.lean`. They are re-imported here
so downstream consumers continue to see the symbols. -/



/-! ## Moved: polymerFreeEnergyAlongExhaustion `_of_nonneg` bound wrappers

The three `polymerFreeEnergyAlongExhaustion_*_of_nonneg` bound wrappers
(`nonneg`, `le_card_log_one_plus`, `le_card_mul`) now live in
`PolymerFreeEnergyBoundsNonneg.lean`. They are re-imported here so
downstream consumers continue to see the symbols. -/



/-- **Along-ex: `polymerFreeEnergy` is `MonotoneOn (Set.Ici 0)`**
(§18.5 along-ex wrap). -/
theorem polymerFreeEnergyAlongExhaustion_monotoneOn_Ici_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    MonotoneOn (fun t : ℝ =>
        IsingModel.polymerFreeEnergy
          (inducedGraph G (Λ.volume n)) t) (Set.Ici 0) :=
  polymerFreeEnergy_Λ_monotoneOn_Ici_zero G (Λ.volume n)

/-! ## Moved: 2 `polymerFreeEnergy_eq_zero_of_*` edge-case wrappers

The two §18.5 along-ex boundary-case vanishing wrappers
(`polymerFreeEnergyAlongExhaustion_eq_zero_of_no_polymers`,
`polymerFreeEnergyAlongExhaustion_eq_zero_of_edgeFinset_empty`) now
live in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsEdgeCases`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from `Legacy.lean`.
-/

/-- **Along-ex: `polymerFreeEnergy` preserves order on `[0, ∞)`**
(§18.5 along-ex wrap of Step 649). -/
theorem polymerFreeEnergyAlongExhaustion_le_of_le_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t ≤ s) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) s :=
  polymerFreeEnergy_Λ_le_of_le_of_nonneg
    G (Λ.volume n) ht hs hts

/-- **Along-ex: `polymerFreeEnergy` strict-form order preservation**
(§18.5 along-ex wrap of Step 650). -/
theorem polymerFreeEnergyAlongExhaustion_le_of_le_strict_form
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) s :=
  polymerFreeEnergy_Λ_le_of_le_strict_form
    G (Λ.volume n) ht hts

/-! ## Moved: polymerFreeEnergyAlongExhaustion tanh bound wrappers

The four `polymerFreeEnergyAlongExhaustion_*` tanh / log_two bound
wrappers (`tanh_sandwich`, `le_card_log_two_of_le_one`,
`tanh_le_card_log_two`, `tanh_double_bound`) now live in
`PolymerFreeEnergyBoundsTanh.lean`. They are re-imported here so
downstream consumers continue to see the symbols. -/



end Ambient
end IsingModel
