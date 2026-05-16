import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyEpsilonSharpeningPFE

/-!
# Polymer free-energy epsilon-sum basic wrappers along an exhaustion

Narrow child module for along-exhaustion `ε(t)` (`vdPolymerFamilies_sum`
minus one) nonnegativity and zero-power identities. This keeps callers
that only need these forwarders out of the monolithic legacy
special-cases module.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 epsilon(t) nonneg + non-tanh polymerFreeEnergy sharpening
along-ex wraps -/

/-- **Along-ex: 0 ≤ ε(t)** for `0 ≤ t`. -/
theorem vdPolymerFamilies_sumAlongExhaustion_minus_one_nonneg_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card :=
  vdPolymerFamilies_sum_Λ_minus_one_nonneg_of_nonneg G (Λ.volume n) ht

/-- **Along-ex: ε(0)^k = 0** for `k ≥ 1`. -/
theorem vdPolymerFamilies_sumAlongExhaustion_minus_one_pow_at_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, (0 : ℝ) ^ P.card) ^ k = 0 :=
  vdPolymerFamilies_sum_Λ_minus_one_pow_at_zero G (Λ.volume n) hk

/-! ## Moved: 4 polymerFreeEnergy ↔ ε equivalence wrappers

The four §18.5 `polymerFreeEnergy_*_iff_eps_*` and
`_lt_*_of_eps_pos` wrappers
(`polymerFreeEnergyAlongExhaustion_eq_zero_iff_eps_eq_zero`,
`polymerFreeEnergyAlongExhaustion_pos_iff_eps_pos`,
`polymerFreeEnergyAlongExhaustion_lt_eps_iff_eps_pos`,
`polymerFreeEnergyAlongExhaustion_lt_pow_sub_one_of_eps_pos`) now
live in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyEpsilonSharpeningPFE`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from `Legacy.lean`.
-/

end Ambient
end IsingModel
