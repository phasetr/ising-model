import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyHighTemperatureBoundsTanh

/-!
# Polymer free-energy high-temperature bound wrappers along an exhaustion

Narrow child module for the §18.5 `vdPolymerFamilies_sum` sandwich,
`MonotoneOn`, and `ε(t)` bound wrappers along an exhaustion. The
theorem names are the same as the former declarations, but
callers can now avoid importing the monolithic special-cases
module.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ## §18.5 polymer free-energy high-temperature bounds along-exhaustion wraps -/

/-- **Along-ex: vdSum sandwich for `t ≥ 0`**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_sandwich_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card :=
  vdPolymerFamilies_sum_Λ_sandwich_of_nonneg G (Λ.volume n) ht

/-- **Along-ex: vdSum is `MonotoneOn (Set.Ici 0)`**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_monotoneOn_Ici_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    MonotoneOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ici 0) :=
  vdPolymerFamilies_sum_Λ_monotoneOn_Ici_zero G (Λ.volume n)

/-- **Along-ex: ε(t) ≤ (1+t)^|E| - 1** for `0 ≤ t`. -/
theorem vdPolymerFamilies_sumAlongExhaustion_minus_one_le_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card - 1 :=
  vdPolymerFamilies_sum_Λ_minus_one_le_of_nonneg G (Λ.volume n) ht

/-! ## Moved: 3 polymerFreeEnergy_tanh high-temperature bound wrappers

The three §18.5 `polymerFreeEnergy_tanh_*` wrappers
(`polymerFreeEnergyAlongExhaustion_tanh_le_eps_of_betaJ_nonneg`,
`polymerFreeEnergyAlongExhaustion_tanh_le_pow_sub_one_of_betaJ_nonneg`,
`polymerFreeEnergyAlongExhaustion_tanh_lt_log_two_of_pow_lt_two`)
now live in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyHighTemperatureBoundsTanh`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel
