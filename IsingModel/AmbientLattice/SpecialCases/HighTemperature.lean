import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureVdSandwichFE
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureTanh

/-!
# High-temperature convergence wrappers along an exhaustion

Narrow child module for the §18.5 high-temperature sandwich, convergence-radius
`HasSum`, polymer-family sandwich, and strict free-energy correction wrappers
along an exhaustion. The theorem names are the same as the former
declarations, but callers can now avoid importing the monolithic special-cases
module.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ## §18.5 cluster-expansion convergence-radius along-exhaustion wraps -/

/-- **Along-exhaustion: high-temperature sandwich for
`polymerFreeEnergy`** (§18.5 along-ex wrap of #1526). -/
theorem polymerFreeEnergyAlongExhaustion_high_temp_sandwich
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ)
    (h_pow : (1 + t) ^
        (inducedGraph G (Λ.volume n)).edgeFinset.card < 2) :
    0 ≤ IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t ∧
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, t ^ P.card ∧
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card - 1 ∧
    (1 + t) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card - 1 < 1 ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t < Real.log 2 :=
  polymerFreeEnergy_Λ_high_temp_sandwich G (Λ.volume n) ht h_pow

/-- **Along-exhaustion: log Taylor expansion for `polymerFreeEnergy`**
(§18.5 along-ex wrap of #1517). -/
theorem polymerFreeEnergyAlongExhaustion_hasSum_via_log_of_pow_lt_two
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ)
    (h_pow : (1 + t) ^
        (inducedGraph G (Λ.volume n)).edgeFinset.card < 2) :
    HasSum (fun k : ℕ =>
        (-1 : ℝ) ^ k *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) ^ (k + 1) /
          (k + 1))
      (IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t) :=
  polymerFreeEnergy_Λ_hasSum_via_log_of_pow_lt_two
    G (Λ.volume n) ht h_pow

/-! ## Moved: 4 tanh sandwich / `HasSum` wrappers

The four along-exhaustion `tanh` wrappers
(`polymerFreeEnergyAlongExhaustion_tanh_high_temp_sandwich`,
`polymerFreeEnergyAlongExhaustion_tanh_hasSum_via_log_of_pow_lt_two`,
`polymerFreeEnergyAlongExhaustion_tanh_high_temp_sandwich_ferromagnetic`,
`polymerFreeEnergyAlongExhaustion_tanh_hasSum_via_log_of_pow_lt_two_ferromagnetic`)
now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureTanh`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-! ## Moved: 4 vdPolymerFamilies_sum sandwich + 2 strict freeEnergy wrappers

The four `vdPolymerFamilies_sumAlongExhaustion_sandwich*` wrappers
and the two `freeEnergyAlongExhaustion_lt_log_two_plus_high_temp_correction*`
strict free-energy bounds now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureVdSandwichFE`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel
