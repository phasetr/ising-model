import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureTanhFerro

/-!
# High-temperature tanh sandwich / `HasSum` wrappers along an exhaustion

Narrow child module for the four §18.5 along-exhaustion
high-temperature `tanh` wrappers extracted from
`HighTemperature.lean`:

* `polymerFreeEnergyAlongExhaustion_tanh_high_temp_sandwich`
* `polymerFreeEnergyAlongExhaustion_tanh_hasSum_via_log_of_pow_lt_two`
* `polymerFreeEnergyAlongExhaustion_tanh_high_temp_sandwich_ferromagnetic`
* `polymerFreeEnergyAlongExhaustion_tanh_hasSum_via_log_of_pow_lt_two_ferromagnetic`

Each wrapper is a thin pass-through to the corresponding
`polymerFreeEnergy_Λ_tanh_*` ambient lemma. Theorem names are
unchanged from the former `HighTemperature` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-exhaustion: high-temperature sandwich for
`polymerFreeEnergy` (tanh form)** (§18.5 along-ex wrap of the tanh
sandwich). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_high_temp_sandwich
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G (Λ.volume n)).edgeFinset.card < 2) :
    0 ≤ IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ∧
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ≤
      (1 + Real.tanh (β * J)) ^
        (inducedGraph G (Λ.volume n)).edgeFinset.card - 1 ∧
    (1 + Real.tanh (β * J)) ^
        (inducedGraph G (Λ.volume n)).edgeFinset.card - 1 < 1 ∧
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) < Real.log 2 :=
  polymerFreeEnergy_Λ_tanh_high_temp_sandwich G (Λ.volume n) hβJ h_pow

/-- **Along-exhaustion: log Taylor expansion for `polymerFreeEnergy`
(tanh form)** (§18.5 along-ex wrap). -/
theorem
polymerFreeEnergyAlongExhaustion_tanh_hasSum_via_log_of_pow_lt_two
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G (Λ.volume n)).edgeFinset.card < 2) :
    HasSum (fun k : ℕ =>
        (-1 : ℝ) ^ k *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ^ (k + 1) /
          (k + 1))
      (IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J))) :=
  polymerFreeEnergy_Λ_tanh_hasSum_via_log_of_pow_lt_two
    G (Λ.volume n) hβJ h_pow

/-! ## Moved: 2 ferromagnetic tanh sandwich / `HasSum` wrappers

The two §18.5 along-ex ferromagnetic tanh wrappers
(`polymerFreeEnergyAlongExhaustion_tanh_high_temp_sandwich_ferromagnetic`,
`polymerFreeEnergyAlongExhaustion_tanh_hasSum_via_log_of_pow_lt_two_ferromagnetic`)
now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureTanhFerro`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella.
-/

end Ambient
end IsingModel
