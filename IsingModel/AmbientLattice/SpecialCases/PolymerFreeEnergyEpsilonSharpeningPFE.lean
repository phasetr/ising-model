import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyEpsilonSharpeningPFELtPow

/-!
# Polymer free-energy ↔ ε(t) equivalence iff wrappers along an exhaustion

Narrow child module for the three §18.5 ambient alongExhaustion
`polymerFreeEnergyAlongExhaustion_*_iff_eps_*` equivalence
wrappers extracted from `PolymerFreeEnergyEpsilonSharpening.lean`:

* `polymerFreeEnergyAlongExhaustion_eq_zero_iff_eps_eq_zero`
* `polymerFreeEnergyAlongExhaustion_pos_iff_eps_pos`
* `polymerFreeEnergyAlongExhaustion_lt_eps_iff_eps_pos`

The corresponding strict-inequality
`_lt_pow_sub_one_of_eps_pos` wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyEpsilonSharpeningPFELtPow`
and is re-imported through this parent module. Each remaining
wrapper is a thin pass-through to the corresponding ambient
`polymerFreeEnergy_Λ_*` lemma. Theorem names are unchanged from
the former `PolymerFreeEnergyEpsilonSharpening` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: pFE(t) = 0 ↔ ε(t) = 0** under `0 ≤ t`. -/
theorem polymerFreeEnergyAlongExhaustion_eq_zero_iff_eps_eq_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t = 0 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) = 0 :=
  polymerFreeEnergy_Λ_eq_zero_iff_eps_eq_zero G (Λ.volume n) ht

/-- **Along-ex: 0 < pFE(t) ↔ 0 < ε(t)** under `0 ≤ t`. -/
theorem polymerFreeEnergyAlongExhaustion_pos_iff_eps_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card :=
  polymerFreeEnergy_Λ_pos_iff_eps_pos G (Λ.volume n) ht

/-- **Along-ex: pFE(t) < ε(t) ↔ 0 < ε(t)** under `0 ≤ t`. -/
theorem polymerFreeEnergyAlongExhaustion_lt_eps_iff_eps_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t <
        ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card :=
  polymerFreeEnergy_Λ_lt_eps_iff_eps_pos G (Λ.volume n) ht

/-! ## Moved: 1 lt_pow_sub_one_of_eps_pos wrapper

The `polymerFreeEnergyAlongExhaustion_lt_pow_sub_one_of_eps_pos`
wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyEpsilonSharpeningPFELtPow`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel
