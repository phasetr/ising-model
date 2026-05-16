import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Polymer free-energy ↔ ε(t) equivalence wrappers along an exhaustion

Narrow child module for the four §18.5 ambient alongExhaustion
`polymerFreeEnergy_*_iff_eps_*` and `_lt_*_of_eps_pos` wrappers
extracted from `PolymerFreeEnergyEpsilonSharpening.lean`:

* `polymerFreeEnergyAlongExhaustion_eq_zero_iff_eps_eq_zero`
* `polymerFreeEnergyAlongExhaustion_pos_iff_eps_pos`
* `polymerFreeEnergyAlongExhaustion_lt_eps_iff_eps_pos`
* `polymerFreeEnergyAlongExhaustion_lt_pow_sub_one_of_eps_pos`

Each wrapper is a thin pass-through to the corresponding ambient
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

/-- **Along-ex: pFE(t) < (1+t)^|E| - 1** under `0 ≤ t` and ε(t) > 0. -/
theorem polymerFreeEnergyAlongExhaustion_lt_pow_sub_one_of_eps_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t <
      (1 + t) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card - 1 :=
  polymerFreeEnergy_Λ_lt_pow_sub_one_of_eps_pos
    G (Λ.volume n) ht h_eps_pos

end Ambient
end IsingModel
