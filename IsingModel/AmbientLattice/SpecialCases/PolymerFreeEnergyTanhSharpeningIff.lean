import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhSharpeningIffEpsPos

/-!
# Polymer free-energy tanh sharpening iff / eps_pos wrappers along an exhaustion

Narrow child module for the five §18.5 along-exhaustion
`polymerFreeEnergyAlongExhaustion_tanh_*` iff / `_of_eps_pos`
wrappers. Each wrapper is a thin pass-through to the corresponding
`polymerFreeEnergy_Λ_tanh_*` ambient lemma. Theorem names are
unchanged from the former `PolymerFreeEnergyTanhSharpening`
declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: pFE(tanh) < ε(tanh) ↔ 0 < ε(tanh)** under
`0 ≤ β·J`. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_lt_eps_iff_eps_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) <
        ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
              ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_Λ_tanh_lt_eps_iff_eps_pos G (Λ.volume n) hβJ

/-- **Along-ex: pFE(tanh) = 0 ↔ ε(tanh) = 0** under `0 ≤ β·J`. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_eq_zero_iff_eps_eq_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) = 0 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 :=
  polymerFreeEnergy_Λ_tanh_eq_zero_iff_eps_eq_zero G (Λ.volume n) hβJ

/-- **Along-ex: 0 < pFE(tanh) ↔ 0 < ε(tanh)** under `0 ≤ β·J`. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_pos_iff_eps_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
          (Real.tanh (β * J)) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_Λ_tanh_pos_iff_eps_pos G (Λ.volume n) hβJ

/-! ## Moved: 2 `_of_eps_pos` tanh sharpening wrappers

The two along-ex `polymerFreeEnergyAlongExhaustion_tanh_*_of_eps_pos`
wrappers (`_lt_eps_of_eps_pos`, `_lt_pow_sub_one_of_eps_pos`) now
live in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhSharpeningIffEpsPos`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from `Legacy.lean`.
-/

end Ambient
end IsingModel
