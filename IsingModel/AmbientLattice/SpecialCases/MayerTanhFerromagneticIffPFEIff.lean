import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerTanhFerromagneticIffPFEIffAllPolymers

/-!
# Mayer ferromagnetic tanh iff wrappers for `polymerFreeEnergy` (iff family)

Narrow child module for the five §18.5 along-exhaustion
ferromagnetic tanh iff wrappers for `polymerFreeEnergy`. Each
wrapper is a thin pass-through to the corresponding
`polymerFreeEnergy_Λ_tanh_*_iff_*_ferro` ambient lemma. Theorem
names are unchanged from the former `MayerTanhFerromagneticIffPFE`
declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: pFE(tanh) < ε(tanh) ↔ ε(tanh) > 0** (ferro). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_lt_eps_iff_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) <
        ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
              ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_Λ_tanh_lt_eps_iff_eps_pos_ferro
    G (Λ.volume n) hβ hJ

/-- **Along-ex: pFE(tanh) = 0 ↔ ε(tanh) = 0** (ferro). -/
theorem
polymerFreeEnergyAlongExhaustion_tanh_eq_zero_iff_eps_eq_zero_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) = 0 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 :=
  polymerFreeEnergy_Λ_tanh_eq_zero_iff_eps_eq_zero_ferro
    G (Λ.volume n) hβ hJ

/-- **Along-ex: 0 < pFE(tanh) ↔ 0 < ε(tanh)** (ferro). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_pos_iff_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
          (Real.tanh (β * J)) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_Λ_tanh_pos_iff_eps_pos_ferro G (Λ.volume n) hβ hJ

/-! ## Moved: 2 allPolymers-form ferromagnetic pFE iff wrappers

The two along-ex ferromagnetic `polymerFreeEnergy_*_iff_ferro`
wrappers in the `allPolymers` form
(`polymerFreeEnergyAlongExhaustion_tanh_pos_iff_ferro`,
`polymerFreeEnergyAlongExhaustion_tanh_eq_zero_iff_ferro`) now
live in
`IsingModel.AmbientLattice.SpecialCases.MayerTanhFerromagneticIffPFEIffAllPolymers`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from `Legacy.lean`.
-/

end Ambient
end IsingModel
