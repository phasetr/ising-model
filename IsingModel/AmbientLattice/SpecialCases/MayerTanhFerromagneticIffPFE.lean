import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerTanhFerromagneticIffPFEIff

/-!
# Mayer ferromagnetic tanh iff wrappers for `polymerFreeEnergy`

Narrow child module for the seven §18.5 along-exhaustion
ferromagnetic tanh iff wrappers for `polymerFreeEnergy`. Each
wrapper is a thin pass-through to the corresponding
`polymerFreeEnergy_Λ_tanh_*_ferro` ambient lemma. Theorem names are
unchanged from the former `MayerTanhFerromagneticIff` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ## Moved: pFE tanh iff (ferro) wrappers

The five `polymerFreeEnergyAlongExhaustion_tanh_*_iff_*_ferro`
wrappers now live in
`IsingModel.AmbientLattice.SpecialCases.MayerTanhFerromagneticIffPFEIff`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from `Legacy.lean`.
-/

/-- **Along-ex: pFE(tanh) < (1+tanh)^|E| - 1** under ε(tanh) > 0
(ferro). -/
theorem
polymerFreeEnergyAlongExhaustion_tanh_lt_pow_sub_one_of_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) <
      (1 + Real.tanh (β * J)) ^
        (inducedGraph G (Λ.volume n)).edgeFinset.card - 1 :=
  polymerFreeEnergy_Λ_tanh_lt_pow_sub_one_of_eps_pos_ferro
    G (Λ.volume n) hβ hJ h_eps_pos

/-- **Along-ex: pFE(tanh) < ε(tanh)** under ε(tanh) > 0 (ferro). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_lt_eps_of_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) <
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_Λ_tanh_lt_eps_of_eps_pos_ferro
    G (Λ.volume n) hβ hJ h_eps_pos

end Ambient
end IsingModel
