import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhSharpeningIffEpsPos
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhSharpeningIffLtEps

/-!
# Polymer free-energy tanh sharpening `iff` wrappers along an exhaustion

Characterizes vanishing and strict positivity of the along-exhaustion polymer free energy by
the corresponding property of the cluster-expansion remainder `ε` (GJ §18.5), so a sign
argument can be transported between them. Each passes through to a
`polymerFreeEnergy_Λ_tanh_*` ambient lemma.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

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

end Ambient
end IsingModel
