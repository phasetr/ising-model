import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaPfeSharpening

/-!
# Polymer free-energy `_of_eps_pos` tanh sharpening wrappers along an exhaustion

Narrow child module for the two §18.5 along-exhaustion
`polymerFreeEnergyAlongExhaustion_tanh_*_of_eps_pos` wrappers
extracted from `PolymerFreeEnergyTanhSharpeningIff.lean`:

* `polymerFreeEnergyAlongExhaustion_tanh_lt_eps_of_eps_pos`
* `polymerFreeEnergyAlongExhaustion_tanh_lt_pow_sub_one_of_eps_pos`

Each wrapper is a thin pass-through to the corresponding ambient
`polymerFreeEnergy_Λ_tanh_*_of_eps_pos` lemma. Theorem names are
unchanged from the former `PolymerFreeEnergyTanhSharpening`
declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: pFE(tanh) < ε(tanh)** under ε(tanh) > 0
(`0 ≤ β·J`). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_lt_eps_of_eps_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) <
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_Λ_tanh_lt_eps_of_eps_pos G (Λ.volume n) hβJ h_eps_pos

/-- **Along-ex: pFE(tanh) < (1+tanh)^|E| - 1** under ε(tanh) > 0
(`0 ≤ β·J`). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_lt_pow_sub_one_of_eps_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) <
      (1 + Real.tanh (β * J)) ^
        (inducedGraph G (Λ.volume n)).edgeFinset.card - 1 :=
  polymerFreeEnergy_Λ_tanh_lt_pow_sub_one_of_eps_pos
    G (Λ.volume n) hβJ h_eps_pos

end Ambient
end IsingModel
