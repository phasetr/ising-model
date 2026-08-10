import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhSharpeningIff
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhSharpeningStrictMono

/-!
# Strict increase of the polymer free energy at a `tanh` activity

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

With the polymer set of the stage subgraph nonempty, the polymer free energy at the activity
`Real.tanh (β * J)` increases strictly when the inverse temperature moves from `β₁` to `β₂`
with the coupling fixed, and when the coupling moves from `J₁` to `J₂` with the inverse
temperature fixed. The Prop-valued hypotheses are exactly that nonemptiness together with
`0 ≤ β₁`, `0 < J` and `β₁ < β₂` in the first statement, and that nonemptiness together with
`0 ≤ J₁`, `0 < β` and `J₁ < J₂` in the second.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: pFE(tanh(β₁·J)) < pFE(tanh(β₂·J))** under `J > 0`,
`0 ≤ β₁ < β₂`, polymers nonempty. -/
theorem
polymerFreeEnergyAlongExhaustion_tanh_lt_of_lt_in_beta_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty)
    {β₁ β₂ J : ℝ} (hβ₁ : 0 ≤ β₁) (hJ : 0 < J) (hβ : β₁ < β₂) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β₁ * J)) <
      IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β₂ * J)) :=
  polymerFreeEnergy_Λ_tanh_lt_of_lt_in_beta_of_polymers_nonempty
    G (Λ.volume n) h_poly hβ₁ hJ hβ

/-- **Along-ex: pFE(tanh(β·J₁)) < pFE(tanh(β·J₂))** under `β > 0`,
`0 ≤ J₁ < J₂`, polymers nonempty. -/
theorem
polymerFreeEnergyAlongExhaustion_tanh_lt_of_lt_in_J_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty)
    {β J₁ J₂ : ℝ} (hJ₁ : 0 ≤ J₁) (hβ : 0 < β) (hJ : J₁ < J₂) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J₁)) <
      IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J₂)) :=
  polymerFreeEnergy_Λ_tanh_lt_of_lt_in_J_of_polymers_nonempty
    G (Λ.volume n) h_poly hJ₁ hβ hJ

end Ambient
end IsingModel
