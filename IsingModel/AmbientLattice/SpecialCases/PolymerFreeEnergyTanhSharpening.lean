import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhSharpeningIff
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhSharpeningStrictMono

/-!
# Polymer free-energy tanh sharpening + β/J strict-mono wrappers along
an exhaustion

Narrow child module for along-exhaustion polymer free-energy
`tanh sharpening + β/J strict-mono` wrappers. This keeps callers that
only need these forwarders out of the monolithic legacy special-cases
module.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 polymerFreeEnergy tanh sharpening + β/J strict-mono
along-ex wraps -/

/-! ## Moved: pFE tanh iff / `_of_eps_pos` wrappers

The five `polymerFreeEnergyAlongExhaustion_tanh_*` iff /
`_of_eps_pos` wrappers now live in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhSharpeningIff`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from `Legacy.lean`.
-/

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

/-! ## Moved: 2 `_strictMonoOn_*` wrappers

The two along-ex `polymerFreeEnergyAlongExhaustion_tanh_strictMonoOn_*`
wrappers (`_strictMonoOn_beta`, `_strictMonoOn_J`) now live in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhSharpeningStrictMono`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from the umbrella.
-/

end Ambient
end IsingModel
