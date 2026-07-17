import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaPfeSharpening

/-!
# Polymer free-energy tanh `< ε(tanh) ↔ 0 < ε(tanh)` wrapper

Narrow child module for the §18.5 along-exhaustion
`polymerFreeEnergyAlongExhaustion_tanh_lt_eps_iff_eps_pos` wrapper
extracted from `PolymerFreeEnergyTanhSharpeningIff.lean`. The
wrapper is a thin pass-through to
`polymerFreeEnergy_Λ_tanh_lt_eps_iff_eps_pos`. The theorem name is
unchanged from the former `PolymerFreeEnergyTanhSharpening`
declaration.
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

end Ambient
end IsingModel
