import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaPfeSharpening

/-!
# Polymer free-energy `< (1+t)^|E| - 1` wrapper along an exhaustion

Narrow child module for the §18.5 ambient alongExhaustion
`polymerFreeEnergyAlongExhaustion_lt_pow_sub_one_of_eps_pos`
wrapper extracted from
`PolymerFreeEnergyEpsilonSharpeningPFE.lean`. The wrapper is a
thin pass-through to the ambient
`polymerFreeEnergy_Λ_lt_pow_sub_one_of_eps_pos` lemma. The
theorem name is unchanged from the former
`PolymerFreeEnergyEpsilonSharpening` declaration.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

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
