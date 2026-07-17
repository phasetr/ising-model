import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaPfeSharpening

/-!
# Polymer free-energy tanh `< log 2` wrapper along an exhaustion

Narrow child module for the §18.5 ambient alongExhaustion
`polymerFreeEnergyAlongExhaustion_tanh_lt_log_two_of_pow_lt_two`
wrapper extracted from
`PolymerFreeEnergyHighTemperatureBoundsTanh.lean`. The wrapper is
a thin pass-through to
`polymerFreeEnergy_Λ_tanh_lt_log_two_of_pow_lt_two`. The theorem
name is unchanged from the former
`PolymerFreeEnergyHighTemperatureBounds` declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: pFE(tanh) < log 2** under `(1+tanh)^|E| < 2`. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_lt_log_two_of_pow_lt_two
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G (Λ.volume n)).edgeFinset.card < 2) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) < Real.log 2 :=
  polymerFreeEnergy_Λ_tanh_lt_log_two_of_pow_lt_two
    G (Λ.volume n) hβJ h_pow

end Ambient
end IsingModel
