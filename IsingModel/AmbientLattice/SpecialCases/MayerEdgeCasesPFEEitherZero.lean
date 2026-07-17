import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMayerIdentity

/-!
# Mayer identity at `J = β = 0` polymer_free_energy wrapper along an exhaustion

Narrow child module for the §18.5 along-exhaustion Mayer identity
edge-case wrapper at the double-zero parameter slice (J = β = 0)
in `polymer_free_energy` form extracted from
`MayerEdgeCasesPFE.lean`. The wrapper is a thin pass-through to
the corresponding
`mayer_identity_at_either_zero_polymer_free_energy_Λ` ambient
lemma. The theorem name is unchanged from the former
`MayerEdgeCases` declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: Mayer identity at `J = β = 0` (polymer_free_energy form)**. -/
theorem
mayer_identity_at_either_zero_polymer_free_energy_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n))
        (Real.tanh ((0 : ℝ) * (0 : ℝ))) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh ((0 : ℝ) * (0 : ℝ))) :=
  mayer_identity_at_either_zero_polymer_free_energy_Λ G (Λ.volume n) N

end Ambient
end IsingModel
