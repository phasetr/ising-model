import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Mayer identity polymer_free_energy edge-case wrappers along an exhaustion

Narrow child module for three §18.5 along-exhaustion Mayer identity
edge-case wrappers in `polymer_free_energy` form (specializations
at `J = 0`, `β = 0`, and `J = β = 0`). Each wrapper is a thin
pass-through to the corresponding
`mayer_identity_at_*_polymer_free_energy_Λ` ambient lemma. Theorem
names are unchanged from the former `MayerEdgeCases` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 mayer_identity polymer_free_energy variants along-ex wraps -/

/-- **Along-ex: Mayer identity at `J = 0` (polymer_free_energy form)**. -/
theorem
mayer_identity_at_J_zero_polymer_free_energy_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (N : ℕ) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * (0 : ℝ))) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh (β * (0 : ℝ))) :=
  mayer_identity_at_J_zero_polymer_free_energy_Λ G (Λ.volume n) β N

/-- **Along-ex: Mayer identity at `β = 0` (polymer_free_energy form)**. -/
theorem
mayer_identity_at_beta_zero_polymer_free_energy_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (N : ℕ) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh ((0 : ℝ) * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh ((0 : ℝ) * J)) :=
  mayer_identity_at_beta_zero_polymer_free_energy_Λ G (Λ.volume n) J N

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
