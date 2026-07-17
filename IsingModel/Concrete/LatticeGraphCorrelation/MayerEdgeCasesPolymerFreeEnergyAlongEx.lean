import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerEdgeCasesPFE

/-!
# Concrete along-ex Mayer-identity polymer_free_energy edge-case wrappers

Narrow child module for 3 ℤ^d along-exhaustion
`mayer_identity_*_polymer_free_energy_AlongExhaustion_latticeGraph`
wrappers extracted from `MayerEdgeCasesPolymerFreeEnergy.lean`:

* `mayer_identity_at_J_zero_polymer_free_energy_AlongExhaustion_latticeGraph`,
* `mayer_identity_at_beta_zero_polymer_free_energy_AlongExhaustion_latticeGraph`,
* `mayer_identity_at_either_zero_polymer_free_energy_AlongExhaustion_latticeGraph`.

Each result is a thin pass-through of the corresponding ambient
`Ambient.mayer_identity_at_*_zero_polymer_free_energy_AlongExhaustion`
lemma at `G := IsingModel.latticeGraph d`. The theorem names are
unchanged from the former `MayerEdgeCasesPolymerFreeEnergy` declarations.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d along-ex: Mayer identity at `J = 0` (polymer_free_energy form)**. -/
theorem
mayer_identity_at_J_zero_polymer_free_energy_AlongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (β : ℝ) (N : ℕ) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * (0 : ℝ))) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β * (0 : ℝ))) :=
  Ambient.mayer_identity_at_J_zero_polymer_free_energy_AlongExhaustion
    (IsingModel.latticeGraph d) Λ β N n

/-- **ℤ^d along-ex: Mayer identity at `β = 0` (polymer_free_energy form)**. -/
theorem
mayer_identity_at_beta_zero_polymer_free_energy_AlongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J : ℝ) (N : ℕ) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh ((0 : ℝ) * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh ((0 : ℝ) * J)) :=
  Ambient.mayer_identity_at_beta_zero_polymer_free_energy_AlongExhaustion
    (IsingModel.latticeGraph d) Λ J N n

/-- **ℤ^d along-ex: Mayer identity at `J = β = 0` (polymer_free_energy form)**. -/
theorem
mayer_identity_at_either_zero_polymer_free_energy_AlongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (N : ℕ) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh ((0 : ℝ) * (0 : ℝ))) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh ((0 : ℝ) * (0 : ℝ))) :=
  Ambient.mayer_identity_at_either_zero_polymer_free_energy_AlongExhaustion
    (IsingModel.latticeGraph d) Λ N n

end Ambient
end IsingModel
