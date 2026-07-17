import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMayerIdentity

/-!
# Concrete `mayer_identity_*_polymer_free_energy_*` edge cases

Narrow child module for six ℤ^d
`mayer_identity_*_polymer_free_energy_*_latticeGraph` wrappers covering
Λ + along-exhaustion forms at `J = 0`, `β = 0`, and either-zero edge
cases. Each wrapper is a thin pass-through to the corresponding
ambient `mayer_identity_*_polymer_free_energy_*` lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-! ### §18.5 mayer_identity polymer_free_energy variants ℤ^d wraps -/

/-- **ℤ^d Λ: Mayer identity at `J = 0` (polymer_free_energy form)**. -/
theorem
mayer_identity_at_J_zero_polymer_free_energy_Λ_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * (0 : ℝ))) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β * (0 : ℝ))) :=
  Ambient.mayer_identity_at_J_zero_polymer_free_energy_Λ
    (IsingModel.latticeGraph d) Λ β N

/-- **ℤ^d Λ: Mayer identity at `β = 0` (polymer_free_energy form)**. -/
theorem
mayer_identity_at_beta_zero_polymer_free_energy_Λ_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh ((0 : ℝ) * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh ((0 : ℝ) * J)) :=
  Ambient.mayer_identity_at_beta_zero_polymer_free_energy_Λ
    (IsingModel.latticeGraph d) Λ J N

/-- **ℤ^d Λ: Mayer identity at `J = β = 0` (polymer_free_energy form)**. -/
theorem
mayer_identity_at_either_zero_polymer_free_energy_Λ_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh ((0 : ℝ) * (0 : ℝ))) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh ((0 : ℝ) * (0 : ℝ))) :=
  Ambient.mayer_identity_at_either_zero_polymer_free_energy_Λ
    (IsingModel.latticeGraph d) Λ N

/-! ## Moved: along-ex Mayer-identity polymer_free_energy wrappers

The three along-ex
`mayer_identity_at_*_zero_polymer_free_energy_AlongExhaustion_latticeGraph`
wrappers (`J_zero`, `beta_zero`, `either_zero`) now live in
`MayerEdgeCasesPolymerFreeEnergyAlongEx.lean`. -/





end Ambient
end IsingModel
