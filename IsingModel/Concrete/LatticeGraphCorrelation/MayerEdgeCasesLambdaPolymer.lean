import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMayerIdentity

/-!
# Concrete Λ polymerFreeEnergy = mayerPartialSum edge cases

Narrow child module for four ℤ^d
`polymerFreeEnergy_Λ_latticeGraph_eq_mayerPartialSum_at_{zero,betaJ_zero,beta_zero,J_zero}`
wrappers. Each wrapper is a thin pass-through to the corresponding
ambient `polymerFreeEnergy_Λ_eq_mayerPartialSum_at_*` lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-! ### §18.5 polymerFreeEnergy_eq_mayerPartialSum_at edge-case ℤ^d wraps -/

/-- **ℤ^d Λ: polymerFreeEnergy = mayerPartialSum at t = 0**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_eq_mayerPartialSum_at_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) 0 =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N 0 :=
  Ambient.polymerFreeEnergy_Λ_eq_mayerPartialSum_at_zero
    (IsingModel.latticeGraph d) Λ N

/-- **ℤ^d Λ: polymerFreeEnergy = mayerPartialSum at β·J = 0**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_eq_mayerPartialSum_at_betaJ_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β * J)) :=
  Ambient.polymerFreeEnergy_Λ_eq_mayerPartialSum_at_betaJ_zero
    (IsingModel.latticeGraph d) Λ hβJ N

/-- **ℤ^d Λ: polymerFreeEnergy = mayerPartialSum at β = 0**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_eq_mayerPartialSum_at_beta_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh ((0 : ℝ) * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh ((0 : ℝ) * J)) :=
  Ambient.polymerFreeEnergy_Λ_eq_mayerPartialSum_at_beta_zero
    (IsingModel.latticeGraph d) Λ J N

/-- **ℤ^d Λ: polymerFreeEnergy = mayerPartialSum at J = 0**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_eq_mayerPartialSum_at_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * (0 : ℝ))) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β * (0 : ℝ))) :=
  Ambient.polymerFreeEnergy_Λ_eq_mayerPartialSum_at_J_zero
    (IsingModel.latticeGraph d) Λ β N

end Ambient
end IsingModel
