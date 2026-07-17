import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerEdgeCasesPolymerFreeEnergy

/-!
# Concrete along-ex polymerFreeEnergy = mayerPartialSum edge cases

Narrow child module for four ℤ^d
`polymerFreeEnergyAlongExhaustion_latticeGraph_eq_mayerPartialSum_at`
wrappers (`{_zero, _betaJ_zero, _beta_zero, _J_zero}`).
Each wrapper is a thin pass-through to the corresponding
ambient `polymerFreeEnergyAlongExhaustion_eq_mayerPartialSum_at_*`
lemma at `IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

open Finset Real


/-- **ℤ^d along-ex: polymerFreeEnergy = mayerPartialSum at t = 0**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_eq_mayerPartialSum_at_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (N : ℕ) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 0 =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N 0 :=
  Ambient.polymerFreeEnergyAlongExhaustion_eq_mayerPartialSum_at_zero
    (IsingModel.latticeGraph d) Λ N n

/-- **ℤ^d along-ex: polymerFreeEnergy = mayerPartialSum at β·J = 0**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_eq_mayerPartialSum_at_betaJ_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (N : ℕ) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β * J)) :=
  Ambient.polymerFreeEnergyAlongExhaustion_eq_mayerPartialSum_at_betaJ_zero
    (IsingModel.latticeGraph d) Λ hβJ N n

/-- **ℤ^d along-ex: polymerFreeEnergy = mayerPartialSum at β = 0**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_eq_mayerPartialSum_at_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J : ℝ) (N : ℕ) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh ((0 : ℝ) * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh ((0 : ℝ) * J)) :=
  Ambient.polymerFreeEnergyAlongExhaustion_eq_mayerPartialSum_at_beta_zero
    (IsingModel.latticeGraph d) Λ J N n

/-- **ℤ^d along-ex: polymerFreeEnergy = mayerPartialSum at J = 0**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_eq_mayerPartialSum_at_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (β : ℝ) (N : ℕ) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * (0 : ℝ))) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β * (0 : ℝ))) :=
  Ambient.polymerFreeEnergyAlongExhaustion_eq_mayerPartialSum_at_J_zero
    (IsingModel.latticeGraph d) Λ β N n

end Ambient
end IsingModel
