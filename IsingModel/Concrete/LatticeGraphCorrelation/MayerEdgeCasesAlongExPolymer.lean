import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerEdgeCases

/-!
# ℤ^d polymer free energy at trivial activities, along an exhaustion

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ`, the agreement of `polymerFreeEnergy` on the stage-`n` induced subgraph with the
Mayer partial sum at every truncation order, at the activity slices where each side is
trivial: at the bare activity `0`, and at the activity `tanh (β * J)` under `β * J = 0`, at
`β = 0`, and at `J = 0`. Only the statement at a general parameter pair assumes anything about
the parameters, namely `β * J = 0`; the remaining `tanh` statements substitute `0` for `β` and
for `J` literally and leave the other parameter arbitrary.
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
