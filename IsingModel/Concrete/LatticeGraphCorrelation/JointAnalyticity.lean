import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.JointAnalyticityPartitionFreeEnergy

/-!
# ℤ^d joint analyticity of the along-exhaustion partition function and free energy

Concrete `latticeGraph d` statements that, at a fixed stage of an arbitrary
`Ambient.Exhaustion` of `Fin d → ℤ`, the partition function and the free energy of that stage
are analytic in the inverse temperature, the coupling and the external field jointly, read as
a function of the triple `(β, J, h)`. Analyticity at a prescribed base triple and analyticity
on a neighbourhood of all of `Set.univ` are stated for each of them. Every statement requires
a `Fintype` instance on the edge set induced at every stage; that instance is its entire
requirement, since no `Prop`-typed hypothesis is carried anywhere in this module.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: partitionFunctionAlongExhaustion jointly AnalyticAt**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_analyticAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (n : ℕ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ n) (β, J, h) :=
  Ambient.partitionFunctionAlongExhaustion_analyticAt_joint
    (IsingModel.latticeGraph d) Λ n β J h

/-- **ℤ^d along-ex: partitionFunctionAlongExhaustion jointly AnalyticOnNhd**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_analyticOnNhd_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ n) Set.univ :=
  Ambient.partitionFunctionAlongExhaustion_analyticOnNhd_joint
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: freeEnergyAlongExhaustion jointly AnalyticAt**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_analyticAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (n : ℕ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ n) (β, J, h) :=
  Ambient.freeEnergyAlongExhaustion_analyticAt_joint
    (IsingModel.latticeGraph d) Λ n β J h

/-- **ℤ^d along-ex: freeEnergyAlongExhaustion jointly AnalyticOnNhd**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_analyticOnNhd_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ n) Set.univ :=
  Ambient.freeEnergyAlongExhaustion_analyticOnNhd_joint
    (IsingModel.latticeGraph d) Λ n

end Ambient
end IsingModel
