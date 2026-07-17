import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.RealAxis

/-!
# ℤ^d freeEnergyComplex continuity / differentiability wrappers

Narrow child module for three ℤ^d freeEnergyComplex continuity /
differentiability wrappers extracted from `ComplexBranchEntire.lean`:

* `continuous_freeEnergyComplex_on_locus_latticeGraph`,
* `continuousAt_freeEnergyComplex_at_real_joint_latticeGraph`,
* `differentiableAt_freeEnergyComplex_at_real_joint_latticeGraph`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `ContinuousOn` joint slitPlane locus (packaged alias)**
(Λ-induced). -/
theorem continuous_freeEnergyComplex_on_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    ContinuousOn
      (fun z : ℂ × ℂ × ℂ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2)
      {z : ℂ × ℂ × ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2
        ∈ Complex.slitPlane} :=
  IsingModel.continuous_freeEnergyComplex_on_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-- **ℤ^d joint `ContinuousAt` at real parameters** (Λ-induced). -/
theorem continuousAt_freeEnergyComplex_at_real_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    ContinuousAt
      (fun z : ℂ × ℂ × ℂ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2)
      ((p.J : ℂ), (p.h : ℂ), (p.β : ℂ)) :=
  IsingModel.continuousAt_freeEnergyComplex_at_real_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d joint `DifferentiableAt` at real parameters** (Λ-induced). -/
theorem differentiableAt_freeEnergyComplex_at_real_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    DifferentiableAt ℂ
      (fun z : ℂ × ℂ × ℂ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2)
      ((p.J : ℂ), (p.h : ℂ), (p.β : ℂ)) :=
  IsingModel.differentiableAt_freeEnergyComplex_at_real_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

end Ambient
end IsingModel
