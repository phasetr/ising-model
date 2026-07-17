import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.RealAxis

/-!
# ℤ^d joint slitPlane-locus wrappers

Narrow child module for four ℤ^d joint slitPlane-locus wrappers
extracted from `ComplexSlitPlane.lean`:

* `freeEnergyComplex_analyticOnNhd_slitPlane_locus_joint_latticeGraph`,
* `isOpen_freeEnergy_analyticity_locus_joint_latticeGraph`,
* `freeEnergyComplex_continuousOn_slitPlane_locus_joint_latticeGraph`,
* `freeEnergyComplex_differentiableOn_slitPlane_locus_joint_latticeGraph`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `f_ℂ` `AnalyticOnNhd` joint slitPlane-locus** (Λ-induced). -/
theorem freeEnergyComplex_analyticOnNhd_slitPlane_locus_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    AnalyticOnNhd ℂ
      (fun z : ℂ × ℂ × ℂ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2)
      {z : ℂ × ℂ × ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2
        ∈ Complex.slitPlane} :=
  IsingModel.freeEnergyComplex_analyticOnNhd_slitPlane_locus_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-- **ℤ^d joint slitPlane-locus is open** (Λ-induced). -/
theorem isOpen_freeEnergy_analyticity_locus_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    IsOpen {z : ℂ × ℂ × ℂ | IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2
        ∈ Complex.slitPlane} :=
  IsingModel.isOpen_freeEnergy_analyticity_locus_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-- **ℤ^d `f_ℂ` `ContinuousOn` joint slitPlane-locus** (Λ-induced). -/
theorem freeEnergyComplex_continuousOn_slitPlane_locus_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    ContinuousOn
      (fun z : ℂ × ℂ × ℂ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2)
      {z : ℂ × ℂ × ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2
        ∈ Complex.slitPlane} :=
  IsingModel.freeEnergyComplex_continuousOn_slitPlane_locus_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-- **ℤ^d `f_ℂ` `DifferentiableOn` joint slitPlane-locus** (Λ-induced). -/
theorem freeEnergyComplex_differentiableOn_slitPlane_locus_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    DifferentiableOn ℂ
      (fun z : ℂ × ℂ × ℂ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2)
      {z : ℂ × ℂ × ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2
        ∈ Complex.slitPlane} :=
  IsingModel.freeEnergyComplex_differentiableOn_slitPlane_locus_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

end Ambient
end IsingModel
