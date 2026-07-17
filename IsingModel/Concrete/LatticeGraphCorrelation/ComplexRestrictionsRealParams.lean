import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.RealAxis

/-!
# ℤ^d real-params joint analyticity wrappers

Narrow child module for three ℤ^d real-parameter joint-analyticity
wrappers extracted from `ComplexRestrictions.lean`:

* `real_params_in_analyticity_locus_joint_latticeGraph`,
* `real_params_analyticAt_joint_latticeGraph`,
* `real_params_image_subset_analyticity_locus_joint_latticeGraph`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d real parameter point in joint slitPlane-locus** (Λ-induced). -/
theorem real_params_in_analyticity_locus_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    ((p.J : ℂ), (p.h : ℂ), (p.β : ℂ)) ∈
      {z : ℂ × ℂ × ℂ | IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        z.1 z.2.1 z.2.2 ∈ Complex.slitPlane} :=
  IsingModel.real_params_in_analyticity_locus_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d real parameter point `AnalyticAt` jointly** (Λ-induced). -/
theorem real_params_analyticAt_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    AnalyticAt ℂ
      (fun z : ℂ × ℂ × ℂ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2)
      ((p.J : ℂ), (p.h : ℂ), (p.β : ℂ)) :=
  IsingModel.real_params_analyticAt_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d image of real-parameter cast ⊆ joint slitPlane-locus**
(Λ-induced). -/
theorem real_params_image_subset_analyticity_locus_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    (fun p : IsingParams ℝ => ((p.J : ℂ), (p.h : ℂ), (p.β : ℂ)))
        '' Set.univ ⊆
      {z : ℂ × ℂ × ℂ | IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        z.1 z.2.1 z.2.2 ∈ Complex.slitPlane} :=
  IsingModel.real_params_image_subset_analyticity_locus_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

end Ambient
end IsingModel
