import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.Basic

/-!
# ℤ^d joint analyticity of the complex partition function and free energy

Instantiates at the subgraph induced on a fixed finite volume `Λ : Finset (Fin d → ℤ)` of
`IsingModel.latticeGraph d` the joint analyticity in `(J, h, β)` of the complex partition
function and of the complex free-energy density. The partition-function statement holds at
every base point and carries no hypothesis; the free-energy statement is conditional on the
partition function lying in `Complex.slitPlane` at that base point.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `partitionFunctionComplex` jointly entire in `(J, h, β)`**
(Λ-induced). -/
theorem partitionFunctionComplex_analyticAt_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (z₀ : ℂ × ℂ × ℂ) :
    AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ =>
      IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2) z₀ :=
  IsingModel.partitionFunctionComplex_analyticAt_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z₀

/-- **ℤ^d `freeEnergyComplex` jointly analytic** (Λ-induced), on
`{Z ∈ slitPlane}`. -/
theorem freeEnergyComplex_analyticAt_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (z₀ : ℂ × ℂ × ℂ)
    (hZ : IsingModel.partitionFunctionComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            z₀.1 z₀.2.1 z₀.2.2
          ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ =>
      IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2) z₀ :=
  IsingModel.freeEnergyComplex_analyticAt_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z₀ hZ

end Ambient

end IsingModel
