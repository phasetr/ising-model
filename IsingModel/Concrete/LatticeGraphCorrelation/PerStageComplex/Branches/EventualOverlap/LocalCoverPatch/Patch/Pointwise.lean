import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.EventualOverlap.LocalCoverPatch.Patch.Structured

/-!
# Pointwise-normalised eventual-overlap local-cover patch wrapper

This module contains the pointwise-normalised eventual-overlap local-cover patch
wrapper split from
`PerStageComplex.Branches.EventualOverlap.LocalCoverPatch.Patch`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d pointwise-normalised eventual-overlap local-cover patching handoff
on `leeYangDomain`**: pointwise-normalised structured data expose the
underlying eventual-overlap package, whose local limits patch to one
differentiable function on `leeYangDomain`. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormEventualData_localCover_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : Ambient.LeeYangPointwiseNormalisedEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ J β) :
    ∃ g : ℂ → ℂ,
      (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
        Set.EqOn g (data.branchData.limitFun h₀)
          (Metric.ball (h₀ : ℂ) (data.branchData.radius h₀))) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormEventualData_localCover_patch
    (IsingModel.latticeGraph d) Λ J β data

end Ambient

end IsingModel
