import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.EventualOverlap.StructuredFamily

/-!
# Structured eventual-overlap local-cover patch wrapper

This module contains the structured eventual-overlap local-cover patch wrapper
split from `PerStageComplex.Branches.EventualOverlap.LocalCoverPatch.Patch`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d structured eventual-overlap local-cover patching handoff on
`leeYangDomain`**: structured eventual-overlap data patch directly to one
differentiable function on `leeYangDomain`. -/
theorem freeEnergyComplexAlongExhaustion_eventualOverlapBranchData_localCover_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : Ambient.LeeYangEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ J β) :
    ∃ g : ℂ → ℂ,
      (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
        Set.EqOn g (data.limitFun h₀)
          (Metric.ball (h₀ : ℂ) (data.radius h₀))) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain :=
  Ambient.freeEnergyComplexAlongExhaustion_eventualOverlapBranchData_localCover_patch
    (IsingModel.latticeGraph d) Λ J β data

end Ambient

end IsingModel
