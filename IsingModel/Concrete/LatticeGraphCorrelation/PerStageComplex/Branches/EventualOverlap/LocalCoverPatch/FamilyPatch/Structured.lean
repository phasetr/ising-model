import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.EventualOverlap.LocalCoverPatch.Patch

/-!
# Structured eventual-overlap local-cover family patch wrappers

This module contains the structured eventual-overlap family-and-patching
wrapper split from
`PerStageComplex.Branches.EventualOverlap.LocalCoverPatch.FamilyPatch`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d structured eventual-overlap local-cover family and patching handoff
on `leeYangDomain`**: structured eventual-overlap data produce both the
compatible local-cover family and one differentiable patch. -/
theorem
    freeEnergyComplexAlongExhaustion_eventualOverlapBranchData_localCover_family_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : Ambient.LeeYangEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ J β) :
    ∃ family : Ambient.LeeYangLocalBranchLimitFamily
        (IsingModel.latticeGraph d) Λ J β,
      ∃ g : ℂ → ℂ,
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (data.limitFun h₀)
            (Metric.ball (h₀ : ℂ) (data.radius h₀))) ∧
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (family.data h₀).limitFun
            (Metric.ball (h₀ : ℂ) (family.data h₀).radius)) ∧
        DifferentiableOn ℂ g IsingModel.leeYangDomain :=
  Ambient.freeEnergyComplexAlongExhaustion_eventualOverlapBranchData_localCover_family_patch
    (IsingModel.latticeGraph d) Λ J β data

end Ambient

end IsingModel
