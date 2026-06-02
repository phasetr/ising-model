import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.LocalCoverPatch.OpenPatch

/-!
# Structured local-cover data patch wrapper

This module contains the structured local-cover branch-limit data patch wrapper
split from `PerStageComplex.Branches.LocalCoverPatch.StructuredPatch.Patch`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d structured pointed local-cover branch-limit patching handoff on
`leeYangDomain`**: point-indexed `Ambient.LeeYangLocalBranchLimit` data with
compatible local limits patches to one differentiable function on
`leeYangDomain`. -/
theorem freeEnergyComplexAlongExhaustion_branchLimitData_localCover_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Ambient.LeeYangLocalBranchLimit (IsingModel.latticeGraph d) Λ J β h₀)
    (hcompat : ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Set.EqOn (data h₀).limitFun (data h₁).limitFun
        (Metric.ball (h₀ : ℂ) (data h₀).radius
          ∩ Metric.ball (h₁ : ℂ) (data h₁).radius)) :
    ∃ g : ℂ → ℂ,
      (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
        Set.EqOn g (data h₀).limitFun
          (Metric.ball (h₀ : ℂ) (data h₀).radius)) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain :=
  Ambient.freeEnergyComplexAlongExhaustion_branchLimitData_localCover_patch
    (IsingModel.latticeGraph d) Λ J β data hcompat

end Ambient

end IsingModel
