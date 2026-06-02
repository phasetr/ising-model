import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.LocalCoverPatch.OpenPatch

/-!
# Structured local-cover patch wrappers

This module contains non-real structured local-cover branch-limit patch wrappers
split from `PerStageComplex.Branches.LocalCoverPatch.StructuredPatch`.
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

/-- **ℤ^d packaged structured local-cover branch-limit patching handoff on
`leeYangDomain`**: a compatible `Ambient.LeeYangLocalBranchLimitFamily` patches
to one differentiable function on `leeYangDomain`. -/
theorem freeEnergyComplexAlongExhaustion_branchLimitFamily_localCover_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (family : Ambient.LeeYangLocalBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β) :
    ∃ g : ℂ → ℂ,
      (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
        Set.EqOn g (family.data h₀).limitFun
          (Metric.ball (h₀ : ℂ) (family.data h₀).radius)) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain :=
  Ambient.freeEnergyComplexAlongExhaustion_branchLimitFamily_localCover_patch
    (IsingModel.latticeGraph d) Λ J β family

end Ambient

end IsingModel
