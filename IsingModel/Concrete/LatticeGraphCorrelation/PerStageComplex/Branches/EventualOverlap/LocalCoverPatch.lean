import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.EventualOverlap.StructuredFamily

/-!
# Eventual-overlap local-cover patch wrappers

This module contains non-real local-cover patching wrappers for structured and
pointwise-normalised eventual-overlap branch data.
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

/-- **ℤ^d pointwise-normalised eventual-overlap local-cover family and
patching handoff on `leeYangDomain`**: pointwise-normalised structured data
produce both the compatible local-cover family and one differentiable patch. -/
theorem
    freeEnergyComplexAlongExhaustion_pointwiseNormEventualData_localCover_family_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : Ambient.LeeYangPointwiseNormalisedEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ J β) :
    ∃ family : Ambient.LeeYangLocalBranchLimitFamily
        (IsingModel.latticeGraph d) Λ J β,
      ∃ g : ℂ → ℂ,
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (data.branchData.limitFun h₀)
            (Metric.ball (h₀ : ℂ) (data.branchData.radius h₀))) ∧
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (family.data h₀).limitFun
            (Metric.ball (h₀ : ℂ) (family.data h₀).radius)) ∧
        DifferentiableOn ℂ g IsingModel.leeYangDomain :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormEventualData_localCover_family_patch
    (IsingModel.latticeGraph d) Λ J β data

end Ambient

end IsingModel
