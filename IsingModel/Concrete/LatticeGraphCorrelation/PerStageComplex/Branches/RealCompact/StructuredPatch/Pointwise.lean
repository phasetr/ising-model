import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.RealCompact.StructuredPatch.Structured

/-!
# Pointwise-normalised eventual-overlap real patch wrappers

This module contains the pointwise-normalised eventual-overlap real-axis
local-cover patch wrapper split from
`PerStageComplex.Branches.RealCompact.StructuredPatch`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d pointwise-normalised eventual-overlap data local-cover patching with
real-axis identification**: pointwise-normalised structured data projects to
the real-centred structured package, then patches and identifies the real
centre. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormEventualData_localCover_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (data : Ambient.LeeYangRealPointwiseNormalisedEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ p) :
    ∃ realFamily : Ambient.LeeYangRealBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p,
      ∃ g : ℂ → ℂ,
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (data.pointwiseData.branchData.limitFun h₀)
            (Metric.ball (h₀ : ℂ) (data.pointwiseData.branchData.radius h₀))) ∧
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (realFamily.family.data h₀).limitFun
            (Metric.ball (h₀ : ℂ) (realFamily.family.data h₀).radius)) ∧
        DifferentiableOn ℂ g IsingModel.leeYangDomain ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormEventualData_localCover_real
    (IsingModel.latticeGraph d) Λ p hBED hd data

end Ambient

end IsingModel
