import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.RealCompact.RawPatch

/-!
# Structured eventual-overlap real patch wrappers

This module contains the structured eventual-overlap real-axis local-cover
patch wrapper split from `PerStageComplex.Branches.RealCompact.StructuredPatch`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d structured eventual-overlap branch-data local-cover patching with
real-axis identification**: a real-centred structured local-cover package is
converted to `Ambient.LeeYangRealBranchLimitFamily`, then patched and
identified at the real centre. -/
theorem freeEnergyComplexAlongExhaustion_realEventualOverlapBranchData_localCover_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (data : Ambient.LeeYangRealEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ p) :
    ∃ realFamily : Ambient.LeeYangRealBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p,
      ∃ g : ℂ → ℂ,
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (data.branchData.limitFun h₀)
            (Metric.ball (h₀ : ℂ) (data.branchData.radius h₀))) ∧
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (realFamily.family.data h₀).limitFun
            (Metric.ball (h₀ : ℂ) (realFamily.family.data h₀).radius)) ∧
        DifferentiableOn ℂ g IsingModel.leeYangDomain ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_realEventualOverlapBranchData_localCover_real
    (IsingModel.latticeGraph d) Λ p hBED hd data

end Ambient

end IsingModel
