import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.LocalCoverPatch.StructuredPatch.Real.Family

/-!
# Structured local-cover real-centred family wrappers

This module contains the real-centred packaged structured local-cover endpoint
wrapper split from `PerStageComplex.Branches.LocalCoverPatch.StructuredPatch.Real`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d real-centred packaged structured local-cover branch-limit endpoint**:
a compatible real-centred `Ambient.LeeYangRealBranchLimitFamily` patches to a
differentiable function on `leeYangDomain`, and its packaged centre
normalisation identifies the patched value with `↑freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_realBranchLimitFamily_localCover_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (realFamily : Ambient.LeeYangRealBranchLimitFamily
      (IsingModel.latticeGraph d) Λ p) :
    ∃ g : ℂ → ℂ,
      (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
        Set.EqOn g (realFamily.family.data h₀).limitFun
          (Metric.ball (h₀ : ℂ) (realFamily.family.data h₀).radius)) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain ∧
      g (p.h : ℂ) =
        ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_realBranchLimitFamily_localCover_real
    (IsingModel.latticeGraph d) Λ p hBED hd realFamily

end Ambient

end IsingModel
