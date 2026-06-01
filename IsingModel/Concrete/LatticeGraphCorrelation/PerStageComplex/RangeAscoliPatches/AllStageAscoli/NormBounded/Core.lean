import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.RangeAscoliPatches.AllStageAscoli.ClosedProduct

/-!
# ℤ^d all-stage norm-bounded Ascoli patch wrappers

This module contains the direct all-stage norm-bounded Ascoli wrapper endpoint.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d pointwise-normalised all-stage norm-bounded closed-product Ascoli
data to compact real-cover patch**: pointwise norm bounds supply the compact
closed-ball targets required by the closed-product Ascoli package. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageNormBoundedAscoliData_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data)
    (normBounded :
      Ambient.LeeYangPointwiseNormAllStageCompactRealNormBoundedAscoliData
        (IsingModel.latticeGraph d) Λ p K data geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageNormBoundedAscoliData_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom normBounded

end Ambient
end IsingModel
