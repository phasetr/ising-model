import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.RangeAscoliPatches.RangeCompactOpen

/-!
# ℤ^d all-stage Arzelà-Ascoli patch wrappers

This module contains the direct all-stage Arzelà-Ascoli wrapper endpoint.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d pointwise-normalised all-stage Arzelà-Ascoli data to compact
real-cover patch**: compactness of the pointwise function-space image and
equicontinuity for the selected all-stage geometry supply compact-open
compactness via Arzelà-Ascoli. -/
theorem freeEnergyComplexAlongExhaustion_allStageAscoliData_patch_latticeGraph
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
    (ascoli : Ambient.LeeYangPointwiseNormAllStageCompactRealAscoliData
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
  Ambient.freeEnergyComplexAlongExhaustion_allStageAscoliData_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom ascoli

end Ambient
end IsingModel
