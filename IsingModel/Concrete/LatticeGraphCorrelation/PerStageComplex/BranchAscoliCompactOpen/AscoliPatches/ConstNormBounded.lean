import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.EventualClosedBallPatches
import IsingModel.AmbientComplexAnalyticity.BranchLocallyBoundedPatches.ConstNormBounded

/-!
# Branch Ascoli compact-open split — branch constant norm-bounded Ascoli patch

Part of the split branch Ascoli compact-open layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d pointwise-normalised all-stage branch constant norm-bounded Ascoli
data to compact real-cover patch**: ballwise constant branch-family norm bounds
are fed through the ambient branch norm-bounded Ascoli package. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageBranchConstNormBoundedAscoliData_patch_latticeGraph
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
    (constBounded :
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchConstNormBoundedAscoliData
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
  Ambient.freeEnergyComplexAlongExhaustion_allStageBranchConstNormBoundedAscoliData_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom constBounded

end Ambient
end IsingModel
