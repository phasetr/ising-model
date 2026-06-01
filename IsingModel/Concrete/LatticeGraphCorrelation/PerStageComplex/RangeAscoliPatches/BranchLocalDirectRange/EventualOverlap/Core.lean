import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.RangeAscoliPatches.BranchLocalDirectRange.ViaDeviation

/-!
# ℤ^d eventual-overlap branch-local direct-range patch wrapper

Part of the split branch-local direct-range wrapper layer.
-/

namespace IsingModel
namespace Ambient

set_option linter.style.longLine false in
/-- **ℤ^d eventual-overlap branch locally bounded Ascoli data to a direct-range
relatively compact patch**: coherent selected-overlap equality is supplied by
the pointwise-normalised eventual-overlap package, while the remaining
branch-local Ascoli inputs feed the direct relatively compact range route. -/
theorem
freeEnergyComplexAlongExhaustion_eventualOverlapBranchLocallyBoundedRelCompact_directRange_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (eventualData :
      Ambient.LeeYangRealPointwiseNormalisedEventualOverlapBranchData
        (IsingModel.latticeGraph d) Λ p)
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K
      (Ambient.LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
        (IsingModel.latticeGraph d) Λ p eventualData))
    (eventualLocallyBounded :
      Ambient.LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchLocallyBoundedAscoliData
        (IsingModel.latticeGraph d) Λ p K eventualData geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i =>
          eventualData.pointwiseData.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (eventualData.pointwiseData.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_eventualOverlapBranchLocallyBoundedRelCompact_directRange_patch
    (IsingModel.latticeGraph d) Λ p hBED hd eventualData geom eventualLocallyBounded

end Ambient
end IsingModel
