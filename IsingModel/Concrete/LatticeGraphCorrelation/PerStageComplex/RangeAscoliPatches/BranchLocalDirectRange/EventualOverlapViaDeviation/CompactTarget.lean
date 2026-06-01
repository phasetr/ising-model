import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.RangeAscoliPatches.BranchLocalDirectRange.EventualOverlapViaDeviation.Core

/-!
# ℤ^d compact target for eventual-overlap branch-local via-deviation wrapper

Part of the split branch-local direct-range wrapper layer.
-/

namespace IsingModel
namespace Ambient

set_option linter.style.longLine false in
/-- **ℤ^d compact target to eventual-overlap branch-local via-deviation
direct-range patch input**: compactness extracts finite all-stage geometry,
branch-local boundedness is converted to branch-deviation data using the
explicit principal free-energy local bound, and eventual-overlap data supplies
selected overlap. -/
theorem
freeEnergyComplexAlongExhaustion_eventualOverlapBranchLocalViaDeviationRelCompact_directRange_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (eventualData :
      Ambient.LeeYangRealPointwiseNormalisedEventualOverlapBranchData
        (IsingModel.latticeGraph d) Λ p) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K
        (Ambient.LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
          (IsingModel.latticeGraph d) Λ p eventualData),
      (∀ i : Fin geom.n, ∃ C : ℝ, ∀ m z
        (_hz : z ∈ Metric.ball (geom.center i : ℂ)
          (eventualData.pointwiseData.branchData.radius (geom.center i))),
        ‖Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (p.J : ℂ) z (p.β : ℂ) m‖ ≤ C) →
      Ambient.LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchLocallyBoundedAscoliData
          (IsingModel.latticeGraph d) Λ p K eventualData geom →
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
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_eventualOverlapBranchLocalViaDeviationRelCompact_directRange_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK eventualData

end Ambient
end IsingModel
