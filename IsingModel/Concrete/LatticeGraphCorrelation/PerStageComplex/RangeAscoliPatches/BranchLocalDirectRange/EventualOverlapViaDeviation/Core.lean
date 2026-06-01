import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.RangeAscoliPatches.BranchLocalDirectRange.EventualOverlap

/-!
# ℤ^d eventual-overlap branch-local via-deviation direct-range patch wrapper

Part of the split branch-local direct-range wrapper layer.
-/

namespace IsingModel
namespace Ambient

set_option linter.style.longLine false in
/-- **ℤ^d eventual-overlap branch-local data to direct-range patch via branch
deviation**: branch-local boundedness and an explicit principal free-energy
local bound are converted to branch-deviation data, while eventual-overlap
data supplies selected-overlap equality. -/
theorem
freeEnergyComplexAlongExhaustion_eventualOverlapBranchLocalViaDeviationRelCompact_directRange_patch_latticeGraph
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
    (freeEnergy_bound : ∀ i : Fin geom.n, ∃ C : ℝ, ∀ m z
      (_hz : z ∈ Metric.ball (geom.center i : ℂ)
        (eventualData.pointwiseData.branchData.radius (geom.center i))),
      ‖Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) z (p.β : ℂ) m‖ ≤ C)
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
  Ambient.freeEnergyComplexAlongExhaustion_eventualOverlapBranchLocalViaDeviationRelCompact_directRange_patch
    (IsingModel.latticeGraph d) Λ p hBED hd eventualData geom
    freeEnergy_bound eventualLocallyBounded

end Ambient
end IsingModel
