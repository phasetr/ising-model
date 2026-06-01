import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.RangeAscoliPatches

namespace IsingModel
namespace Ambient

set_option linter.style.longLine false in
/-- **ℤ^d eventual-overlap branch-deviation Ascoli data to a direct-range
relatively compact patch**: coherent selected-overlap equality is supplied by
the pointwise-normalised eventual-overlap package, while the remaining
branch-deviation Ascoli inputs feed the direct relatively compact range route.
-/
theorem
freeEnergyComplexAlongExhaustion_eventualOverlapBranchDeviationRelCompact_directRange_patch_latticeGraph
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
    (eventualDeviation :
      Ambient.LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchDeviationAscoliData
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
  Ambient.freeEnergyComplexAlongExhaustion_eventualOverlapBranchDeviationRelCompact_directRange_patch
    (IsingModel.latticeGraph d) Λ p hBED hd eventualData geom eventualDeviation

set_option linter.style.longLine false in
/-- **ℤ^d compact target to eventual-overlap branch-deviation direct-range
patch input**: compactness extracts the selected all-stage finite geometry,
and the pointwise-normalised eventual-overlap package supplies coherent
selected-overlap equality for the branch-deviation Ascoli route. -/
theorem
freeEnergyComplexAlongExhaustion_eventualOverlapBranchDeviationRelCompact_directRange_patch_isCompact_latticeGraph
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
      Ambient.LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchDeviationAscoliData
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
  Ambient.freeEnergyComplexAlongExhaustion_eventualOverlapBranchDeviationRelCompact_directRange_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK eventualData

end Ambient

end IsingModel
