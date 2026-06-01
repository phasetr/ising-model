import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.RangeAscoliPatches.BranchLocalDirectRange.ViaDeviation.Core

/-!
# ℤ^d compact target for branch-local via-deviation direct-range wrapper

Part of the split branch-local direct-range wrapper layer.
-/

namespace IsingModel
namespace Ambient

set_option linter.style.longLine false in
/-- **ℤ^d compact target to branch-local via-deviation direct-range patch
input**: compactness extracts finite all-stage geometry; branch-local
boundedness and an explicit principal free-energy local bound are then
converted to branch-deviation data before patching. -/
theorem
freeEnergyComplexAlongExhaustion_branchLocalViaDeviationRelCompact_directRange_patch_isCompact_latticeGraph
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
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      (∀ i : Fin geom.n, ∃ C : ℝ, ∀ m z
        (_hz : z ∈ Metric.ball (geom.center i : ℂ)
          (data.branchData.radius (geom.center i))),
        ‖Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (p.J : ℂ) z (p.β : ℂ) m‖ ≤ C) →
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchLocalViaDeviationRelCompact_directRange_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

end Ambient
end IsingModel
