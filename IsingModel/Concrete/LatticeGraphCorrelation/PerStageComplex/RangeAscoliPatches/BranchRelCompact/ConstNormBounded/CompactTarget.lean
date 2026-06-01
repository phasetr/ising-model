import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.RangeAscoliPatches.BranchRelCompact.ConstNormBounded.Core

/-!
# ℤ^d branch constant norm-bounded relatively compact compact-target wrappers

This module contains the compact-target branch constant norm-bounded relatively
compact wrapper endpoint.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d compact target to branch constant norm-bounded relatively compact
patch input**: compactness of `K` extracts the finite all-stage geometry, and
branch constant norm-bounded data supplies the relative-compactness input. -/
theorem
    freeEnergyComplexAlongExhaustion_branchConstNormBoundedRelCompact_patch_isCompact_latticeGraph
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
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchConstNormBoundedAscoliData
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
  Ambient.freeEnergyComplexAlongExhaustion_branchConstNormBoundedRelCompact_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

end Ambient

end IsingModel
