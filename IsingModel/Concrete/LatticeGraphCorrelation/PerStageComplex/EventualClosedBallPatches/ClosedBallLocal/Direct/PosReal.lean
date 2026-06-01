import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.EventualClosedBallPatches.ClosedBallLocal.Direct.Core

namespace IsingModel
namespace Ambient

set_option linter.style.longLine false in
/-- **ℤ^d positive-real compact target to direct closed-ball branch
local-boundedness patch input**: positive real ferromagnetic parameters
construct the closed-ball all-stage branch data, compactness extracts finite
geometry, and branch local boundedness feeds the direct relative-compactness
input. -/
theorem
freeEnergyComplexAlongExhaustion_posRealClosedBallBranchLocallyBounded_direct_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K) :
    ∃ closedData :
        Ambient.LeeYangClosedBallPointwiseNormalisedAllStageBranchData
          (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ),
      ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
          (IsingModel.latticeGraph d) Λ p K closedData.data,
        Ambient.LeeYangClosedBallBranchLocallyBoundedAscoliData
            (IsingModel.latticeGraph d) Λ p K closedData geom →
          ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
              (IsingModel.latticeGraph d) Λ p K geom.n geom.center
              (fun i => closedData.data.branchData.radius (geom.center i)),
            ∃ g : ℂ → ℂ,
              (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
                (Metric.ball (geom.center i : ℂ)
                  (closedData.data.branchData.radius (geom.center i)))) ∧
              DifferentiableOn ℂ g K ∧
              g (p.h : ℂ) =
                ((Ambient.freeEnergyInfinite
                  (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  by
    rcases Ambient.exists_leeYangClosedBallPointwiseNormalisedAllStageBranchData_of_positive_real
        (IsingModel.latticeGraph d) Λ hβ hJ with
      ⟨closedData⟩
    rcases
        freeEnergyComplexAlongExhaustion_closedBallBranchLocallyBoundedRelCompact_direct_patch_isCompact_latticeGraph
          d Λ p hBED hd hK hKsub hpK closedData with
      ⟨geom, hgeom⟩
    exact ⟨closedData, geom, hgeom⟩

end Ambient

end IsingModel
