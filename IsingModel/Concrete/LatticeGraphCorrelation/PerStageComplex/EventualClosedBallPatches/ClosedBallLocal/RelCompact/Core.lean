import IsingModel.Lattice
import IsingModel.AmbientComplexAnalyticity.AscoliData.ClosedBallConversions.BranchLocal
import IsingModel.AmbientComplexAnalyticity.CompactPatches.BranchRelCompact

namespace IsingModel
namespace Ambient

/-- **ℤ^d closed-ball branch local boundedness to relatively compact patch**:
closed-ball branch local bounds supply the underlying branch locally bounded
relative-compactness input directly through the closed-ball-to-branch-local
conversion. -/
theorem
freeEnergyComplexAlongExhaustion_closedBallBranchLocallyBoundedRelCompact_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (_hβ : 0 < p.β)
    (_hJ : 0 < p.J)
    {K : Set ℂ}
    (closedData :
      Ambient.LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K closedData.data)
    (closedBallLocal :
      Ambient.LeeYangClosedBallBranchLocallyBoundedAscoliData
        (IsingModel.latticeGraph d) Λ p K closedData geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i => closedData.data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (closedData.data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchLocallyBoundedRelCompact_patch
    (IsingModel.latticeGraph d) Λ p hBED hd closedData.data geom
    (Ambient.LeeYangClosedBallBranchLocallyBoundedAscoliData.toBranchLocallyBoundedData
      (IsingModel.latticeGraph d) Λ p K closedData geom closedBallLocal)

set_option linter.style.longLine false in
/-- **ℤ^d compact target to closed-ball branch local-boundedness patch input**:
compactness extracts the finite all-stage geometry from closed-ball branch
data; branch-family local boundedness then supplies the relative-compactness
patch input. -/
theorem
freeEnergyComplexAlongExhaustion_closedBallBranchLocallyBoundedRelCompact_patch_isCompact_latticeGraph
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
    (hpK : (p.h : ℂ) ∈ K)
    (closedData :
      Ambient.LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
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
    rcases Ambient.exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
        (IsingModel.latticeGraph d) Λ p hK hKsub hpK closedData.data with
      ⟨geom⟩
    exact ⟨geom, fun closedBallLocal =>
      freeEnergyComplexAlongExhaustion_closedBallBranchLocallyBoundedRelCompact_patch_latticeGraph
        d Λ p hBED hd hβ hJ closedData geom closedBallLocal⟩

end Ambient

end IsingModel
