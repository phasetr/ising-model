import IsingModel.AmbientComplexAnalyticity.ClosedBallPatches.RelCompact

/-!
# Closed-ball patches split — direct and direct-range closed-ball branch-deviation patches

Part of the split closed-ball branch-deviation patches layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

set_option linter.style.longLine false in
/-- **Compact target to direct closed-ball branch-deviation patch input**:
compactness extracts the finite all-stage geometry from closed-ball branch
data; closed-ball branch-deviation data then feeds the direct relatively compact
range route. -/
theorem
    freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_direct_patch_of_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
        G Λ p K closedData.data,
      LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
          G Λ p K closedData geom →
        ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
            G Λ p K geom.n geom.center
            (fun i => closedData.data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (closedData.data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
      G Λ p hK hKsub hpK closedData.data with
    ⟨geom⟩
  exact ⟨geom, fun closedBallDeviation =>
    freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_direct_patch
      G Λ p hBED hd hβ hJ closedData geom closedBallDeviation⟩

set_option linter.style.longLine false in
/-- **Positive-real compact target to direct closed-ball branch-deviation patch
input**: positive real ferromagnetic parameters construct the closed-ball
all-stage branch data, compactness extracts the finite geometry, and
closed-ball branch-deviation data then feeds the direct range route. -/
theorem
    freeEnergyComplexAlongExhaustion_posRealClosedBallDeviation_direct_patch_of_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K) :
    ∃ closedData :
        LeeYangClosedBallPointwiseNormalisedAllStageBranchData
          G Λ (p.J : ℂ) (p.β : ℂ),
      ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
          G Λ p K closedData.data,
        LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
            G Λ p K closedData geom →
          ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
              G Λ p K geom.n geom.center
              (fun i => closedData.data.branchData.radius (geom.center i)),
            ∃ g : ℂ → ℂ,
              (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
                (Metric.ball (geom.center i : ℂ)
                  (closedData.data.branchData.radius (geom.center i)))) ∧
              DifferentiableOn ℂ g K ∧
              g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_leeYangClosedBallPointwiseNormalisedAllStageBranchData_of_positive_real
      G Λ hβ hJ with
    ⟨closedData⟩
  rcases
      freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_direct_patch_of_isCompact
        G Λ p hBED hd hβ hJ hK hKsub hpK closedData with
    ⟨geom, hgeom⟩
  exact ⟨closedData, geom, hgeom⟩

set_option linter.style.longLine false in
/-- **Closed-ball branch-deviation to direct-range relatively compact patch**:
closed-ball branch-deviation data is converted directly to relatively compact
range data through the direct closed-ball branch-local route, then fed to the
all-stage relatively compact range patch endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_directRange_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallDeviation :
      LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
        G Λ p K closedData geom) :
    ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
        G Λ p K geom.n geom.center
        (fun i => closedData.data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (closedData.data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch
    G Λ p hBED hd closedData.data geom
    (LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData.toRangeRelCompactData_direct
      G Λ p hBED hβ hJ K closedData geom closedBallDeviation)

set_option linter.style.longLine false in
/-- **Compact target to direct-range closed-ball branch-deviation patch input**:
compactness extracts the finite all-stage geometry from closed-ball branch
data; closed-ball branch-deviation data then feeds the direct-range relatively
compact route. -/
theorem
    freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_directRange_patch_of_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
        G Λ p K closedData.data,
      LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
          G Λ p K closedData geom →
        ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
            G Λ p K geom.n geom.center
            (fun i => closedData.data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (closedData.data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
      G Λ p hK hKsub hpK closedData.data with
    ⟨geom⟩
  exact ⟨geom, fun closedBallDeviation =>
    freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_directRange_patch
      G Λ p hBED hd hβ hJ closedData geom closedBallDeviation⟩


end Ambient
end IsingModel
