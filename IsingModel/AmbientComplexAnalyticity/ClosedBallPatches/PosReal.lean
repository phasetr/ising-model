import IsingModel.AmbientComplexAnalyticity.ClosedBallPatches.EventualOverlap

/-!
# Closed-ball patches split — eventual-overlap via-local and pos-real direct-range patches

Part of the split closed-ball branch-deviation patches layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

set_option linter.style.longLine false in
/-- **Compact target to eventual-overlap closed-ball branch-deviation via-local
direct-range patch input**: compactness extracts finite all-stage geometry,
branch-deviation bounds are converted to branch-local boundedness using the
closed-ball principal free-energy bound, and eventual-overlap data supplies
selected overlap. -/
theorem
    freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchDeviationViaLocalRelCompact_directRange_patch_of_isCompact
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
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
        (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
          G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data,
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData
          G Λ p K closedEventualData geom →
        ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
            G Λ p K geom.n geom.center
            (fun i =>
              closedEventualData.pointwiseData.branchData.radius
                (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (closedEventualData.pointwiseData.branchData.radius
                  (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
      G Λ p hK hKsub hpK
        (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
          G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data with
    ⟨geom⟩
  exact ⟨geom, fun closedEventualDeviation =>
    freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchDeviationViaLocalRelCompact_directRange_patch
      G Λ p hBED hd hβ hJ closedEventualData geom closedEventualDeviation⟩

set_option linter.style.longLine false in
/-- **Positive-real compact target to direct-range closed-ball
branch-deviation patch input**: positive real ferromagnetic parameters
construct the closed-ball all-stage branch data, compactness extracts the
finite geometry, and closed-ball branch-deviation data then feeds the
direct-range route. -/
theorem
    freeEnergyComplexAlongExhaustion_posRealClosedBallDeviation_directRange_patch_of_isCompact
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
      freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_directRange_patch_of_isCompact
        G Λ p hBED hd hβ hJ hK hKsub hpK closedData with
    ⟨geom, hgeom⟩
  exact ⟨closedData, geom, hgeom⟩

set_option linter.style.longLine false in
/-- **Positive-real compact target to named via-local direct-range closed-ball
branch-deviation patch input**: positive real ferromagnetic parameters
construct the closed-ball all-stage branch data, compactness extracts the
finite geometry, and closed-ball branch-deviation data then feeds the named
via-local direct-range route. -/
theorem
    freeEnergyComplexAlongExhaustion_posRealClosedBallDeviationViaLocal_directRange_patch_of_isCompact
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
      freeEnergyComplexAlongExhaustion_closedBallBranchDeviationViaLocalRelCompact_directRange_patch_of_isCompact
        G Λ p hBED hd hβ hJ hK hKsub hpK closedData with
    ⟨geom, hgeom⟩
  exact ⟨closedData, geom, hgeom⟩


end Ambient
end IsingModel
