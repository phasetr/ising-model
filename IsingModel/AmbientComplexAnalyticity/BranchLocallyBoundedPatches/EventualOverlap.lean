import IsingModel.AmbientComplexAnalyticity.BranchLocallyBoundedPatches.DirectRange

/-!
# Branch locally bounded patches split — eventual-overlap closed-ball branch-local patches

Part of the split branch-locally-bounded patches layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

set_option linter.style.longLine false in
/-- **Closed-ball branch-local data to direct-range patch via branch
deviation**: branch-local boundedness and the automatic closed-ball principal
free-energy bound are converted to closed-ball branch-deviation data before
feeding the directRange relatively compact route. -/
theorem
    freeEnergyComplexAlongExhaustion_closedBallBranchLocalViaDeviationRelCompact_directRange_patch
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
    (closedBallLocal :
      LeeYangClosedBallBranchLocallyBoundedAscoliData
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
    (LeeYangClosedBallBranchLocallyBoundedAscoliData.toRangeRelCompactData_viaDeviation_direct
      G Λ p hBED hβ hJ K closedData geom closedBallLocal)

set_option linter.style.longLine false in
/-- **Compact target to closed-ball branch-local via-deviation direct-range
patch input**: compactness extracts finite all-stage geometry; branch-local
boundedness is converted to closed-ball branch-deviation data using the
automatic closed-ball principal free-energy bound, then routed through
directRange relative compactness. -/
theorem
    freeEnergyComplexAlongExhaustion_closedBallBranchLocalViaDeviationRelCompact_directRange_patch_of_isCompact
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
      LeeYangClosedBallBranchLocallyBoundedAscoliData
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
  exact ⟨geom, fun closedBallLocal =>
    freeEnergyComplexAlongExhaustion_closedBallBranchLocalViaDeviationRelCompact_directRange_patch
      G Λ p hBED hd hβ hJ closedData geom closedBallLocal⟩

set_option linter.style.longLine false in
/-- **Positive-real compact target to closed-ball branch-local via-deviation
direct-range patch input**: positive real ferromagnetic parameters construct
closed-ball all-stage branch data; compactness extracts finite geometry; branch
local boundedness is converted through closed-ball branch-deviation data before
directRange patching. -/
theorem
    freeEnergyComplexAlongExhaustion_posRealClosedBallBranchLocalViaDeviation_directRange_patch_of_isCompact
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
        LeeYangClosedBallBranchLocallyBoundedAscoliData
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
      freeEnergyComplexAlongExhaustion_closedBallBranchLocalViaDeviationRelCompact_directRange_patch_of_isCompact
        G Λ p hBED hd hβ hJ hK hKsub hpK closedData with
    ⟨geom, hgeom⟩
  exact ⟨closedData, geom, hgeom⟩

set_option linter.style.longLine false in
/-- **Eventual-overlap closed-ball branch local boundedness to direct-range
relatively compact patch**: closed-ball branch local boundedness data is
converted directly to relatively compact range data, with coherent
selected-overlap equality supplied by the pointwise-normalised
eventual-overlap package. -/
theorem
    freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchLocallyBoundedRelCompact_directRange_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data)
    (closedEventualLocal :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData
        G Λ p K closedEventualData geom) :
    ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
        G Λ p K geom.n geom.center
        (fun i =>
          closedEventualData.pointwiseData.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (closedEventualData.pointwiseData.branchData.radius
              (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch
    G Λ p hBED hd
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data geom
    (LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData.toRangeRelCompactData_direct
      G Λ p K closedEventualData geom closedEventualLocal)


end Ambient
end IsingModel
