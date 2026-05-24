import IsingModel.AmbientComplexAnalyticity.AscoliData.ClosedBallConversions.BranchLocal

/-!
# Eventual-overlap closed-ball branch-local conversions

Conversions from eventual-overlap closed-ball branch-local data to ordinary
closed-ball branch-local and range-compactness packages.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

set_option linter.style.longLine false in
/-- Convert eventual-overlap closed-ball branch local boundedness into the
ordinary closed-ball branch locally bounded package by taking the coherent
selected-overlap field from the underlying pointwise-normalised
eventual-overlap data. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData.toClosedBallBranchLocallyBoundedData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data)
    (closedEventualLocal :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData
        G Λ p K closedEventualData geom) :
    LeeYangClosedBallBranchLocallyBoundedAscoliData G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData) geom where
  restricted := closedEventualLocal.restricted
  toFun_image_closed := closedEventualLocal.toFun_image_closed
  branch_bound := by
    simpa [LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData,
      LeeYangPointwiseNormalisedEventualOverlapBranchData.toAllStageData] using
      closedEventualLocal.branch_bound
  equicontinuous := closedEventualLocal.equicontinuous
  restrict_eq := by
    simpa [LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData,
      LeeYangPointwiseNormalisedEventualOverlapBranchData.toAllStageData] using
      closedEventualLocal.restrict_eq
  overlap_eventually := by
    intro i j
    simpa [LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData,
      LeeYangPointwiseNormalisedEventualOverlapBranchData.toAllStageData] using
      closedEventualData.pointwiseData.branchData.overlap_eventually
        (geom.center i) (geom.center j)

set_option linter.style.longLine false in
/-- Convert eventual-overlap closed-ball branch local boundedness directly
into relatively compact range data by first deriving the ordinary closed-ball
branch locally bounded package with its overlap field supplied from
eventual-overlap data. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData.toRangeRelCompactData_direct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data)
    (closedEventualLocal :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData
        G Λ p K closedEventualData geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K
        (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
          G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data geom :=
  LeeYangClosedBallBranchLocallyBoundedAscoliData.toRangeRelCompactData_direct
    G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData) geom
    (LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData.toClosedBallBranchLocallyBoundedData
      G Λ p K closedEventualData geom closedEventualLocal)

end Ambient

end IsingModel
