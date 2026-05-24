import IsingModel.AmbientComplexAnalyticity.AscoliData.ClosedBallConversions.DeviationDirect

/-!
# Eventual-overlap closed-ball deviation conversions

Conversions between eventual-overlap closed-ball branch-deviation and
branch-local packages, including direct range-compactness routes.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

set_option linter.style.longLine false in
/-- Convert eventual-overlap closed-ball branch-deviation data into the
ordinary closed-ball branch-deviation package by taking the coherent
selected-overlap field from the underlying pointwise-normalised
eventual-overlap data. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData.toClosedBallBranchDeviationData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data)
    (closedEventualDeviation :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData
        G Λ p K closedEventualData geom) :
    LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
      G Λ p K
        (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
          G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData) geom where
  restricted := closedEventualDeviation.restricted
  toFun_image_closed := closedEventualDeviation.toFun_image_closed
  branch_deviation_bound := by
    simpa [LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData,
      LeeYangPointwiseNormalisedEventualOverlapBranchData.toAllStageData] using
      closedEventualDeviation.branch_deviation_bound
  equicontinuous := closedEventualDeviation.equicontinuous
  restrict_eq := by
    simpa [LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData,
      LeeYangPointwiseNormalisedEventualOverlapBranchData.toAllStageData] using
      closedEventualDeviation.restrict_eq
  overlap_eventually := by
    intro i j
    simpa [LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData,
      LeeYangPointwiseNormalisedEventualOverlapBranchData.toAllStageData] using
      closedEventualData.pointwiseData.branchData.overlap_eventually
        (geom.center i) (geom.center j)

set_option linter.style.longLine false in
/-- Convert eventual-overlap closed-ball branch-deviation data directly into
relatively compact range data by first deriving the ordinary closed-ball
branch-deviation package with its overlap field supplied from
eventual-overlap data. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData.toRangeRelCompactData_direct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data)
    (closedEventualDeviation :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData
        G Λ p K closedEventualData geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K
        (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
          G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data geom :=
  LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData.toRangeRelCompactData_direct
    G Λ p hBED hβ hJ K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData) geom
    (LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData.toClosedBallBranchDeviationData
      G Λ p K closedEventualData geom closedEventualDeviation)

set_option linter.style.longLine false in
/-- Convert eventual-overlap closed-ball branch-local data into the
eventual-overlap closed-ball branch-deviation package by combining the
explicit branch bound with the automatic closed-ball principal free-energy
bound.  The selected-overlap field is still left to the eventual-overlap
package consumed by the downstream conversion. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData.toClosedBallBranchDeviationData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data)
    (closedEventualLocal :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData
        G Λ p K closedEventualData geom) :
    LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData
      G Λ p K closedEventualData geom where
  restricted := closedEventualLocal.restricted
  toFun_image_closed := closedEventualLocal.toFun_image_closed
  branch_deviation_bound := fun i => by
    rcases closedEventualLocal.branch_bound i with ⟨B, hB⟩
    rcases exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_on_ball
        G Λ hBED hβ hJ (closedEventualData.closedBall_subset (geom.center i)) with
      ⟨C, hC⟩
    refine ⟨B + (C + Real.pi), ?_⟩
    intro m z hz
    calc
      ‖closedEventualData.pointwiseData.branchData.branchFamily (geom.center i) m z
          - freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m‖
          ≤ ‖closedEventualData.pointwiseData.branchData.branchFamily (geom.center i) m z‖ +
              ‖freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m‖ := by
            exact norm_sub_le _ _
      _ ≤ B + (C + Real.pi) := by
            exact add_le_add (hB m z hz) (hC m z hz)
  equicontinuous := closedEventualLocal.equicontinuous
  restrict_eq := closedEventualLocal.restrict_eq

set_option linter.style.longLine false in
/-- Convert eventual-overlap closed-ball branch-local data to relatively
compact range data through the branch-deviation route.  This records the
triangle-inequality path parallel to the ordinary closed-ball branch-local
conversion, while the selected overlap is supplied by eventual-overlap data. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData.toRangeRelCompactData_viaDeviation_direct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
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
  LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData.toRangeRelCompactData_direct
    G Λ p hBED hβ hJ K closedEventualData geom
    (LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData.toClosedBallBranchDeviationData
      G Λ p hBED hβ hJ K closedEventualData geom closedEventualLocal)

set_option linter.style.longLine false in
/-- Convert eventual-overlap closed-ball branch-deviation data into the
eventual-overlap closed-ball branch-local package by combining the supplied
deviation bound with the automatic closed-ball principal free-energy bound.
The selected-overlap field is still supplied only by the eventual-overlap data
when the downstream ordinary closed-ball branch-local package is formed. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData.toClosedBallBranchLocallyBoundedData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data)
    (closedEventualDeviation :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData
        G Λ p K closedEventualData geom) :
    LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData
      G Λ p K closedEventualData geom where
  restricted := closedEventualDeviation.restricted
  toFun_image_closed := closedEventualDeviation.toFun_image_closed
  branch_bound := fun i => by
    rcases closedEventualDeviation.branch_deviation_bound i with ⟨D, hD⟩
    rcases exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_on_ball
        G Λ hBED hβ hJ (closedEventualData.closedBall_subset (geom.center i)) with
      ⟨C, hC⟩
    refine ⟨D + (C + Real.pi), ?_⟩
    intro m z hz
    let F := freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m
    calc
      ‖closedEventualData.pointwiseData.branchData.branchFamily (geom.center i) m z‖ =
          ‖(closedEventualData.pointwiseData.branchData.branchFamily (geom.center i) m z - F)
              + F‖ := by
            rw [sub_add_cancel]
      _ ≤ ‖closedEventualData.pointwiseData.branchData.branchFamily (geom.center i) m z - F‖ +
            ‖F‖ := norm_add_le _ _
      _ ≤ D + (C + Real.pi) := add_le_add (hD m z hz) (hC m z hz)
  equicontinuous := closedEventualDeviation.equicontinuous
  restrict_eq := closedEventualDeviation.restrict_eq

set_option linter.style.longLine false in
/-- Convert eventual-overlap closed-ball branch-deviation data to relatively
compact range data through the branch-local route.  This records the closed-ball
triangle-inequality route from deviation bounds to branch-local boundedness,
with selected overlap supplied downstream by eventual-overlap data. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData.toRangeRelCompactData_viaLocal_direct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data)
    (closedEventualDeviation :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData
        G Λ p K closedEventualData geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K
        (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
          G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data geom :=
  LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData.toRangeRelCompactData_direct
    G Λ p K closedEventualData geom
    (LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData.toClosedBallBranchLocallyBoundedData
      G Λ p hBED hβ hJ K closedEventualData geom closedEventualDeviation)

end Ambient

end IsingModel
