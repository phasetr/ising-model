import IsingModel.AmbientComplexAnalyticity.AscoliData.BranchConversions

/-!
# Ambient complex analyticity Ascoli closed-ball conversions

Mechanical child split from `AmbientComplexAnalyticity/AscoliData.lean`.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- Convert closed-ball branch-deviation Ascoli data into the PR #2744
branch-deviation package by supplying the principal finite-volume free-energy
bound from the closed-ball Lee-Yang local boundedness theorem. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData.toDeviationData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallDeviation :
      LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
        G Λ p K closedData geom) :
    LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
      G Λ p K closedData.data geom where
  restricted := closedBallDeviation.restricted
  toFun_image_closed := closedBallDeviation.toFun_image_closed
  freeEnergy_bound := fun i => by
    rcases exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_on_ball
        G Λ hBED hβ hJ (closedData.closedBall_subset (geom.center i)) with
      ⟨C, hC⟩
    refine ⟨C + Real.pi, ?_⟩
    intro m z hz
    exact hC m z hz
  branch_deviation_bound := closedBallDeviation.branch_deviation_bound
  equicontinuous := closedBallDeviation.equicontinuous
  restrict_eq := closedBallDeviation.restrict_eq
  overlap_eventually := closedBallDeviation.overlap_eventually

/-- Convert closed-ball branch-deviation Ascoli data into relatively compact
range data by first supplying the automatic principal free-energy bound. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData.toRangeRelCompactData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallDeviation :
      LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
        G Λ p K closedData geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K closedData.data geom :=
  LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData.toRangeRelCompactData
    G Λ p K closedData.data geom
    (LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData.toDeviationData
      G Λ p hBED hβ hJ K closedData geom closedBallDeviation)

namespace LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData

/-- Convert closed-ball branch-deviation Ascoli data into closed-ball branch
locally bounded Ascoli data by combining the automatic closed-ball principal
free-energy bound with the supplied branch-deviation bound. -/
noncomputable def toClosedBallBranchLocallyBoundedData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallDeviation :
      LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
        G Λ p K closedData geom) :
    LeeYangClosedBallBranchLocallyBoundedAscoliData
      G Λ p K closedData geom where
  restricted := closedBallDeviation.restricted
  toFun_image_closed := closedBallDeviation.toFun_image_closed
  branch_bound := fun i => by
    rcases closedBallDeviation.branch_deviation_bound i with ⟨D, hD⟩
    rcases exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_on_ball
        G Λ hBED hβ hJ (closedData.closedBall_subset (geom.center i)) with
      ⟨C, hC⟩
    refine ⟨D + (C + Real.pi), ?_⟩
    intro m z hz
    let F := freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m
    calc
      ‖closedData.data.branchData.branchFamily (geom.center i) m z‖ =
          ‖(closedData.data.branchData.branchFamily (geom.center i) m z - F) + F‖ := by
            rw [sub_add_cancel]
      _ ≤ ‖closedData.data.branchData.branchFamily (geom.center i) m z - F‖ + ‖F‖ :=
          norm_add_le _ _
      _ ≤ D + (C + Real.pi) := add_le_add (hD m z hz) (hC m z hz)
  equicontinuous := closedBallDeviation.equicontinuous
  restrict_eq := closedBallDeviation.restrict_eq
  overlap_eventually := closedBallDeviation.overlap_eventually

end LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData

namespace LeeYangClosedBallBranchLocallyBoundedAscoliData

/-- Convert closed-ball branch local boundedness into the underlying
pointwise-normalised branch locally bounded Ascoli package.  This direct
conversion forgets only the closed-ball containment data and keeps the same
restriction, boundedness, equicontinuity, and overlap inputs. -/
noncomputable def toBranchLocallyBoundedData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallLocal :
      LeeYangClosedBallBranchLocallyBoundedAscoliData
        G Λ p K closedData geom) :
    LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData
      G Λ p K closedData.data geom where
  restricted := closedBallLocal.restricted
  toFun_image_closed := closedBallLocal.toFun_image_closed
  branch_bound := closedBallLocal.branch_bound
  equicontinuous := closedBallLocal.equicontinuous
  restrict_eq := closedBallLocal.restrict_eq
  overlap_eventually := closedBallLocal.overlap_eventually

/-- Convert closed-ball branch local boundedness directly into relatively
compact range data by forgetting the closed-ball containment data and reusing
the underlying branch locally bounded Ascoli conversion. -/
noncomputable def toRangeRelCompactData_direct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallLocal :
      LeeYangClosedBallBranchLocallyBoundedAscoliData
        G Λ p K closedData geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K closedData.data geom :=
  LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData.toRangeRelCompactData
    G Λ p K closedData.data geom
    (toBranchLocallyBoundedData
      G Λ p K closedData geom closedBallLocal)

/-- Convert closed-ball branch local boundedness into closed-ball
branch-deviation data.  The deviation estimate follows from the local branch
bound and the closed-ball Lee-Yang principal free-energy bound. -/
noncomputable def toClosedBallDeviationData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallLocal :
      LeeYangClosedBallBranchLocallyBoundedAscoliData
        G Λ p K closedData geom) :
    LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
      G Λ p K closedData geom where
  restricted := closedBallLocal.restricted
  toFun_image_closed := closedBallLocal.toFun_image_closed
  branch_deviation_bound := fun i => by
    rcases closedBallLocal.branch_bound i with ⟨B, hB⟩
    rcases exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_on_ball
        G Λ hBED hβ hJ (closedData.closedBall_subset (geom.center i)) with
      ⟨C, hC⟩
    refine ⟨B + (C + Real.pi), ?_⟩
    intro m z hz
    calc
      ‖closedData.data.branchData.branchFamily (geom.center i) m z
          - freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m‖
          ≤ ‖closedData.data.branchData.branchFamily (geom.center i) m z‖ +
              ‖freeEnergyComplexAlongExhaustion
                G Λ (p.J : ℂ) z (p.β : ℂ) m‖ := by
            exact norm_sub_le _ _
      _ ≤ B + (C + Real.pi) := by
            exact add_le_add (hB m z hz) (hC m z hz)
  equicontinuous := closedBallLocal.equicontinuous
  restrict_eq := closedBallLocal.restrict_eq
  overlap_eventually := closedBallLocal.overlap_eventually

/-- Convert closed-ball branch local boundedness into relatively compact range
data by deriving the closed-ball branch-deviation package first. -/
noncomputable def toRangeRelCompactData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallLocal :
      LeeYangClosedBallBranchLocallyBoundedAscoliData
        G Λ p K closedData geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K closedData.data geom :=
  LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData.toRangeRelCompactData
    G Λ p hBED hβ hJ K closedData geom
    (toClosedBallDeviationData
      G Λ p hBED hβ hJ K closedData geom closedBallLocal)

end LeeYangClosedBallBranchLocallyBoundedAscoliData

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

namespace LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData

/-- Convert closed-ball branch-deviation Ascoli data into relatively compact
range data through the direct closed-ball branch-local route. -/
noncomputable def toRangeRelCompactData_closedBallLocal_direct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallDeviation :
      LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
        G Λ p K closedData geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K closedData.data geom :=
  LeeYangClosedBallBranchLocallyBoundedAscoliData.toRangeRelCompactData_direct
    G Λ p K closedData geom
    (toClosedBallBranchLocallyBoundedData
      G Λ p hBED hβ hJ K closedData geom closedBallDeviation)

/-- Direct-route alias for the closed-ball branch-deviation Ascoli data to
relatively compact range data conversion.  This keeps the public name parallel
to `LeeYangClosedBallBranchLocallyBoundedAscoliData.toRangeRelCompactData_direct`
while using the same branch-local route. -/
noncomputable def toRangeRelCompactData_direct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallDeviation :
      LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
        G Λ p K closedData geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K closedData.data geom :=
  toRangeRelCompactData_closedBallLocal_direct
    G Λ p hBED hβ hJ K closedData geom closedBallDeviation

set_option linter.style.longLine false in
/-- Named via-local direct-route alias for the closed-ball branch-deviation
Ascoli data to relatively compact range data conversion.  This restates the
existing closed-ball branch-local route with the intermediate route exposed.
-/
noncomputable def toRangeRelCompactData_viaLocal_direct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallDeviation :
      LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
        G Λ p K closedData geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K closedData.data geom :=
  toRangeRelCompactData_closedBallLocal_direct
    G Λ p hBED hβ hJ K closedData geom closedBallDeviation

end LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData

set_option linter.style.longLine false in
/-- Convert closed-ball branch local boundedness into relatively compact range
data through the direct closed-ball branch-deviation route.  This keeps the
closed-ball branch-deviation boundary visible while using the directRange
relative-compactness conversion. -/
noncomputable def
    LeeYangClosedBallBranchLocallyBoundedAscoliData.toRangeRelCompactData_viaDeviation_direct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallLocal :
      LeeYangClosedBallBranchLocallyBoundedAscoliData
        G Λ p K closedData geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K closedData.data geom :=
  LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData.toRangeRelCompactData_direct
    G Λ p hBED hβ hJ K closedData geom
    (LeeYangClosedBallBranchLocallyBoundedAscoliData.toClosedBallDeviationData
      G Λ p hBED hβ hJ K closedData geom closedBallLocal)

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
