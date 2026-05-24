import IsingModel.AmbientComplexAnalyticity.AscoliData.ClosedBallConversions.ClosedBallDeviation

/-!
# Closed-ball branch-local conversions

Conversions from closed-ball branch-local boundedness to ordinary branch-local,
closed-ball deviation, and range compactness packages.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

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

end Ambient

end IsingModel
