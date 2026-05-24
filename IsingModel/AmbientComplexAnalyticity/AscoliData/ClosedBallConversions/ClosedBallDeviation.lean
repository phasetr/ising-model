import IsingModel.AmbientComplexAnalyticity.AscoliData.BranchConversions

/-!
# Closed-ball deviation conversions

Conversions from closed-ball branch-deviation Ascoli data to ordinary
branch-deviation, range compactness, and branch-local boundedness packages.
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

end Ambient

end IsingModel
