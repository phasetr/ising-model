import IsingModel.AmbientComplexAnalyticity.AscoliData.ClosedBallConversions.EventualLocal

/-!
# Closed-ball deviation direct-route conversions

Direct-route aliases connecting closed-ball deviation, branch-local boundedness,
and relatively compact range data.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

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

end Ambient

end IsingModel
