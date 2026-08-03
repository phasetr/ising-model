import IsingModel.AmbientComplexAnalyticity.ClosedBallPatches.Direct

/-!
# Closed-ball patches split — via-local relatively-compact direct-range patches

Part of the split closed-ball branch-deviation patches layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Closed-ball branch-deviation data through the named branch-local
direct-range patch route** (compatibility alias): closed-ball branch-deviation
data is converted to relatively compact range data through the named via-local
route, then fed to the all-stage relatively compact range patch endpoint.

The statement is identical to
`freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_direct_patch`,
which owns the proof (Issue #4854); this name is a documented compatibility
alias and forwards to it.  The via-local naming records the branch-local
intermediate, not a distinct proof: the data-layer conversion
`toRangeRelCompactData_viaLocal_direct` used previously here was a verbatim
forward to the `toRangeRelCompactData_closedBallLocal_direct` used by the owner,
and it was retired in Issue #4869 once this alias stopped consuming it.
The name is kept because the via-local route is cited by `docs/index.md`,
`tex/proof-guide.tex`, and the ℤ^d wrappers in
`PerStageComplex/EventualClosedBallPatches/ClosedBallDeviation.lean`. -/
theorem
    freeEnergyComplexAlongExhaustion_closedBallBranchDeviationViaLocalRelCompact_directRange_patch
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
  freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_direct_patch
    G Λ p hBED hd hβ hJ closedData geom closedBallDeviation

set_option linter.style.longLine false in
/-- **Compact target to named via-local closed-ball branch-deviation patch
input**: compactness extracts the finite all-stage geometry from closed-ball
branch data; closed-ball branch-deviation data then feeds the named via-local
relatively compact route. -/
theorem
    freeEnergyComplexAlongExhaustion_closedBallBranchDeviationViaLocalRelCompact_directRange_patch_of_isCompact
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
    freeEnergyComplexAlongExhaustion_closedBallBranchDeviationViaLocalRelCompact_directRange_patch
      G Λ p hBED hd hβ hJ closedData geom closedBallDeviation⟩

set_option linter.style.longLine false in
/-- **Eventual-overlap closed-ball branch-deviation data to direct-range
relatively compact patch**: closed-ball branch-deviation data is converted
directly to relatively compact range data, with coherent selected-overlap
equality supplied by the pointwise-normalised eventual-overlap package. -/
theorem
    freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchDeviationRelCompact_directRange_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data)
    (closedEventualDeviation :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData
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
    (LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData.toRangeRelCompactData_direct
      G Λ p hBED hβ hJ K closedEventualData geom closedEventualDeviation)

set_option linter.style.longLine false in
/-- **Compact target to eventual-overlap closed-ball branch-deviation
direct-range patch input**: compactness extracts finite all-stage geometry
from the closed-ball all-stage data underlying the pointwise-normalised
eventual-overlap package; the eventual-overlap package then supplies the
selected overlap field for the closed-ball branch-deviation route. -/
theorem
    freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchDeviationRelCompact_directRange_patch_of_isCompact
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
    freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchDeviationRelCompact_directRange_patch
      G Λ p hBED hd hβ hJ closedEventualData geom closedEventualDeviation⟩


end Ambient
end IsingModel
