import IsingModel.AmbientComplexAnalyticity.BranchDeviationPatches

/-!
# Closed-ball patches split — relatively-compact and direct closed-ball branch-deviation patches

Part of the split closed-ball branch-deviation patches layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Closed-ball branch-deviation data to a relatively compact range patch**:
closed-ball all-stage branch data supplies the Lee-Yang local compactness
needed to bound the principal finite-volume free energies on each selected
ball.  The only remaining local-boundedness input is the uniform deviation of
the selected branch from that principal value.

This statement is identical to the one owned by
`freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_direct_patch`
below, but this theorem is deliberately outside the Issue #4854
canonicalization pilot and keeps its own proof: it reaches the conclusion by
the independent `toDeviationData` route into
`freeEnergyComplexAlongExhaustion_branchDeviationRelCompact_patch`, and it has
its own in-repo consumers. -/
theorem freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_patch
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
  freeEnergyComplexAlongExhaustion_branchDeviationRelCompact_patch
    G Λ p hBED hd closedData.data geom
    (LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData.toDeviationData
      G Λ p hBED hβ hJ K closedData geom closedBallDeviation)

/-- **Compact target to closed-ball branch-deviation relatively compact patch
input**: compactness of `K` extracts the finite all-stage geometry from the
underlying closed-ball branch data; the closed-ball branch-deviation data then
supplies the relative-compactness input with the principal free-energy bound
filled in automatically. -/
theorem
    freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_patch_of_isCompact
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
    freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_patch
      G Λ p hBED hd hβ hJ closedData geom closedBallDeviation⟩

/-- **Positive-real compact target to closed-ball branch-deviation relatively
compact patch input**: positive real ferromagnetic parameters construct the
closed-ball pointwise-normalised all-stage branch data, compactness of `K`
extracts the finite geometry, and closed-ball branch-deviation data then feeds
the PR #2745 closed-ball relative-compactness bridge. -/
theorem
    freeEnergyComplexAlongExhaustion_posRealClosedBallDeviation_patch_of_isCompact
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
      freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_patch_of_isCompact
        G Λ p hBED hd hβ hJ hK hKsub hpK closedData with
    ⟨geom, hgeom⟩
  exact ⟨closedData, geom, hgeom⟩

open LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData in
/-- **Closed-ball branch-deviation to direct relatively compact patch**:
closed-ball branch-deviation data is first converted to relatively compact
range data through the direct closed-ball branch-local route, then fed to the
all-stage relatively compact range patch endpoint.

This theorem owns the proof for the three declarations in the scope of the
Issue #4854 canonicalization pilot.  The two other pilot declarations are
documented compatibility aliases that forward here:
`freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_directRange_patch`
(`ClosedBallPatches/Direct.lean`) and
`freeEnergyComplexAlongExhaustion_closedBallBranchDeviationViaLocalRelCompact_directRange_patch`
(`ClosedBallPatches/ViaLocal.lean`).  Their data-layer conversions
`toRangeRelCompactData_direct` and `toRangeRelCompactData_viaLocal_direct` are
verbatim forwards to the `toRangeRelCompactData_closedBallLocal_direct` used
below, so these three names always denoted the same proof route under
different published names, never independent proofs.

The pilot covers three of the four declarations that share this statement:
`freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_patch`
above in this file has the identical statement as well, but is deliberately
excluded because it proves it by an independent route (`toDeviationData` into
`freeEnergyComplexAlongExhaustion_branchDeviationRelCompact_patch`) and has
its own in-repo consumers. -/
theorem freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_direct_patch
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
    (toRangeRelCompactData_closedBallLocal_direct
      G Λ p hBED hβ hJ K closedData geom closedBallDeviation)


end Ambient
end IsingModel
