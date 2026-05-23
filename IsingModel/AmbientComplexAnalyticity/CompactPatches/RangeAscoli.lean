import IsingModel.AmbientComplexAnalyticity.CompactPatches.GeometryCOpen

/-!
# Range compact-open and Ascoli patch wrappers

This module contains range-closure, relatively compact range, and
basic all-stage Ascoli wrappers.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Pointwise-normalised all-stage range-closure compact-open data to a
compact real-cover patch**: compactness of the closure of the selected
stage-restriction range supplies the compact-open carrier membership required
by the packaged compact-open patch bridge. -/
theorem freeEnergyComplexAlongExhaustion_allStageRangeClosureCOpenData_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (rangeClosure :
      LeeYangPointwiseNormAllStageCompactRealRangeClosureCOpenData
        G Λ p K data geom) :
    ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
        G Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_allStageCOpenData_patch
    G Λ p hBED hd data geom
    (LeeYangPointwiseNormAllStageCompactRealRangeClosureCOpenData.toCOpenData
      G Λ p K data geom rangeClosure)

/-- **Compact target to all-stage range-closure compact-open patch input**:
compactness of `K` extracts the finite all-stage geometry, after which
compactness of each closure of the actual stage-restriction range, restriction
identities, and coherent overlap equality suffice for the compact real-cover
patch endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeClosureCOpenData_patch_of_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data,
      LeeYangPointwiseNormAllStageCompactRealRangeClosureCOpenData
          G Λ p K data geom →
        ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
            G Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
      G Λ p hK hKsub hpK data with
    ⟨geom⟩
  exact ⟨geom, fun rangeClosure =>
    freeEnergyComplexAlongExhaustion_allStageRangeClosureCOpenData_patch
      G Λ p hBED hd data geom rangeClosure⟩

/-- **Pointwise-normalised all-stage relatively compact range data to a
compact real-cover patch**: if the selected stage-restriction range lies in a
compact compact-open carrier, then the range closure is compact and the
range-closure compact-open patch bridge applies. -/
theorem freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (relCompact :
      LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
        G Λ p K data geom) :
    ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
        G Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_allStageRangeClosureCOpenData_patch
    G Λ p hBED hd data geom
    (LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData.toRangeClosureData
      G Λ p K data geom relCompact)

/-- **Compact target to all-stage relatively compact range patch input**:
compactness of `K` extracts the finite all-stage geometry, after which compact
carriers containing the selected restriction ranges, restriction identities,
and coherent overlap equality suffice for the compact real-cover patch
endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch_of_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data,
      LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
          G Λ p K data geom →
        ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
            G Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
      G Λ p hK hKsub hpK data with
    ⟨geom⟩
  exact ⟨geom, fun relCompact =>
    freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch
      G Λ p hBED hd data geom relCompact⟩

/-- **Pointwise-normalised all-stage Arzelà-Ascoli data to a compact real-cover
patch**: compactness of the pointwise function-space image plus equicontinuity
on the selected all-stage compact finite geometry supply compact-open
compactness via Arzelà-Ascoli, and the resulting compact-open package feeds the
compact real-cover patch bridge. -/
theorem freeEnergyComplexAlongExhaustion_allStageAscoliData_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (ascoli : LeeYangPointwiseNormAllStageCompactRealAscoliData
      G Λ p K data geom) :
    ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
        G Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_allStageCOpenData_patch
    G Λ p hBED hd data geom
    (LeeYangPointwiseNormAllStageCompactRealAscoliData.toCOpenData
      G Λ p K data geom ascoli)

/-- **Compact target to all-stage Arzelà-Ascoli patch input**: compactness of
`K` extracts the finite all-stage geometry, after which compactness of the
pointwise function-space image, equicontinuity, restriction identities, and
coherent overlap equality for that geometry suffice to obtain the compact
real-cover patch endpoint. -/
theorem freeEnergyComplexAlongExhaustion_allStageAscoliData_patch_of_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data,
      LeeYangPointwiseNormAllStageCompactRealAscoliData G Λ p K data geom →
        ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
            G Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
      G Λ p hK hKsub hpK data with
    ⟨geom⟩
  exact ⟨geom, fun ascoli =>
    freeEnergyComplexAlongExhaustion_allStageAscoliData_patch
      G Λ p hBED hd data geom ascoli⟩

end Ambient

end IsingModel
