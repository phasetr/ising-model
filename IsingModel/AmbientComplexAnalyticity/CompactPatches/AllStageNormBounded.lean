import IsingModel.AmbientComplexAnalyticity.CompactPatches.RangeAscoli

/-!
# Closed-product and range-norm Ascoli patch wrappers

This module contains closed-product, norm-bounded, and range norm-bounded
all-stage Ascoli wrappers.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Pointwise-normalised all-stage closed-product Ascoli data to a compact
real-cover patch**: compact pointwise target sets plus closedness of the
pointwise function-space image and equicontinuity supply the Ascoli data, which
then feeds the compact real-cover patch bridge. -/
theorem freeEnergyComplexAlongExhaustion_allStageClosedProductAscoliData_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (closedProduct :
      LeeYangPointwiseNormAllStageCompactRealClosedProductAscoliData
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
  freeEnergyComplexAlongExhaustion_allStageAscoliData_patch
    G Λ p hBED hd data geom
    (LeeYangPointwiseNormAllStageCompactRealClosedProductAscoliData.toAscoliData
      G Λ p K data geom closedProduct)

/-- **Compact target to all-stage closed-product Ascoli patch input**:
compactness of `K` extracts the finite all-stage geometry, after which compact
pointwise targets, closed pointwise image, equicontinuity, restriction
identities, and coherent overlap equality for that geometry suffice to obtain
the compact real-cover patch endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageClosedProductAscoliData_patch_of_isCompact
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
      LeeYangPointwiseNormAllStageCompactRealClosedProductAscoliData
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
  exact ⟨geom, fun closedProduct =>
    freeEnergyComplexAlongExhaustion_allStageClosedProductAscoliData_patch
      G Λ p hBED hd data geom closedProduct⟩

/-- **Pointwise-normalised all-stage norm-bounded closed-product Ascoli data
to a compact real-cover patch**: pointwise norm bounds supply the compact
closed-ball targets required by the closed-product Ascoli package, and the
resulting data feeds the compact real-cover patch endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageNormBoundedAscoliData_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (normBounded :
      LeeYangPointwiseNormAllStageCompactRealNormBoundedAscoliData
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
  freeEnergyComplexAlongExhaustion_allStageClosedProductAscoliData_patch
    G Λ p hBED hd data geom
    (LeeYangPointwiseNormAllStageCompactRealNormBoundedAscoliData.toClosedProductData
      G Λ p K data geom normBounded)

/-- **Compact target to all-stage norm-bounded closed-product Ascoli patch
input**: compactness of `K` extracts the finite all-stage geometry, after
which closed pointwise image, pointwise norm bounds, equicontinuity,
restriction identities, and coherent overlap equality suffice to obtain the
compact real-cover patch endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageNormBoundedAscoliData_patch_of_isCompact
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
      LeeYangPointwiseNormAllStageCompactRealNormBoundedAscoliData
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
  exact ⟨geom, fun normBounded =>
    freeEnergyComplexAlongExhaustion_allStageNormBoundedAscoliData_patch
      G Λ p hBED hd data geom normBounded⟩

/-- **Pointwise-normalised all-stage range norm-bounded Ascoli data to a
compact real-cover patch**: range carriers reduce the norm-bounded Ascoli
input to stagewise pointwise norm bounds for the selected continuous
restrictions. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedAscoliData_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (rangeBounded :
      LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData
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
  freeEnergyComplexAlongExhaustion_allStageNormBoundedAscoliData_patch
    G Λ p hBED hd data geom
    (LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData.toNormBoundedData
      G Λ p K data geom rangeBounded)

/-- **Compact target to all-stage range norm-bounded Ascoli patch input**:
compactness of `K` extracts the finite all-stage geometry; range
norm-bounded Ascoli data for that geometry then yields the compact real-cover
patch endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedAscoliData_patch_of_isCompact
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
      LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData
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
  exact ⟨geom, fun rangeBounded =>
    freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedAscoliData_patch
      G Λ p hBED hd data geom rangeBounded⟩

/-- **Pointwise-normalised all-stage range norm-bounded Ascoli data to a
relatively compact range patch**: closedness of the pointwise range image,
stagewise pointwise norm bounds, and equicontinuity make the actual
stage-restriction range a compact compact-open carrier, so the PR #2741
relatively compact range bridge applies. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedRelCompact_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (rangeBounded :
      LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData
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
  freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch
    G Λ p hBED hd data geom
    (LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData.toRangeRelCompactData
      G Λ p K data geom rangeBounded)

/-- **Compact target to all-stage range norm-bounded relatively compact patch
input**: compactness of `K` extracts the finite all-stage geometry; range
norm-bounded Ascoli data then supplies the compact carrier input required by
the relatively compact range bridge. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedRelCompact_patch_of_isCompact
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
      LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData
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
  exact ⟨geom, fun rangeBounded =>
    freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedRelCompact_patch
      G Λ p hBED hd data geom rangeBounded⟩

end Ambient

end IsingModel
