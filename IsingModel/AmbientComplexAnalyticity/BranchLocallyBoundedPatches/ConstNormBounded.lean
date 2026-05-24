import IsingModel.AmbientComplexAnalyticity.BranchLocallyBoundedPatches.CompactTarget

/-!
# Branch locally bounded patches split — constant norm-bounded Ascoli data patches

Part of the split branch-locally-bounded patches layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Pointwise-normalised all-stage branch constant norm-bounded Ascoli data
to a compact real-cover patch**: ballwise constant branch-family norm bounds
are turned into pointwise constant bounds and then fed to the branch
norm-bounded Ascoli package. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageBranchConstNormBoundedAscoliData_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (constBounded :
      LeeYangPointwiseNormAllStageCompactRealBranchConstNormBoundedAscoliData
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
  freeEnergyComplexAlongExhaustion_allStageBranchNormBoundedAscoliData_patch
    G Λ p hBED hd data geom
    (LeeYangPointwiseNormAllStageCompactRealBranchConstNormBoundedAscoliData.toBranchNormBoundedData
      G Λ p K data geom constBounded)

/-- **Compact target to all-stage branch constant norm-bounded Ascoli patch
input**: compactness of `K` extracts the finite all-stage geometry; branch
constant norm-bounded Ascoli data for that geometry then yields the compact
real-cover patch endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageBranchConstNormBoundedAscoliData_patch_of_isCompact
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
      LeeYangPointwiseNormAllStageCompactRealBranchConstNormBoundedAscoliData
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
  exact ⟨geom, fun constBounded =>
    freeEnergyComplexAlongExhaustion_allStageBranchConstNormBoundedAscoliData_patch
      G Λ p hBED hd data geom constBounded⟩

/-- **Pointwise-normalised all-stage branch locally bounded Ascoli data to a
compact real-cover patch**: existential ballwise branch-family bounds are
chosen as constants and then fed to the branch constant norm-bounded Ascoli
package. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageBranchLocallyBoundedAscoliData_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (locallyBounded :
      LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData
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
  freeEnergyComplexAlongExhaustion_allStageBranchConstNormBoundedAscoliData_patch
    G Λ p hBED hd data geom
    (LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData.toConstData
      G Λ p K data geom locallyBounded)

/-- **Compact target to all-stage branch locally bounded Ascoli patch input**:
compactness of `K` extracts the finite all-stage geometry; branch locally
bounded Ascoli data for that geometry then yields the compact real-cover patch
endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageBranchLocallyBoundedAscoliData_patch_of_isCompact
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
      LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData
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
  exact ⟨geom, fun locallyBounded =>
    freeEnergyComplexAlongExhaustion_allStageBranchLocallyBoundedAscoliData_patch
      G Λ p hBED hd data geom locallyBounded⟩


end Ambient
end IsingModel
