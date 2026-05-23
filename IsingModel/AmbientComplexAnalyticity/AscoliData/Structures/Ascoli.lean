import IsingModel.AmbientComplexAnalyticity.AscoliData.Structures.Geometry

/-!
# Ascoli data structures split — Ascoli data and closed-product Ascoli data

Part of the split ambient Ascoli-data structures layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Pointwise-normalised all-stage Arzelà-Ascoli data**: an Ascoli-style
replacement for direct compact-open compactness on the selected all-stage
Lee-Yang balls.  For each selected ball it stores a compact-open carrier of
continuous restrictions together with compactness of its pointwise
function-space image and equicontinuity; mathlib's Arzelà-Ascoli theorem then
supplies compact-open compactness.  This is still a pre-Montel input: it does
not prove the equicontinuity or compactness of the pointwise function-space
image from holomorphy and local boundedness. -/
structure LeeYangPointwiseNormAllStageCompactRealAscoliData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K data) where
  /-- Carrier of selected continuous restrictions. -/
  carrier : ∀ i : Fin geom.n,
    Set C(Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i)), ℂ)
  /-- Continuous restrictions of each stage branch on the selected ball. -/
  restricted : ∀ i : Fin geom.n, ℕ →
    C(Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i)), ℂ)
  /-- The pointwise function-space image of every carrier is compact. -/
  toFun_image_compact : ∀ i,
    IsCompact (ContinuousMap.toFun '' carrier i)
  /-- Every carrier is equicontinuous. -/
  equicontinuous : ∀ i,
    Equicontinuous
      ((↑) : carrier i →
        Metric.ball (geom.center i : ℂ)
          (data.branchData.radius (geom.center i)) → ℂ)
  /-- Every stage restriction lies in the selected carrier. -/
  mem : ∀ i m, restricted i m ∈ carrier i
  /-- The continuous restriction agrees with the original branch family. -/
  restrict_eq : ∀ i m z
    (hz : z ∈ Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i))),
    data.branchData.branchFamily (geom.center i) m z =
      restricted i m ⟨z, hz⟩
  /-- Selected branch families are eventually equal on pairwise overlaps. -/
  overlap_eventually : ∀ i j, ∀ᶠ m in Filter.atTop,
    Set.EqOn
      (data.branchData.branchFamily (geom.center i) m)
      (data.branchData.branchFamily (geom.center j) m)
      (Metric.ball (geom.center i : ℂ) (data.branchData.radius (geom.center i))
        ∩ Metric.ball (geom.center j : ℂ)
          (data.branchData.radius (geom.center j)))

/-- **Pointwise-normalised all-stage closed-product Ascoli data**: a
Tychonoff-style refinement of the Ascoli input on selected all-stage Lee-Yang
balls.  Instead of directly assuming compactness of the `ContinuousMap.toFun`
image, it records compact pointwise target sets, closedness of the function
image inside the pointwise product, and equicontinuity.  This is still a
pre-Montel input: it does not prove closedness, equicontinuity, or the compact
pointwise bounds from holomorphy and local boundedness. -/
structure LeeYangPointwiseNormAllStageCompactRealClosedProductAscoliData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K data) where
  /-- Carrier of selected continuous restrictions. -/
  carrier : ∀ i : Fin geom.n,
    Set C(Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i)), ℂ)
  /-- Continuous restrictions of each stage branch on the selected ball. -/
  restricted : ∀ i : Fin geom.n, ℕ →
    C(Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i)), ℂ)
  /-- Compact pointwise target set at each point of every selected ball. -/
  valueCompact : ∀ i : Fin geom.n,
    Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i)) → Set ℂ
  /-- Every pointwise target set is compact. -/
  valueCompact_isCompact : ∀ i x, IsCompact (valueCompact i x)
  /-- The pointwise function-space image of every carrier is closed. -/
  toFun_image_closed : ∀ i, IsClosed (ContinuousMap.toFun '' carrier i)
  /-- Every carrier element lands in the selected pointwise compact target. -/
  value_mem : ∀ i f, f ∈ carrier i → ∀ x, f x ∈ valueCompact i x
  /-- Every carrier is equicontinuous. -/
  equicontinuous : ∀ i,
    Equicontinuous
      ((↑) : carrier i →
        Metric.ball (geom.center i : ℂ)
          (data.branchData.radius (geom.center i)) → ℂ)
  /-- Every stage restriction lies in the selected carrier. -/
  mem : ∀ i m, restricted i m ∈ carrier i
  /-- The continuous restriction agrees with the original branch family. -/
  restrict_eq : ∀ i m z
    (hz : z ∈ Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i))),
    data.branchData.branchFamily (geom.center i) m z =
      restricted i m ⟨z, hz⟩
  /-- Selected branch families are eventually equal on pairwise overlaps. -/
  overlap_eventually : ∀ i j, ∀ᶠ m in Filter.atTop,
    Set.EqOn
      (data.branchData.branchFamily (geom.center i) m)
      (data.branchData.branchFamily (geom.center j) m)
      (Metric.ball (geom.center i : ℂ) (data.branchData.radius (geom.center i))
        ∩ Metric.ball (geom.center j : ℂ)
          (data.branchData.radius (geom.center j)))


end Ambient
end IsingModel
