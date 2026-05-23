import IsingModel.AmbientComplexAnalyticity.AscoliData.Structures.Ascoli

/-!
# Ascoli data structures split — norm-bounded and range-norm-bounded Ascoli data

Part of the split ambient Ascoli-data structures layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Pointwise-normalised all-stage norm-bounded closed-product Ascoli
data**: a specialisation of the closed-product Ascoli input where the compact
pointwise target sets are closed complex balls supplied by pointwise norm
bounds.  This narrows the remaining normal-family input to closedness of the
pointwise function-space image, pointwise norm bounds, equicontinuity, and
coherent overlap equality. -/
structure LeeYangPointwiseNormAllStageCompactRealNormBoundedAscoliData
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
  /-- Pointwise real-valued norm bound for each selected ball. -/
  bound : ∀ i : Fin geom.n,
    Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i)) → ℝ
  /-- The pointwise function-space image of every carrier is closed. -/
  toFun_image_closed : ∀ i, IsClosed (ContinuousMap.toFun '' carrier i)
  /-- Every carrier element satisfies the selected pointwise norm bound. -/
  norm_le : ∀ i f, f ∈ carrier i → ∀ x, ‖f x‖ ≤ bound i x
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

/-- **Pointwise-normalised all-stage range norm-bounded Ascoli data**: a
range-specialised version of the norm-bounded Ascoli input where each carrier
is fixed to the actual sequence range of the continuous restrictions.  A
stagewise norm bound therefore supplies the carrier-wide bound required by the
norm-bounded package. -/
structure LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K data) where
  /-- Continuous restrictions of each stage branch on the selected ball. -/
  restricted : ∀ i : Fin geom.n, ℕ →
    C(Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i)), ℂ)
  /-- Pointwise real-valued norm bound for each selected ball. -/
  bound : ∀ i : Fin geom.n,
    Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i)) → ℝ
  /-- The pointwise function-space image of every range carrier is closed. -/
  toFun_image_closed : ∀ i,
    IsClosed (ContinuousMap.toFun '' Set.range (restricted i))
  /-- Every stage restriction satisfies the selected pointwise norm bound. -/
  norm_le : ∀ i m, ∀ x, ‖restricted i m x‖ ≤ bound i x
  /-- Every range carrier is equicontinuous. -/
  equicontinuous : ∀ i,
    Equicontinuous
      ((↑) : Set.range (restricted i) →
        Metric.ball (geom.center i : ℂ)
          (data.branchData.radius (geom.center i)) → ℂ)
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
