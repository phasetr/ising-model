import IsingModel.AmbientComplexAnalyticity.AscoliData.Structures.NormBounded

/-!
# Ascoli data structures split — branch norm-bounded and branch const-norm-bounded Ascoli data

Part of the split ambient Ascoli-data structures layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Pointwise-normalised all-stage branch norm-bounded Ascoli data**: a
branch-family version of the range norm-bounded Ascoli input where the
pointwise norm bounds are stated on the original selected branch functions.
The restriction identities transport those bounds to the continuous
restrictions consumed by the range package. -/
structure LeeYangPointwiseNormAllStageCompactRealBranchNormBoundedAscoliData
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
  /-- Every original branch function satisfies the selected pointwise norm bound. -/
  branch_norm_le : ∀ i m z
    (hz : z ∈ Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i))),
    ‖data.branchData.branchFamily (geom.center i) m z‖ ≤ bound i ⟨z, hz⟩
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

/-- **Pointwise-normalised all-stage branch constant norm-bounded Ascoli data**:
a constant-bound version of the branch norm-bounded Ascoli input.  It asks for
one real norm bound on each selected Lee--Yang ball, rather than a bound
function depending on the point of the ball. -/
structure LeeYangPointwiseNormAllStageCompactRealBranchConstNormBoundedAscoliData
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
  /-- One real-valued norm bound for each selected ball. -/
  bound : Fin geom.n → ℝ
  /-- The pointwise function-space image of every range carrier is closed. -/
  toFun_image_closed : ∀ i,
    IsClosed (ContinuousMap.toFun '' Set.range (restricted i))
  /-- Every original branch function satisfies the selected ballwise norm bound. -/
  branch_norm_le : ∀ i m z
    (_hz : z ∈ Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i))),
    ‖data.branchData.branchFamily (geom.center i) m z‖ ≤ bound i
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
