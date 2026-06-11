import IsingModel.ComplexAnalyticity.ClosureCompactness
import IsingModel.AmbientComplexAnalyticity.AscoliData.Structures.BranchLocallyBounded

/-!
# Closure-carrier conversions — relative compactness without closedness (GJ §4.6 Thm 4.6.2)

The closedness-free route into the relative-compactness pipeline (Issue #628): the carrier
`toFun ⁻¹' closure (toFun '' range)` is compact in the compact-open topology from pointwise
norm bounds and equicontinuity alone, so the range-relative-compactness data can be built
without the `toFun_image_closed` input of the Ascoli structures.

* `...RangeRelCompactCOpenData.ofClosureCarrier` — closedness-free constructor.
* `...RangeRelCompactCOpenData.ofClosedBallDeviationData` — wrapper from the closed-ball
  branch-deviation Ascoli data (its closedness field is not consumed).

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.6,
Theorem 4.6.2, pp. 68–70.
-/

namespace IsingModel

namespace Ambient

open Metric

variable {V : Type*} [DecidableEq V]

/-- **Closedness-free relative-compactness constructor**: the closure carrier is compact from a
stage-uniform norm bound and equicontinuity; the range embeds by `subset_closure`. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData.ofClosureCarrier
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (restricted : ∀ i : Fin geom.n, ℕ →
      C(Metric.ball (geom.center i : ℂ) (data.branchData.radius (geom.center i)), ℂ))
    (hrestrict_eq : ∀ i m z
      (hz : z ∈ Metric.ball (geom.center i : ℂ)
        (data.branchData.radius (geom.center i))),
      data.branchData.branchFamily (geom.center i) m z = restricted i m ⟨z, hz⟩)
    (hbound : ∀ i : Fin geom.n, ∃ C : ℝ, ∀ m
      (x : Metric.ball (geom.center i : ℂ) (data.branchData.radius (geom.center i))),
      ‖restricted i m x‖ ≤ C)
    (heq : ∀ i, Equicontinuous
      ((↑) : Set.range (restricted i) →
        Metric.ball (geom.center i : ℂ) (data.branchData.radius (geom.center i)) → ℂ))
    (hover : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (geom.center i) m)
        (data.branchData.branchFamily (geom.center j) m)
        (Metric.ball (geom.center i : ℂ) (data.branchData.radius (geom.center i))
          ∩ Metric.ball (geom.center j : ℂ) (data.branchData.radius (geom.center j)))) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData G Λ p K data geom where
  carrier i := ContinuousMap.toFun ⁻¹'
    closure (ContinuousMap.toFun '' Set.range (restricted i))
  restricted := restricted
  isCompact_carrier i := by
    obtain ⟨C, hC⟩ := hbound i
    exact isCompact_closureCarrier_compactOpen_complex_of_norm_le_equicontinuous
      (fun _ => C)
      (fun f hf x => by
        obtain ⟨m, rfl⟩ := hf
        exact hC m x)
      (heq i)
  range_subset i := fun g hg =>
    Set.mem_preimage.mpr (subset_closure (Set.mem_image_of_mem _ hg))
  restrict_eq := hrestrict_eq
  overlap_eventually := hover

/-- **Closedness-free wrapper from the closed-ball branch-deviation Ascoli data**: consumes the
equicontinuity, restriction, and overlap fields — but *not* the closedness field — together
with a stage-uniform norm bound on the restrictions. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData.ofClosedBallDeviationData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (closedData : LeeYangClosedBallPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K closedData.data)
    (ascoli : LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
      G Λ p K closedData geom)
    (hbound : ∀ i : Fin geom.n, ∃ C : ℝ, ∀ m
      (x : Metric.ball (geom.center i : ℂ)
        (closedData.data.branchData.radius (geom.center i))),
      ‖ascoli.restricted i m x‖ ≤ C) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K closedData.data geom :=
  LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData.ofClosureCarrier
    G Λ p K closedData.data geom ascoli.restricted ascoli.restrict_eq hbound
    ascoli.equicontinuous ascoli.overlap_eventually

end Ambient

end IsingModel
