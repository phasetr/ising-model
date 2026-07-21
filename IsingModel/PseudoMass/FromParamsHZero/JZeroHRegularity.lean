import IsingModel.PseudoMass.FromParamsHZero.JZeroBetaRegularity

/-!
# Pseudo-mass J-zero field regularity

Continuity and differentiability wrappers in the field variable on the `J = 0`
distinct-pair slice.

## Umbrella-reachable via its cluster head

This module has no importers outside its own cluster.  The cluster head is
registered in the root umbrella `IsingModel.lean`, so this module lies inside
the transitive import closure of `import IsingModel` and is therefore covered by
the capstone axiom audit (`scripts/audit_gate.py`, check V3).  It is
genuine formalization — non-trivial regularity results for the `J = 0` /
`h = 0` slices of `pseudoMassFromParamsAtPair`, built on the live
`PseudoMass/FromParamsBasic` results.
-/

namespace IsingModel

open Set Real Filter

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is
`DifferentiableAt` in `h` for `h > 0`** (with `β > 0` fixed):
h-direction analogue of `_differentiableAt_beta_pos`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_differentiableAt_h_pos
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    DifferentiableAt ℝ
      (fun y : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨0, y, β⟩ : IsingParams ℝ) x z) h := by
  have hf_at : ∀ y > 0, Ferromagnetic (⟨(0 : ℝ), y, β⟩ : IsingParams ℝ) :=
    fun y hy => ⟨le_refl 0, hy.le, hβ⟩
  have hh_nhd : ∀ᶠ y in nhds h, 0 < y := by
    rw [Metric.eventually_nhds_iff]
    refine ⟨h / 2, by linarith, ?_⟩
    intros y hy
    rw [Real.dist_eq, abs_lt] at hy
    linarith
  have hEq : (fun y : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                              (⟨0, y, β⟩ : IsingParams ℝ) x z) =ᶠ[nhds h]
              (fun y : ℝ => pseudoMassExt hα hr (Real.tanh (β * y) ^ 2)) := by
    filter_upwards [hh_nhd] with y hy
    exact pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ
            (hf_at y hy) hxz
  have hdiff_alt : DifferentiableAt ℝ
                    (fun y : ℝ => pseudoMassExt hα hr (Real.tanh (β * y) ^ 2)) h := by
    have hβh_pos : 0 < β * h := mul_pos hβ hh
    have hmul : DifferentiableAt ℝ (fun y : ℝ => β * y) h :=
      ((differentiable_const _).mul differentiable_id).differentiableAt
    have houter : DifferentiableAt ℝ
                    (fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) (β * h) :=
      pseudoMassExt_tanh_sq_differentiableAt_pos hα hr hβh_pos
    change DifferentiableAt ℝ
      ((fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) ∘ (fun y : ℝ => β * y)) h
    exact DifferentiableAt.comp h houter hmul
  exact hdiff_alt.congr_of_eventuallyEq hEq

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is
`ContinuousAt` in `h` for `h > 0`** (with `β > 0` fixed): h-direction
analogue of `_at_J_zero_distinct_continuousAt_beta_pos`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_continuousAt_h_pos
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    ContinuousAt
      (fun y : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨0, y, β⟩ : IsingParams ℝ) x z) h := by
  have hf_at : ∀ y > 0, Ferromagnetic (⟨(0 : ℝ), y, β⟩ : IsingParams ℝ) :=
    fun y hy => ⟨le_refl 0, hy.le, hβ⟩
  have hh_nhd : ∀ᶠ y in nhds h, 0 < y := by
    rw [Metric.eventually_nhds_iff]
    refine ⟨h / 2, by linarith, ?_⟩
    intros y hy
    rw [Real.dist_eq, abs_lt] at hy
    linarith
  have hEq : (fun y : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                              (⟨0, y, β⟩ : IsingParams ℝ) x z) =ᶠ[nhds h]
              (fun y : ℝ => pseudoMassExt hα hr (Real.tanh (β * y) ^ 2)) := by
    filter_upwards [hh_nhd] with y hy
    exact pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ
            (hf_at y hy) hxz
  refine (ContinuousAt.congr ?_ hEq.symm)
  have hβh_pos : 0 < β * h := mul_pos hβ hh
  have hmul : ContinuousAt (fun y : ℝ => β * y) h :=
    (continuous_const.mul continuous_id).continuousAt
  have houter : ContinuousAt
                  (fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) (β * h) :=
    pseudoMassExt_tanh_sq_continuousAt_pos hα hr hβh_pos
  change ContinuousAt
    ((fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) ∘ (fun y : ℝ => β * y)) h
  exact ContinuousAt.comp houter hmul

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is
`ContinuousOn (Ioi 0)` in `β`**: lift `_continuousAt_beta_pos` to a
`ContinuousOn` over the open positive real interval. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_continuousOn_beta_Ioi
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h : ℝ} (hh : 0 < h) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    ContinuousOn
      (fun b : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨0, h, b⟩ : IsingParams ℝ) x z) (Set.Ioi 0) := by
  intro β hβ
  exact (pseudoMassFromParamsAtPair_at_J_zero_distinct_continuousAt_beta_pos
            hα hr d Λ hh hβ hxz).continuousWithinAt

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is
`ContinuousOn (Ioi 0)` in `h`**: lift `_continuousAt_h_pos`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_continuousOn_h_Ioi
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    ContinuousOn
      (fun y : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨0, y, β⟩ : IsingParams ℝ) x z) (Set.Ioi 0) := by
  intro h hh
  exact (pseudoMassFromParamsAtPair_at_J_zero_distinct_continuousAt_h_pos
            hα hr d Λ hh hβ hxz).continuousWithinAt

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is
`DifferentiableOn (Ioi 0)` in `β`**. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_differentiableOn_beta_Ioi
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h : ℝ} (hh : 0 < h) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    DifferentiableOn ℝ
      (fun b : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨0, h, b⟩ : IsingParams ℝ) x z) (Set.Ioi 0) := by
  intro β hβ
  exact (pseudoMassFromParamsAtPair_at_J_zero_distinct_differentiableAt_beta_pos
            hα hr d Λ hh hβ hxz).differentiableWithinAt

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is
`DifferentiableOn (Ioi 0)` in `h`**. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_differentiableOn_h_Ioi
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    DifferentiableOn ℝ
      (fun y : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨0, y, β⟩ : IsingParams ℝ) x z) (Set.Ioi 0) := by
  intro h hh
  exact (pseudoMassFromParamsAtPair_at_J_zero_distinct_differentiableAt_h_pos
            hα hr d Λ hh hβ hxz).differentiableWithinAt

end IsingModel
