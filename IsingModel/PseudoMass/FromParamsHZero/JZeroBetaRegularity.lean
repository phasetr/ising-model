import IsingModel.PseudoMass.FromParamsHZero.JZeroValues

/-!
# Pseudo-mass J-zero beta regularity

Continuity and differentiability wrappers in the inverse-temperature variable
on the `J = 0` distinct-pair slice.

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
`ContinuousAt` in `β` for `β > 0`** (with `h > 0` fixed): combines
`_at_J_zero_distinct_eq` (the bridge equals `pseudoMassExt(tanh(β·h)^2)`)
with `pseudoMassExt_tanh_sq_continuousAt_pos` (PR #1685). Useful for
showing the J=0 reference slice is continuously parametrised by β. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_continuousAt_beta_pos
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    ContinuousAt
      (fun b : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨0, h, b⟩ : IsingParams ℝ) x z) β := by
  have hf_at : ∀ b > 0, Ferromagnetic (⟨(0 : ℝ), h, b⟩ : IsingParams ℝ) :=
    fun b hb => ⟨le_refl 0, hh.le, hb⟩
  -- Use `pseudoMassFromParamsAtPair_at_J_zero_distinct_eq` to rewrite as
  -- `pseudoMassExt(tanh(b·h)^2)`. The rewrite holds for ferromagnetic params,
  -- which requires `b > 0`. Use `Filter.EventuallyEq` on a neighborhood of β.
  have hβ_nhd : ∀ᶠ b in nhds β, 0 < b := by
    rw [Metric.eventually_nhds_iff]
    refine ⟨β / 2, by linarith, ?_⟩
    intros y hy
    rw [Real.dist_eq, abs_lt] at hy
    linarith
  have hEq : (fun b : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                              (⟨0, h, b⟩ : IsingParams ℝ) x z) =ᶠ[nhds β]
              (fun b : ℝ => pseudoMassExt hα hr (Real.tanh (b * h) ^ 2)) := by
    filter_upwards [hβ_nhd] with b hb
    exact pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ
            (hf_at b hb) hxz
  refine (ContinuousAt.congr ?_ hEq.symm)
  -- Continuity of `b ↦ pseudoMassExt(tanh(b·h)^2)` at β:
  -- Composition `(b ↦ b·h)` (continuous) then `pseudoMassExt(tanh(·)^2)`
  -- (continuous at β·h > 0 by PR #1685).
  have hβh_pos : 0 < β * h := mul_pos hβ hh
  have hmul : ContinuousAt (fun b : ℝ => b * h) β :=
    (continuous_id.mul continuous_const).continuousAt
  have houter : ContinuousAt
                  (fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) (β * h) :=
    pseudoMassExt_tanh_sq_continuousAt_pos hα hr hβh_pos
  change ContinuousAt
    ((fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) ∘ (fun b : ℝ => b * h)) β
  exact ContinuousAt.comp houter hmul

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` is
`DifferentiableAt` in `β` for `β > 0`** (with `h > 0` fixed): same
proof structure as `_continuousAt_beta_pos` (PR #1686), substituting
`pseudoMassExt_tanh_sq_differentiableAt_pos` (PR #1685) for the
ContinuousAt version. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_differentiableAt_beta_pos
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    DifferentiableAt ℝ
      (fun b : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨0, h, b⟩ : IsingParams ℝ) x z) β := by
  have hf_at : ∀ b > 0, Ferromagnetic (⟨(0 : ℝ), h, b⟩ : IsingParams ℝ) :=
    fun b hb => ⟨le_refl 0, hh.le, hb⟩
  have hβ_nhd : ∀ᶠ b in nhds β, 0 < b := by
    rw [Metric.eventually_nhds_iff]
    refine ⟨β / 2, by linarith, ?_⟩
    intros y hy
    rw [Real.dist_eq, abs_lt] at hy
    linarith
  have hEq : (fun b : ℝ => pseudoMassFromParamsAtPair hα hr d Λ
                              (⟨0, h, b⟩ : IsingParams ℝ) x z) =ᶠ[nhds β]
              (fun b : ℝ => pseudoMassExt hα hr (Real.tanh (b * h) ^ 2)) := by
    filter_upwards [hβ_nhd] with b hb
    exact pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ
            (hf_at b hb) hxz
  have hdiff_alt : DifferentiableAt ℝ
                    (fun b : ℝ => pseudoMassExt hα hr (Real.tanh (b * h) ^ 2)) β := by
    have hβh_pos : 0 < β * h := mul_pos hβ hh
    have hmul : DifferentiableAt ℝ (fun b : ℝ => b * h) β :=
      (differentiable_id.mul (differentiable_const _)).differentiableAt
    have houter : DifferentiableAt ℝ
                    (fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) (β * h) :=
      pseudoMassExt_tanh_sq_differentiableAt_pos hα hr hβh_pos
    change DifferentiableAt ℝ
      ((fun s : ℝ => pseudoMassExt hα hr (Real.tanh s ^ 2)) ∘ (fun b : ℝ => b * h)) β
    exact DifferentiableAt.comp β houter hmul
  exact hdiff_alt.congr_of_eventuallyEq hEq

end IsingModel
