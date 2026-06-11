import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Borel–Carathéodory branch bounds on half-radius balls (GJ §4.6 Thm 4.6.2)

The general layer of the stage-uniform branch bounds (Issue #628): a holomorphic function with a
real-part upper bound on a ball is norm-bounded on the half-radius closed ball with the clean
constant `2M + 3‖f c‖` (Borel–Carathéodory, centred and specialised), and a logarithm branch of
`Z` has real part `log ‖Z‖ / N` (the exponential identity), so the two-sided normalised-log
controls of the Lee–Yang partition function bound the branch real part stage-uniformly.

* `norm_le_of_re_le_on_half` — the half-radius Borel–Carathéodory bound.
* `re_eq_log_norm_div_of_exp_eq` — the branch real-part identity.

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.6,
Theorem 4.6.2, pp. 68–70.
-/

namespace IsingModel

open Metric

/-- **Borel–Carathéodory on the half-radius closed ball, centred**: a holomorphic function on
`ball c r` with `Re f ≤ M` (`0 < M`) satisfies `‖f z‖ ≤ 2M + 3‖f c‖` on
`closedBall c (r/2)` — a constant independent of the function beyond `M` and the centre
value. -/
theorem norm_le_of_re_le_on_half {M : ℝ} (hM : 0 < M) {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball c r))
    (hre : ∀ z ∈ ball c r, (f z).re ≤ M)
    {z : ℂ} (hz : z ∈ closedBall c (r / 2)) :
    ‖f z‖ ≤ 2 * M + 3 * ‖f c‖ := by
  have hmem : ∀ w : ℂ, w ∈ ball (0 : ℂ) r → c + w ∈ ball c r := by
    intro w hw
    rw [mem_ball] at hw ⊢
    simpa [dist_eq_norm] using hw
  have hgd : DifferentiableOn ℂ (fun w => f (c + w)) (ball (0 : ℂ) r) := by
    refine DifferentiableOn.comp hf ?_ ?_
    · exact (differentiable_const c).differentiableOn.add differentiable_id.differentiableOn
    · intro w hw
      exact hmem w hw
  have hgre : Set.MapsTo (fun w => f (c + w)) (ball (0 : ℂ) r) {w : ℂ | w.re ≤ M} := by
    intro w hw
    exact hre (c + w) (hmem w hw)
  have hwz : z - c ∈ ball (0 : ℂ) r := by
    rw [mem_ball, dist_zero_right]
    rw [mem_closedBall, dist_eq_norm] at hz
    linarith
  have hbc := Complex.borelCaratheodory hM hgd hgre hr hwz
  simp only [add_sub_cancel, add_zero] at hbc
  -- the geometric estimates on the half ball
  rw [mem_closedBall, dist_eq_norm] at hz
  have hd0 : 0 ≤ ‖z - c‖ := norm_nonneg _
  have hD : r / 2 ≤ r - ‖z - c‖ := by linarith
  have hDpos : 0 < r - ‖z - c‖ := by linarith
  have h1 : 2 * M * ‖z - c‖ / (r - ‖z - c‖) ≤ 2 * M := by
    rw [div_le_iff₀ hDpos]
    nlinarith
  have h2 : ‖f c‖ * (r + ‖z - c‖) / (r - ‖z - c‖) ≤ 3 * ‖f c‖ := by
    rw [div_le_iff₀ hDpos]
    nlinarith [norm_nonneg (f c)]
  linarith

/-- **The real part of a logarithm branch**: if `exp (N·w) = Zv` with `0 < N`, then
`Re w = log ‖Zv‖ / N`. -/
theorem re_eq_log_norm_div_of_exp_eq {N : ℝ} (hN : 0 < N) {w Zv : ℂ}
    (h : Complex.exp ((N : ℂ) * w) = Zv) :
    w.re = Real.log ‖Zv‖ / N := by
  have h1 : ‖Complex.exp ((N : ℂ) * w)‖ = Real.exp (((N : ℂ) * w).re) :=
    Complex.norm_exp _
  rw [h] at h1
  have h2 : (((N : ℂ)) * w).re = N * w.re := by
    simp [Complex.mul_re]
  rw [h2] at h1
  have h3 : Real.log ‖Zv‖ = N * w.re := by
    rw [h1, Real.log_exp]
  rw [h3]
  field_simp

end IsingModel
