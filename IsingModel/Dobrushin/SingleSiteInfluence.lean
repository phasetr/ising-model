import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The single-site Ising influence bound (GJ §17.1 / Dobrushin uniqueness)

Toward a transverse-volume-uniform spectral gap, the correct route (the one-step full-layer
Dobrushin coefficient is provably insufficient) is **single-site Dobrushin uniqueness**: the
influence `c_{xy}` of a neighbour `y` on the single-site conditional Gibbs distribution at `x` is
uniformly small at high temperature, and Dobrushin's condition `∑_y c_{xy} = tanh(βJ)·deg < 1`
gives uniqueness with volume-uniform exponential decay.

This file proves the analytic heart: the single-site up-probability is `(1 + tanh a)/2`; flipping
one neighbour (shifting the local field by `±t`, `t = βJ`) changes it by at most `tanh t`. The
nearest-neighbour Ising influence is therefore `tanh(βJ)`.

* `isingSingleSiteUpProb` — the single-site up-probability `e^a/(e^a + e^{-a})` of local field `a`.
* `isingSingleSiteUpProb_eq_tanh` — `= (1 + tanh a)/2`.
* `tanh_add_sub_tanh_sub_abs_le` — `|tanh(a+t) − tanh(a−t)| ≤ 2·tanh t` for `t ≥ 0`.
* `isingSingleSiteUpProb_flip_neighbour_dist_le` — the single-site influence bound `≤ tanh t`.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1.
-/

namespace IsingModel

namespace Dobrushin

open Real

/-- **The single-site up-probability** of a spin in local field `a = β(h + J·(neighbour sum))`:
the conditional probability that the spin is `+1`, `e^a/(e^a + e^{-a})`. -/
noncomputable def isingSingleSiteUpProb (a : ℝ) : ℝ :=
  Real.exp a / (Real.exp a + Real.exp (-a))

/-- **The single-site up-probability is `(1 + tanh a)/2`** (the logistic/sigmoid form). -/
theorem isingSingleSiteUpProb_eq_tanh (a : ℝ) :
    isingSingleSiteUpProb a = (1 + Real.tanh a) / 2 := by
  have hne : Real.exp a + Real.exp (-a) ≠ 0 := by positivity
  rw [isingSingleSiteUpProb, Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  field_simp
  ring

/-- **The product of shifted hyperbolic cosines**: `cosh(a+t)·cosh(a−t) = cosh²t + sinh²a`. -/
theorem cosh_add_mul_cosh_sub (a t : ℝ) :
    Real.cosh (a + t) * Real.cosh (a - t) = Real.cosh t ^ 2 + Real.sinh a ^ 2 := by
  rw [Real.cosh_add, Real.cosh_sub]
  nlinarith [Real.cosh_sq_sub_sinh_sq a, Real.cosh_sq_sub_sinh_sq t]

/-- **The sharp tanh-difference bound**: `|tanh(a+t) − tanh(a−t)| ≤ 2·tanh t` for `t ≥ 0`. The
difference is `sinh(2t)/(cosh(a+t)·cosh(a−t))` and the denominator is at least `cosh²t`. -/
theorem tanh_add_sub_tanh_sub_abs_le (a t : ℝ) (ht : 0 ≤ t) :
    |Real.tanh (a + t) - Real.tanh (a - t)| ≤ 2 * Real.tanh t := by
  have hcat : (0 : ℝ) < Real.cosh (a + t) := Real.cosh_pos _
  have hcas : (0 : ℝ) < Real.cosh (a - t) := Real.cosh_pos _
  have hct : (0 : ℝ) < Real.cosh t := Real.cosh_pos _
  have hkey : Real.tanh (a + t) - Real.tanh (a - t)
      = Real.sinh (2 * t) / (Real.cosh (a + t) * Real.cosh (a - t)) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
      div_sub_div _ _ hcat.ne' hcas.ne']
    congr 1
    rw [← Real.sinh_sub]
    congr 1
    ring
  have hdenom_pos : (0 : ℝ) < Real.cosh (a + t) * Real.cosh (a - t) := mul_pos hcat hcas
  have hge : Real.cosh t ^ 2 ≤ Real.cosh (a + t) * Real.cosh (a - t) := by
    rw [cosh_add_mul_cosh_sub]; nlinarith [sq_nonneg (Real.sinh a)]
  have hsinh2t : (0 : ℝ) ≤ Real.sinh (2 * t) := by
    rw [Real.sinh_eq]
    have : Real.exp (-(2 * t)) ≤ Real.exp (2 * t) := Real.exp_le_exp.mpr (by linarith)
    linarith
  -- the difference is nonnegative, so the absolute value is the difference
  have hdiff_nonneg : 0 ≤ Real.tanh (a + t) - Real.tanh (a - t) := by
    rw [hkey]; exact div_nonneg hsinh2t hdenom_pos.le
  rw [abs_of_nonneg hdiff_nonneg, hkey]
  -- sinh(2t)/(cosh(a+t)cosh(a-t)) ≤ sinh(2t)/cosh²t = 2 tanh t
  have hstep : Real.sinh (2 * t) / (Real.cosh (a + t) * Real.cosh (a - t))
      ≤ Real.sinh (2 * t) / Real.cosh t ^ 2 :=
    div_le_div_of_nonneg_left hsinh2t (by positivity) hge
  refine hstep.trans (le_of_eq ?_)
  rw [Real.sinh_two_mul, Real.tanh_eq_sinh_div_cosh]
  field_simp

/-- **The single-site Ising influence bound**: flipping a single neighbour shifts the local field by
`±t` (with `t = βJ`), and the resulting change in the single-site up-probability is at most
`tanh t`. Thus the nearest-neighbour Dobrushin influence of the Ising model is `tanh(βJ)`. -/
theorem isingSingleSiteUpProb_flip_neighbour_dist_le (a t : ℝ) (ht : 0 ≤ t) :
    |isingSingleSiteUpProb (a + t) - isingSingleSiteUpProb (a - t)| ≤ Real.tanh t := by
  rw [isingSingleSiteUpProb_eq_tanh, isingSingleSiteUpProb_eq_tanh,
    show ((1 + Real.tanh (a + t)) / 2 - (1 + Real.tanh (a - t)) / 2)
      = (Real.tanh (a + t) - Real.tanh (a - t)) / 2 by ring,
    abs_div, abs_two]
  have h := tanh_add_sub_tanh_sub_abs_le a t ht
  linarith

end Dobrushin

end IsingModel
