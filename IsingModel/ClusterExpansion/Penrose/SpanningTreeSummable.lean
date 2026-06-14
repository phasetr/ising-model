import IsingModel.ClusterExpansion.Penrose.CompleteGraphTreeBound
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Summable majorant for the spanning-tree count of `Kₙ` (Penrose tree-graph, GJ §18.4-18.5)

The cluster-expansion convergence (Issue #3954, milestone M2) requires the
absolute convergence of a Mayer/Ursell series whose coefficients are bounded by
`numSpanningTrees (⊤ : SimpleGraph (Fin n)) / n!` (`CompleteGraphTreeBound.lean`,
`UrsellTreeBound.lean`).  The summable majorant is the real-analysis core proved
here: for `R` with `e·|R| < 1` (i.e. `|R| < 1/e`),
`∑ₙ n^(n-1)/n! · Rⁿ` converges absolutely.

The argument is the ratio test: with `aₙ = n^(n-1)/n! · |R|ⁿ`, the ratio
`a_{n+1}/aₙ = (1 + 1/n)^(n-1) · |R| → e·|R|`, and the elementary bound
`(1 + 1/n)^(n-1) ≤ e` (from `1 + x ≤ eˣ`) gives an eventual ratio `≤ e·|R| < 1`
without invoking the limit `(1 + 1/n)ⁿ → e`.  Majorising the spanning-tree count
`numSpanningTrees (⊤ : SimpleGraph (Fin n)) ≤ n^(n-1)`
(`numSpanningTrees_top_fin_le_pow_pred`) transfers summability to the
Mayer-majorant series, supplying the radius of convergence `1/e`.

## References
- Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4 (p. 332) – §18.5 (p. 335).
- Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §5.7.
-/

namespace IsingModel.Penrose

open Filter Real
open scoped Topology

/-- **Elementary exponential ratio bound** `(1 + 1/n)^(n-1) ≤ e`, the core of the
ratio test for the spanning-tree majorant: from `1 + x ≤ eˣ` at `x = 1/n`,
raising to the power `n - 1` gives `(1 + 1/n)^(n-1) ≤ e^{(n-1)/n} ≤ e`. -/
theorem one_add_inv_natCast_pow_pred_le_exp (n : ℕ) :
    (1 + (n : ℝ)⁻¹) ^ (n - 1) ≤ Real.exp 1 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Nat.cast_zero, inv_zero, add_zero, Nat.zero_sub, pow_zero]
    exact Real.one_le_exp (by norm_num)
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hstep : 1 + (n : ℝ)⁻¹ ≤ Real.exp ((n : ℝ)⁻¹) := by
      have := Real.add_one_le_exp ((n : ℝ)⁻¹)
      linarith
    calc (1 + (n : ℝ)⁻¹) ^ (n - 1)
        ≤ (Real.exp ((n : ℝ)⁻¹)) ^ (n - 1) :=
          pow_le_pow_left₀ (by positivity) hstep _
      _ = Real.exp ((n - 1 : ℕ) * (n : ℝ)⁻¹) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp 1 := by
          apply Real.exp_le_exp.mpr
          rw [mul_inv_le_iff₀ hn0, one_mul]
          exact_mod_cast Nat.sub_le n 1

/-- **Post-cancellation ratio bound** `(n+1)^(n-1) ≤ e · n^(n-1)`: after cancelling
the factorial and power factors, the ratio test for the spanning-tree majorant
reduces to this pure-power inequality, obtained from
`one_add_inv_natCast_pow_pred_le_exp` by multiplying by `n^(n-1)`. -/
theorem succ_pow_pred_le_exp_mul_pow_pred (n : ℕ) :
    ((n : ℝ) + 1) ^ (n - 1) ≤ Real.exp 1 * (n : ℝ) ^ (n - 1) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Nat.cast_zero, zero_add, Nat.zero_sub, pow_zero, mul_one]
    exact Real.one_le_exp (by norm_num)
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hkey := one_add_inv_natCast_pow_pred_le_exp n
    have hrw : (1 + (n : ℝ)⁻¹) ^ (n - 1) * (n : ℝ) ^ (n - 1)
        = ((n : ℝ) + 1) ^ (n - 1) := by
      rw [← mul_pow]
      congr 1
      field_simp
    calc ((n : ℝ) + 1) ^ (n - 1)
        = (1 + (n : ℝ)⁻¹) ^ (n - 1) * (n : ℝ) ^ (n - 1) := hrw.symm
      _ ≤ Real.exp 1 * (n : ℝ) ^ (n - 1) := by
          apply mul_le_mul_of_nonneg_right hkey (by positivity)

/-- **Summable spanning-tree majorant (absolute form)**: for `e·|R| < 1`
(i.e. `|R| < 1/e`), the series `∑ₙ n^(n-1)/n! · |R|ⁿ` converges, by the ratio
test with eventual ratio `≤ e·|R|`. -/
theorem summable_nat_pow_pred_div_factorial_mul_abs_pow
    (R : ℝ) (hR : Real.exp 1 * |R| < 1) :
    Summable fun n : ℕ =>
      ((n : ℝ) ^ (n - 1) / (n.factorial : ℝ)) * |R| ^ n := by
  refine summable_of_ratio_norm_eventually_le hR ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set F : ℝ := ((m + 1).factorial : ℝ) with hF
  have hnnA : (0 : ℝ) ≤ ((↑(m + 1) : ℝ) ^ ((m + 1) - 1) / F) * |R| ^ (m + 1) := by positivity
  have hnnB : (0 : ℝ) ≤
      ((↑(m + 1 + 1) : ℝ) ^ ((m + 1 + 1) - 1) / ((m + 1 + 1).factorial : ℝ)) *
        |R| ^ (m + 1 + 1) := by positivity
  rw [Real.norm_of_nonneg hnnB, Real.norm_of_nonneg hnnA]
  -- reduce ℕ subtraction (no truncation now: m+1 ≥ 1)
  have e_exp1 : (m + 1) - 1 = m := rfl
  have e_exp2 : (m + 1 + 1) - 1 = m + 1 := rfl
  rw [e_exp1, e_exp2]
  -- factor (m+2)! = (m+2)·(m+1)!, (m+2)^(m+1) = (m+2)·(m+2)^m, |R|^(m+2) = |R|^(m+1)·|R|
  have e_fac : ((m + 1 + 1).factorial : ℝ) = ((↑(m + 1) : ℝ) + 1) * F := by
    rw [hF, Nat.factorial_succ (m + 1), Nat.cast_mul, Nat.cast_succ]
  have e_pow : (↑(m + 1 + 1) : ℝ) ^ (m + 1) = ((↑(m + 1) : ℝ) + 1) * ((↑(m + 1) : ℝ) + 1) ^ m := by
    rw [Nat.cast_succ, pow_succ]; ring
  have e_R : |R| ^ (m + 1 + 1) = |R| ^ (m + 1) * |R| := by rw [pow_succ]
  rw [e_fac, e_pow, e_R, mul_div_mul_left _ _ (by positivity : (↑(m + 1) : ℝ) + 1 ≠ 0)]
  have hkey := succ_pow_pred_le_exp_mul_pow_pred (m + 1)
  rw [e_exp1] at hkey
  calc ((↑(m + 1) : ℝ) + 1) ^ m / F * (|R| ^ (m + 1) * |R|)
      = ((↑(m + 1) : ℝ) + 1) ^ m * (|R| ^ (m + 1) * |R| / F) := by ring
    _ ≤ (Real.exp 1 * (↑(m + 1) : ℝ) ^ m) * (|R| ^ (m + 1) * |R| / F) :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = Real.exp 1 * |R| * ((↑(m + 1) : ℝ) ^ m / F * |R| ^ (m + 1)) := by ring

/-- **Summable spanning-tree majorant (signed form)**: for `e·|R| < 1`, the series
`∑ₙ n^(n-1)/n! · Rⁿ` converges absolutely. -/
theorem summable_nat_pow_pred_div_factorial_mul_pow
    (R : ℝ) (hR : Real.exp 1 * |R| < 1) :
    Summable fun n : ℕ =>
      ((n : ℝ) ^ (n - 1) / (n.factorial : ℝ)) * R ^ n := by
  refine (summable_nat_pow_pred_div_factorial_mul_abs_pow R hR).of_norm_bounded ?_
  intro n
  have h : ‖((n : ℝ) ^ (n - 1) / (n.factorial : ℝ)) * R ^ n‖
      = ((n : ℝ) ^ (n - 1) / (n.factorial : ℝ)) * |R| ^ n := by
    rw [Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (n - 1) / (n.factorial : ℝ))]
  exact le_of_eq h

/-- **Summable complete-graph spanning-tree majorant (absolute form)**: the series
`∑ₙ numSpanningTrees (⊤ : SimpleGraph (Fin n)) / n! · |R|ⁿ` converges for `e·|R| < 1`,
by majorising the spanning-tree count `numSpanningTrees (⊤ Fin n) ≤ n^(n-1)`. -/
theorem summable_completeGraph_numSpanningTrees_div_factorial_mul_abs_pow
    (R : ℝ) (hR : Real.exp 1 * |R| < 1) :
    Summable fun n : ℕ =>
      ((numSpanningTrees (⊤ : SimpleGraph (Fin n)) : ℝ) / (n.factorial : ℝ)) * |R| ^ n := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_nat_pow_pred_div_factorial_mul_abs_pow R hR)
  have htree : (numSpanningTrees (⊤ : SimpleGraph (Fin n)) : ℝ) ≤ (n : ℝ) ^ (n - 1) := by
    exact_mod_cast numSpanningTrees_top_fin_le_pow_pred n
  gcongr

/-- **Summable complete-graph spanning-tree majorant (signed form)**: the series
`∑ₙ numSpanningTrees (⊤ : SimpleGraph (Fin n)) / n! · Rⁿ` converges absolutely for
`e·|R| < 1` — the explicit Mayer-series radius of convergence `1/e`. -/
theorem summable_completeGraph_numSpanningTrees_div_factorial_mul_pow
    (R : ℝ) (hR : Real.exp 1 * |R| < 1) :
    Summable fun n : ℕ =>
      ((numSpanningTrees (⊤ : SimpleGraph (Fin n)) : ℝ) / (n.factorial : ℝ)) * R ^ n := by
  refine (summable_completeGraph_numSpanningTrees_div_factorial_mul_abs_pow R hR).of_norm_bounded ?_
  intro n
  have h : ‖((numSpanningTrees (⊤ : SimpleGraph (Fin n)) : ℝ) / (n.factorial : ℝ)) * R ^ n‖
      = ((numSpanningTrees (⊤ : SimpleGraph (Fin n)) : ℝ) / (n.factorial : ℝ)) * |R| ^ n := by
    rw [Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ (numSpanningTrees (⊤ : SimpleGraph (Fin n)) : ℝ) / (n.factorial : ℝ))]
  exact le_of_eq h

end IsingModel.Penrose
