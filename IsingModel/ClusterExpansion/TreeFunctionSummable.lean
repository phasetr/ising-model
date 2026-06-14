import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Summability of the tree-function majorant (GJ §18.5)

Toward the convergence of the general (interacting) cluster expansion
(Issue #3954): the analytic majorant series for the Kotecký–Preiss / tree-graph
bound.  The tree-graph (Penrose) bound supplies a per-order Ursell estimate
`|ϕ^T(ω)| ≤ n^{n-2}/n!`, so the comparison series in
`summable_mayerExpansionTerm_of_ursell_le` is `∑_n (n^{n-2}/n!)·S^n`
(`S = ∑_P t^|P|`).  Here we prove the stronger `∑_n (n^n/n!)·S^n` is summable
whenever `e·S < 1` (the radius `S < 1/e` of the tree function `T(x) = ∑ n^{n-1}x^n/n!`),
via the ratio test with the elementary bound `(1 + 1/n)^n ≤ e`.  The
`n^{n-2}/n!` majorant then follows by comparison.

With this analytic step in place, the *only* remaining input for full
cluster-expansion convergence is the tree-graph (Penrose) bound itself
(`|ϕ^T(ω)| ≤ n^{n-2}/n!`).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4–18.5, pp. 378–386.
-/

namespace IsingModel

open scoped Nat

/-- **Elementary bound `(1 + 1/n)^n ≤ e`**: for `1 ≤ n`,
`(1 + 1/n)^n ≤ Real.exp 1`.  Each factor satisfies `1 + 1/n ≤ exp(1/n)`
(`Real.add_one_le_exp`), and `exp(1/n)^n = exp(n·(1/n)) = exp 1`. -/
theorem one_add_inv_pow_le_exp_one {n : ℕ} (hn : 1 ≤ n) :
    (1 + 1 / (n : ℝ)) ^ n ≤ Real.exp 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac : (1 : ℝ) + 1 / (n : ℝ) ≤ Real.exp (1 / (n : ℝ)) := by
    have := Real.add_one_le_exp (1 / (n : ℝ)); linarith
  calc (1 + 1 / (n : ℝ)) ^ n
      ≤ (Real.exp (1 / (n : ℝ))) ^ n :=
        pow_le_pow_left₀ (by positivity) hfac n
    _ = Real.exp ((n : ℝ) * (1 / (n : ℝ))) := by rw [← Real.exp_nat_mul]
    _ = Real.exp 1 := by rw [mul_one_div, div_self (ne_of_gt hn0)]

/-- **Summability of the tree-function majorant** (GJ §18.5): for `0 ≤ S` and
`e·S < 1`, the series `∑_n (n^n/n!)·S^n` is summable.  Ratio test: the ratio of
consecutive terms is `(1 + 1/n)^n · S ≤ e·S < 1` (using
`one_add_inv_pow_le_exp_one`).  This is the analytic majorant for the tree-graph
Ursell bound; the `n^{n-2}/n!` series follows by comparison. -/
theorem summable_nat_pow_self_mul_geometric_div_factorial
    {S : ℝ} (hS0 : 0 ≤ S) (hS : Real.exp 1 * S < 1) :
    Summable (fun n : ℕ => (n : ℝ) ^ n * S ^ n / n.factorial) := by
  refine summable_of_ratio_norm_eventually_le hS (Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hcore : ((n : ℝ) + 1) ^ n ≤ Real.exp 1 * (n : ℝ) ^ n := by
    have h1 : ((n : ℝ) + 1) ^ n = (1 + 1 / (n : ℝ)) ^ n * (n : ℝ) ^ n := by
      rw [← mul_pow]; congr 1; field_simp
    rw [h1]
    exact mul_le_mul_of_nonneg_right (one_add_inv_pow_le_exp_one hn) (by positivity)
  -- f(n+1) = (n+1)^n · S^(n+1) / n!
  have hf1 : ((n + 1 : ℕ) : ℝ) ^ (n + 1) * S ^ (n + 1) / ((n + 1).factorial : ℝ)
      = ((n : ℝ) + 1) ^ n * S ^ (n + 1) / (n.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; rw [pow_succ ((n : ℝ) + 1)]
    field_simp
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity), hf1, div_le_iff₀ hfac]
  have hrhs : Real.exp 1 * S * ((n : ℝ) ^ n * S ^ n / (n.factorial : ℝ)) * (n.factorial : ℝ)
      = Real.exp 1 * (n : ℝ) ^ n * S ^ (n + 1) := by
    field_simp; ring
  rw [hrhs, pow_succ S]
  exact mul_le_mul_of_nonneg_right hcore (by positivity)

/-- **Summability of the tree-graph Ursell majorant** (GJ §18.5): for `0 ≤ S` and
`e·S < 1`, the series `∑_n (n^{n-2}/n!)·S^n` — the exact comparison series for the
tree-graph Ursell bound `|ϕ^T(ω)| ≤ n^{n-2}/n!` consumed by
`summable_mayerExpansionTerm_of_ursell_le` — is summable.  By comparison with
`summable_nat_pow_self_mul_geometric_div_factorial`, since `n^{n-2} ≤ n^n`. -/
theorem summable_nat_pow_self_sub_two_mul_geometric_div_factorial
    {S : ℝ} (hS0 : 0 ≤ S) (hS : Real.exp 1 * S < 1) :
    Summable (fun n : ℕ => (n : ℝ) ^ (n - 2) * S ^ n / n.factorial) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_nat_pow_self_mul_geometric_div_factorial hS0 hS)
  have hfacpos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hpow : (n : ℝ) ^ (n - 2) ≤ (n : ℝ) ^ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · exact pow_le_pow_right₀ (by exact_mod_cast h) (Nat.sub_le n 2)
  have hnum : (n : ℝ) ^ (n - 2) * S ^ n ≤ (n : ℝ) ^ n * S ^ n :=
    mul_le_mul_of_nonneg_right hpow (pow_nonneg hS0 n)
  exact (div_le_div_iff_of_pos_right hfacpos).mpr hnum

end IsingModel
