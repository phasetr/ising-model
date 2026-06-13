import IsingModel.ClusterExpansion.MayerRootComponent

/-!
# The Penrose tree-graph bound for the complete graph (GJ §18.4–18.5)

Toward the convergence of the general (interacting) cluster expansion
(Issue #3954): the **Penrose tree-graph inequality** bounds the absolute value
of the connected-spanning alternating sum (the Ursell numerator) by the number
of spanning trees of the incompatibility graph,
`|∑_{S connected spanning} (-1)^{|S|}| ≤ (number of spanning trees)`.

This file establishes the inequality for the **complete graph** `K_n` — the
worst case, attained by a fully-incompatible cluster.  There the alternating
sum is exactly `(-1)^{n-1}(n-1)!`
(`alternatingConnectedSubgraphSum_completeGraph_closed_form`) and the number of
spanning trees is Cayley's count `n^{n-2}`, so the tree-graph bound is the
elementary inequality `(n-1)! ≤ n^{n-2}`.  The general-graph Penrose bound
(Penrose's partition scheme) remains for a later PR of #3954.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4–18.5, pp. 378–386.
* O. Penrose, *Convergence of fugacity expansions for classical systems*, 1967.
-/

namespace IsingModel

open Finset

/-- **Factorial vs. shifted power**: `(m+1)! ≤ (m+2)^m` for every `m`.  The
clean (subtraction-free) form of the Cayley bound `(n-1)! ≤ n^{n-2}`; the
inductive step multiplies by `(k+2)` and absorbs it into the base of the
power. -/
theorem factorial_succ_le_pow (m : ℕ) : (m + 1).factorial ≤ (m + 2) ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
    calc (k + 2).factorial = (k + 2) * (k + 1).factorial := by
          rw [Nat.factorial_succ]
      _ ≤ (k + 2) * (k + 2) ^ k := Nat.mul_le_mul_left _ ih
      _ = (k + 2) ^ (k + 1) := by rw [← pow_succ']
      _ ≤ (k + 3) ^ (k + 1) := Nat.pow_le_pow_left (by omega) _

/-- **Cayley tree-graph bound (ℕ form)**: `(n-1)! ≤ n^{n-2}` for `n ≥ 1`.  The
number of spanning trees of `K_n` is `n^{n-2}` (Cayley), so this is the
tree-graph bound for the complete graph in `ℕ`. -/
theorem factorial_pred_le_pow_sub_two {n : ℕ} (hn : 1 ≤ n) :
    (n - 1).factorial ≤ n ^ (n - 2) := by
  match n, hn with
  | 1, _ => simp
  | (k + 2), _ =>
    have h := factorial_succ_le_pow k
    simpa using h

/-- **Penrose tree-graph bound for the complete graph** (GJ §18.4): the absolute
value of the connected-spanning alternating sum of `K_n` is at most Cayley's
spanning-tree count `n^{n-2}`.  Since the alternating sum is exactly
`(-1)^{n-1}(n-1)!`, this is `(n-1)! ≤ n^{n-2}`
(`factorial_pred_le_pow_sub_two`). -/
theorem abs_alternatingConnectedSubgraphSum_completeGraph_le_cayley
    {n : ℕ} (hn : 1 ≤ n) :
    |alternatingConnectedSubgraphSum (⊤ : SimpleGraph (Fin n))|
      ≤ (n : ℝ) ^ (n - 2) := by
  rw [alternatingConnectedSubgraphSum_completeGraph_closed_form hn, abs_mul,
    abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
  calc ((n - 1).factorial : ℝ) ≤ ((n ^ (n - 2) : ℕ) : ℝ) := by
        exact_mod_cast factorial_pred_le_pow_sub_two hn
    _ = (n : ℝ) ^ (n - 2) := by push_cast; ring

/-- **Ursell coefficient tree-graph bound (complete cluster)** (GJ §18.4): for a
fully-incompatible cluster `ω : Fin n → polymers` (`n ≥ 1`), the Ursell
coefficient is bounded by Cayley's spanning-tree count over `n!`,
`|ϕ^T(ω)| ≤ n^{n-2}/n!`.  Combines `ursellCoefficient_complete`
(`ϕ^T(ω) = (-1)^{n-1}(n-1)!/n!`) with the complete-graph tree-graph bound. -/
theorem abs_ursellCoefficient_complete_le_cayley_div
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} {ω : Fin n → Finset (Sym2 ι)} (hn : 1 ≤ n)
    (h : ∀ i j, i ≠ j → PolymersIncompatible (ω i) (ω j)) :
    |ursellCoefficient ω| ≤ (n : ℝ) ^ (n - 2) / (n.factorial : ℝ) := by
  rw [ursellCoefficient_complete hn h, abs_div, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, one_mul, Nat.abs_cast, Nat.abs_cast]
  gcongr
  calc ((n - 1).factorial : ℝ) ≤ ((n ^ (n - 2) : ℕ) : ℝ) := by
        exact_mod_cast factorial_pred_le_pow_sub_two hn
    _ = (n : ℝ) ^ (n - 2) := by push_cast; ring

end IsingModel
