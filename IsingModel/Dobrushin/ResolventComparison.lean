import IsingModel.Dobrushin.DobrushinResolvent

/-!
# The Dobrushin resolvent comparison inequality (GJ §17.1, Issue #4201)

The matrix-analytic core of the Dobrushin comparison theorem: a nonnegative vector `d` satisfying
the one-step Dobrushin inequality `d_x ≤ b_x + ∑_y C_{xy} d_y` is bounded by the resolvent applied
to `b`, `d_x ≤ ∑_y R_{xy} b_y`, where `R = ∑_n Cⁿ` is the Neumann resolvent of the influence matrix
`C`. This solves the linear comparison system `d ≤ b + C d ⟹ d ≤ (I − C)^{-1} b` via the decay
`Cⁿ → 0` (the rows of `Cⁿ` tend to `0` at high temperature). Combined with the heat-bath telescoping
(which produces the hypothesis `d ≤ b + C d` from a boundary-condition difference), this yields the
Dobrushin comparison theorem (final assembly, later PR).

* `vector_le_resolvent_of_le_add_mul` — abstract: nonnegative `C`, `d`, per-entry-summable powers,
  rows of `Cⁿ` tending to `0`, and `d ≤ b + C d` give `d_x ≤ ∑_y (∑_n (Cⁿ)_{xy}) b_y`.
* `dobrushin_resolvent_comparison` — the Ising specialization with `C = isingInfluenceMatrix`,
  `R = dobrushinResolvent`, valid for `0 ≤ βJ` and `βJ·Δ(G) < 1`.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306.
-/

namespace IsingModel

namespace Dobrushin

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Abstract Dobrushin resolvent comparison**: for a nonnegative matrix `C` whose powers are
per-entry summable with row sums tending to `0`, a nonnegative vector `d` satisfying the one-step
inequality `d_x ≤ b_x + ∑_y C_{xy} d_y` is bounded by the Neumann resolvent applied to `b`:
`d_x ≤ ∑_y (∑_n (Cⁿ)_{xy}) b_y`. The proof iterates into finite Neumann partial sums
`d_x ≤ ∑_y (∑_{k<n} (Cᵏ)_{xy}) b_y + ∑_y (Cⁿ)_{xy} d_y`, then takes `n → ∞`: the first term
converges to the resolvent and the tail `∑_y (Cⁿ)_{xy} d_y` vanishes (bounded by
`(∑_z d_z)·∑_y (Cⁿ)_{xy} → 0`). -/
theorem vector_le_resolvent_of_le_add_mul {C : Matrix ι ι ℝ} {d b : ι → ℝ}
    (hC : ∀ x y, 0 ≤ C x y) (hd : ∀ x, 0 ≤ d x)
    (hsum : ∀ x y, Summable (fun n => (C ^ n) x y))
    (htail : ∀ x, Filter.Tendsto (fun n => ∑ y, (C ^ n) x y) Filter.atTop (nhds 0))
    (hineq : ∀ x, d x ≤ b x + ∑ y, C x y * d y) (x : ι) :
    d x ≤ ∑ y, (∑' n, (C ^ n) x y) * b y := by
  classical
  have hCpow : ∀ (n : ℕ) (a c : ι), 0 ≤ (C ^ n) a c := Matrix.pow_apply_nonneg hC
  -- the n-th Neumann partial bound `RHS n a`
  set RHS : ℕ → ι → ℝ := fun n a =>
    (∑ y, (∑ k ∈ Finset.range n, (C ^ k) a y) * b y) + ∑ y, (C ^ n) a y * d y with hRHSdef
  -- the key per-step (monotonicity) inequality
  have hstep : ∀ (n : ℕ) (a : ι),
      ∑ y, (C ^ n) a y * d y
        ≤ (∑ y, (C ^ n) a y * b y) + ∑ z, (C ^ (n + 1)) a z * d z := by
    intro n a
    have hexpand : ∑ z, (C ^ (n + 1)) a z * d z
        = ∑ y, (C ^ n) a y * ∑ z, C y z * d z := by
      have : ∀ z, (C ^ (n + 1)) a z * d z = ∑ y, (C ^ n) a y * C y z * d z := by
        intro z; rw [pow_succ, Matrix.mul_apply, Finset.sum_mul]
      rw [Finset.sum_congr rfl fun z _ => this z, Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [hexpand, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun y _ => ?_
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (hineq y) (hCpow n a y)
  have hmono : ∀ (n : ℕ) (a : ι), RHS n a ≤ RHS (n + 1) a := by
    intro n a
    have hA : ∑ y, (∑ k ∈ Finset.range (n + 1), (C ^ k) a y) * b y
        = (∑ y, (∑ k ∈ Finset.range n, (C ^ k) a y) * b y) + ∑ y, (C ^ n) a y * b y := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun y _ => by rw [Finset.sum_range_succ, add_mul]
    simp only [hRHSdef, hA]
    have := hstep n a
    linarith
  have hbase : ∀ a : ι, RHS 0 a = d a := by
    intro a
    simp [hRHSdef, Matrix.one_apply]
  have hdRHS : ∀ (n : ℕ), d x ≤ RHS n x := by
    intro n
    rw [← hbase x]
    exact (monotone_nat_of_le_succ (fun m => hmono m x)) (Nat.zero_le n)
  -- limit of the first term: partial Neumann sums → resolvent applied to b
  have hAlim : Filter.Tendsto
      (fun n => ∑ y, (∑ k ∈ Finset.range n, (C ^ k) x y) * b y) Filter.atTop
      (nhds (∑ y, (∑' n, (C ^ n) x y) * b y)) := by
    refine tendsto_finset_sum _ fun y _ => ?_
    exact ((hsum x y).hasSum.tendsto_sum_nat).mul_const (b y)
  -- limit of the tail: ∑_y (Cⁿ)_{xy} d_y → 0
  have hTaillim : Filter.Tendsto (fun n => ∑ y, (C ^ n) x y * d y) Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun n => Finset.sum_nonneg fun y _ => mul_nonneg (hCpow n x y) (hd y))
      (g := fun n => (∑ z, d z) * ∑ y, (C ^ n) x y) (fun n => ?_) ?_
    · calc ∑ y, (C ^ n) x y * d y
          ≤ ∑ y, (C ^ n) x y * ∑ z, d z := by
            refine Finset.sum_le_sum fun y _ => ?_
            exact mul_le_mul_of_nonneg_left
              (Finset.single_le_sum (fun z _ => hd z) (Finset.mem_univ y)) (hCpow n x y)
        _ = (∑ y, (C ^ n) x y) * ∑ z, d z := by rw [← Finset.sum_mul]
        _ = (∑ z, d z) * ∑ y, (C ^ n) x y := mul_comm _ _
    · have := (htail x).const_mul (∑ z, d z)
      simpa using this
  have hRHSlim : Filter.Tendsto (fun n => RHS n x) Filter.atTop
      (nhds (∑ y, (∑' n, (C ^ n) x y) * b y)) := by
    have := hAlim.add hTaillim
    simpa [hRHSdef] using this
  exact ge_of_tendsto' hRHSlim hdRHS

variable (G : SimpleGraph ι) [Fintype G.edgeSet] [DecidableRel G.Adj]

omit [Fintype G.edgeSet] in
/-- **The Dobrushin resolvent comparison for the Ising influence matrix** (GJ §17.1): for
`0 ≤ βJ` and `βJ·Δ(G) < 1`, a nonnegative vector `d` satisfying the one-step Dobrushin inequality
`d_x ≤ b_x + ∑_y C_{xy} d_y` (with `C` the single-site influence matrix) is bounded by the
resolvent applied to `b`, `d_x ≤ ∑_y R_{xy} b_y` with `R = dobrushinResolvent`. This consumes the
influence matrix's geometric decay; with the heat-bath telescoping it gives the comparison
theorem. -/
theorem dobrushin_resolvent_comparison {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hΔ : β * J * G.maxDegree < 1) {d b : ι → ℝ} (hd : ∀ x, 0 ≤ d x)
    (hineq : ∀ x, d x ≤ b x + ∑ y, isingInfluenceMatrix G β J x y * d y) (x : ι) :
    d x ≤ ∑ y, dobrushinResolvent G β J x y * b y := by
  simp only [dobrushinResolvent]
  exact vector_le_resolvent_of_le_add_mul (isingInfluenceMatrix_nonneg G hβJ) hd
    (fun a c => isingInfluenceMatrix_summable_pow_apply G hβJ hΔ a c)
    (fun a => isingInfluenceMatrix_pow_rowSum_tendsto_zero G hβJ hΔ a) hineq x

end Dobrushin

end IsingModel
