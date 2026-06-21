import IsingModel.Dobrushin.SingleSiteInfluenceMatrix

/-!
# High-temperature sufficiency of the single-site Dobrushin condition (GJ §17.1)

The single-site Dobrushin uniqueness condition `tanh(βJ)·deg(x) < 1`
(`isingDobrushin_condition`) is satisfied in the high-temperature regime. Since `tanh(t) ≤ t` for
`t ≥ 0`, the Dobrushin interaction sum is dominated by `βJ·deg(x)`, so the **same** high-temperature
threshold `βJ·deg(x) < 1` used by the Simon–Lieb decay results already implies Dobrushin's
condition.

* `tanh_le_self` — `tanh t ≤ t` for `0 ≤ t` (absent from Mathlib; via the auxiliary monotone
  function `t·cosh t − sinh t`).
* `isingInfluence_rowSum_le` — the Dobrushin interaction sum is `≤ βJ·deg(x)` (for `0 ≤ βJ`).
* `isingDobrushin_condition_of_high_temp` — `βJ·deg(x) < 1` implies Dobrushin's condition at `x`.
* `isingDobrushin_condition_of_high_temp_maxDegree` — the uniform form: `βJ·Δ(G) < 1` (with `Δ(G)`
  the maximum degree) implies Dobrushin's condition at every site.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306.
-/

namespace IsingModel

namespace Dobrushin

open Real

/-- **`tanh` is below the identity on `[0, ∞)`**: `tanh t ≤ t` for `0 ≤ t`. (Mathlib has no `tanh`
derivative or `tanh ≤ id` lemma.) Since `cosh > 0`, this is `sinh t ≤ t·cosh t`, and the auxiliary
function `g(t) = t·cosh t − sinh t` is monotone on `[0, ∞)` (its derivative `t·sinh t` is
nonnegative there) with `g(0) = 0`. -/
theorem tanh_le_self {t : ℝ} (ht : 0 ≤ t) : Real.tanh t ≤ t := by
  rw [Real.tanh_eq_sinh_div_cosh, div_le_iff₀ (Real.cosh_pos t)]
  have hderiv : ∀ s : ℝ,
      HasDerivAt (fun u => u * Real.cosh u - Real.sinh u) (s * Real.sinh s) s := by
    intro s
    have h : HasDerivAt (fun u => u * Real.cosh u - Real.sinh u)
        (1 * Real.cosh s + s * Real.sinh s - Real.cosh s) s :=
      ((hasDerivAt_id s).mul (Real.hasDerivAt_cosh s)).sub (Real.hasDerivAt_sinh s)
    have he : 1 * Real.cosh s + s * Real.sinh s - Real.cosh s = s * Real.sinh s := by ring
    rwa [he] at h
  have hmono : MonotoneOn (fun u => u * Real.cosh u - Real.sinh u) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      ((continuous_id.mul Real.continuous_cosh).sub Real.continuous_sinh).continuousOn
      (fun s _ => (hderiv s).differentiableAt.differentiableWithinAt) ?_
    intro s hs
    rw [interior_Ici, Set.mem_Ioi] at hs
    rw [(hderiv s).deriv]
    exact mul_nonneg hs.le (Real.sinh_nonneg_iff.mpr hs.le)
  have h0 := hmono Set.self_mem_Ici (Set.mem_Ici.mpr ht) ht
  simp only [zero_mul, Real.sinh_zero, sub_zero] at h0
  linarith [h0]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (G : SimpleGraph ι) [Fintype G.edgeSet] [DecidableRel G.Adj]

omit [Fintype G.edgeSet] in
/-- **The Dobrushin interaction sum is dominated by `βJ·deg(x)`** at high temperature: for `0 ≤ βJ`,
`∑_y c_{xy} = deg(x)·tanh(βJ) ≤ βJ·deg(x)` (since `tanh(βJ) ≤ βJ`). -/
theorem isingInfluence_rowSum_le {β J : ℝ} (hβJ : 0 ≤ β * J) (x : ι) :
    ∑ y, isingInfluence G β J x y ≤ β * J * G.degree x := by
  rw [isingInfluence_rowSum, mul_comm]
  exact mul_le_mul_of_nonneg_right (tanh_le_self hβJ) (Nat.cast_nonneg _)

omit [Fintype G.edgeSet] [DecidableEq ι] in
/-- **High-temperature sufficiency of Dobrushin's condition** (GJ §17.1): if `0 ≤ βJ` and the
high-temperature threshold `βJ·deg(x) < 1` holds, then Dobrushin's uniqueness condition
`tanh(βJ)·deg(x) < 1` holds at `x`. This is the same `βJ·deg < 1` threshold as the Simon–Lieb decay
results. -/
theorem isingDobrushin_condition_of_high_temp {β J : ℝ} (hβJ : 0 ≤ β * J) (x : ι)
    (hx : β * J * G.degree x < 1) : isingDobrushin_condition G β J x := by
  rw [isingDobrushin_condition, mul_comm]
  calc (G.degree x : ℝ) * Real.tanh (β * J)
      ≤ (G.degree x : ℝ) * (β * J) :=
        mul_le_mul_of_nonneg_left (tanh_le_self hβJ) (Nat.cast_nonneg _)
    _ = β * J * G.degree x := by ring
    _ < 1 := hx

omit [Fintype G.edgeSet] [DecidableEq ι] in
/-- **Uniform high-temperature sufficiency** (GJ §17.1): if `0 ≤ βJ` and `βJ·Δ(G) < 1` with `Δ(G)`
the maximum degree, then Dobrushin's condition holds at **every** site (each degree is at most the
maximum degree). -/
theorem isingDobrushin_condition_of_high_temp_maxDegree {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hΔ : β * J * G.maxDegree < 1) (x : ι) : isingDobrushin_condition G β J x := by
  refine isingDobrushin_condition_of_high_temp G hβJ x (lt_of_le_of_lt ?_ hΔ)
  exact mul_le_mul_of_nonneg_left
    (by exact_mod_cast G.degree_le_maxDegree x) hβJ

end Dobrushin

end IsingModel
