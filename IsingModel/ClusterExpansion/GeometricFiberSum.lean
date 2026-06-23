import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace IsingModel

open Finset

/-- **Finite fiber-count geometric bound.**  Suppose a finite family `s` is graded by
`size`, all sizes are at most `M`, each weight is bounded by `A * a ^ size x`, and each
fiber of size `n` has cardinality at most `B ^ n`.  Then the total weight is bounded by
the corresponding finite geometric majorant with ratio `a * B`. -/
theorem sum_le_geometric_of_fiber_card_le
    {α : Type*}
    (s : Finset α) (size : α → ℕ) (w : α → ℝ)
    (A a B : ℝ) (M : ℕ)
    (hsize : ∀ x ∈ s, size x ≤ M)
    (hw_nonneg : ∀ x ∈ s, 0 ≤ w x)
    (hw_le : ∀ x ∈ s, w x ≤ A * a ^ size x)
    (hcount : ∀ n, ((s.filter fun x => size x = n).card : ℝ) ≤ B ^ n)
    (hA : 0 ≤ A) (ha : 0 ≤ a) (hB : 0 ≤ B) :
    (∑ x ∈ s, w x) ≤ A * ∑ n ∈ Finset.range (M + 1), (a * B) ^ n := by
  classical
  have _ : 0 ≤ ∑ x ∈ s, w x := Finset.sum_nonneg hw_nonneg
  have _ : ∀ n : ℕ, 0 ≤ B ^ n := fun n => pow_nonneg hB n
  have hmaps : ∀ x ∈ s, size x ∈ Finset.range (M + 1) := by
    intro x hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hsize x hx))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps w]
  calc
    (∑ n ∈ Finset.range (M + 1), ∑ x ∈ s.filter (fun x => size x = n), w x)
        ≤ ∑ n ∈ Finset.range (M + 1), A * (a * B) ^ n := by
      refine Finset.sum_le_sum ?_
      intro n hn
      let fiber : Finset α := s.filter fun x => size x = n
      have hsum_le : (∑ x ∈ fiber, w x) ≤ ∑ x ∈ fiber, A * a ^ n := by
        refine Finset.sum_le_sum ?_
        intro x hx
        have hx_s : x ∈ s := (Finset.mem_filter.mp hx).1
        have hx_size : size x = n := (Finset.mem_filter.mp hx).2
        calc
          w x ≤ A * a ^ size x := hw_le x hx_s
          _ = A * a ^ n := by rw [hx_size]
      have hconst : (∑ x ∈ fiber, A * a ^ n) = (fiber.card : ℝ) * (A * a ^ n) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      calc
        (∑ x ∈ s.filter (fun x => size x = n), w x)
            = ∑ x ∈ fiber, w x := by rfl
        _ ≤ ∑ x ∈ fiber, A * a ^ n := hsum_le
        _ = (fiber.card : ℝ) * (A * a ^ n) := hconst
        _ ≤ B ^ n * (A * a ^ n) := by
          refine mul_le_mul_of_nonneg_right ?_ ?_
          · simpa [fiber] using hcount n
          · exact mul_nonneg hA (pow_nonneg ha n)
        _ = A * (a * B) ^ n := by
          rw [mul_pow]
          ring
    _ = A * ∑ n ∈ Finset.range (M + 1), (a * B) ^ n := by
      rw [Finset.mul_sum]

/-- **Closed fiber-count geometric bound.**  Under the hypotheses of
`sum_le_geometric_of_fiber_card_le`, if the geometric ratio `a * B` is strictly less
than `1`, then the finite majorant is bounded by the closed geometric-series value
`A / (1 - a * B)`. -/
theorem sum_le_geometric_closed_of_fiber_card_le
    {α : Type*}
    (s : Finset α) (size : α → ℕ) (w : α → ℝ)
    (A a B : ℝ) (M : ℕ)
    (hsize : ∀ x ∈ s, size x ≤ M)
    (hw_nonneg : ∀ x ∈ s, 0 ≤ w x)
    (hw_le : ∀ x ∈ s, w x ≤ A * a ^ size x)
    (hcount : ∀ n, ((s.filter fun x => size x = n).card : ℝ) ≤ B ^ n)
    (hA : 0 ≤ A) (ha : 0 ≤ a) (hB : 0 ≤ B) (hq : a * B < 1) :
    (∑ x ∈ s, w x) ≤ A / (1 - a * B) := by
  have hfinite := sum_le_geometric_of_fiber_card_le s size w A a B M hsize hw_nonneg hw_le
    hcount hA ha hB
  have hratio_nonneg : 0 ≤ a * B := mul_nonneg ha hB
  have hsummable : Summable fun n : ℕ => (a * B) ^ n :=
    summable_geometric_of_lt_one hratio_nonneg hq
  have hpartial : (∑ n ∈ Finset.range (M + 1), (a * B) ^ n) ≤ (1 - a * B)⁻¹ := by
    calc
      (∑ n ∈ Finset.range (M + 1), (a * B) ^ n)
          ≤ ∑' n : ℕ, (a * B) ^ n := by
        exact hsummable.sum_le_tsum (Finset.range (M + 1))
          (fun n hn => pow_nonneg hratio_nonneg n)
      _ = (1 - a * B)⁻¹ := tsum_geometric_of_lt_one hratio_nonneg hq
  calc
    (∑ x ∈ s, w x) ≤ A * ∑ n ∈ Finset.range (M + 1), (a * B) ^ n := hfinite
    _ ≤ A * (1 - a * B)⁻¹ := mul_le_mul_of_nonneg_left hpartial hA
    _ = A / (1 - a * B) := by rw [div_eq_mul_inv]

end IsingModel
