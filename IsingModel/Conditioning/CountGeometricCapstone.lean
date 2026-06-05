import IsingModel.Conditioning.GeometricTail
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Geometric domination of a counted finite sum (FV §3.7.3 capstone bound)

If a finite family of objects each has a "size" at least `n`, and the number of objects of
size `ℓ` is at most `M^ℓ`, then the weighted sum `∑ q^{size}` is dominated by the geometric
tail `(Mq)^n/(1-Mq)`. This is the analytic capstone of FV §3.7.3: with the objects the
origin components, `size = |C|`, `M = (2d)²`, `q = tanh βJ`, it gives
`⟨σ₀⟩⁺_{B(n)} ≤ (4d²·tanh βJ)^n/(1-4d²·tanh βJ) → 0`, reducing the high-temperature
`m*(β)=0` to the counting bound `#{C : |C|=ℓ} ≤ (2d)^{2ℓ}` (Issue #3613).

* `sum_pow_le_geometric_tail_of_count` — the domination bound.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.3, eq. (3.49), p. 118.
-/

namespace IsingModel

open Finset

/-- **Geometric domination of a counted sum**: for a finite family `S` with a size
function `g` bounded below by `n`, where the number of members of size `ℓ` is at most
`M^ℓ`, the weighted sum `∑_{C} q^{g(C)}` is at most the geometric tail
`(Mq)^n/(1-Mq)` (assuming `0 < Mq < 1`). -/
theorem sum_pow_le_geometric_tail_of_count {α : Type*} (S : Finset α)
    (g : α → ℕ) {q : ℝ} (hq : 0 ≤ q) {M : ℕ} (n : ℕ)
    (hge : ∀ C ∈ S, n ≤ g C)
    (hcount : ∀ ℓ : ℕ, ((S.filter (fun C => g C = ℓ)).card : ℝ) ≤ (M : ℝ) ^ ℓ)
    (hr0 : 0 < (M : ℝ) * q) (hr1 : (M : ℝ) * q < 1) :
    ∑ C ∈ S, q ^ (g C) ≤ ((M : ℝ) * q) ^ n / (1 - (M : ℝ) * q) := by
  classical
  set r := (M : ℝ) * q with hrdef
  -- group by size
  have hgroup : ∑ C ∈ S, q ^ (g C)
      = ∑ ℓ ∈ S.image g, ((S.filter (fun C => g C = ℓ)).card : ℝ) * q ^ ℓ := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := S.image g)
      (fun C hC => Finset.mem_image_of_mem g hC)]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    rw [Finset.sum_congr rfl (fun C hC => by rw [(Finset.mem_filter.mp hC).2]),
      Finset.sum_const, nsmul_eq_mul]
  rw [hgroup]
  -- each size class contributes at most r^ℓ
  have hterm : ∀ ℓ ∈ S.image g,
      ((S.filter (fun C => g C = ℓ)).card : ℝ) * q ^ ℓ ≤ r ^ ℓ := by
    intro ℓ _
    rw [hrdef, mul_pow]
    exact mul_le_mul_of_nonneg_right (hcount ℓ) (pow_nonneg hq ℓ)
  refine (Finset.sum_le_sum hterm).trans ?_
  -- every size in the image is at least n
  have hge' : ∀ ℓ ∈ S.image g, n ≤ ℓ := by
    intro ℓ hℓ
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hℓ
    exact hge C hC
  -- factor out r^n and reindex by ℓ - n
  have hfac : ∑ ℓ ∈ S.image g, r ^ ℓ = r ^ n * ∑ ℓ ∈ S.image g, r ^ (ℓ - n) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ℓ hℓ => ?_)
    rw [← pow_add, Nat.add_sub_cancel' (hge' ℓ hℓ)]
  rw [hfac]
  have hinj : ∀ a ∈ S.image g, ∀ b ∈ S.image g, a - n = b - n → a = b := by
    intro a ha b hb hab
    have h1 := hge' a ha; have h2 := hge' b hb
    omega
  have htail : ∑ ℓ ∈ S.image g, r ^ (ℓ - n) ≤ (1 - r)⁻¹ := by
    rw [← Finset.sum_image hinj, ← tsum_geometric_of_lt_one hr0.le hr1]
    exact Summable.sum_le_tsum _ (fun k _ => pow_nonneg hr0.le k)
      (summable_geometric_of_lt_one hr0.le hr1)
  calc r ^ n * ∑ ℓ ∈ S.image g, r ^ (ℓ - n)
      ≤ r ^ n * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left htail (pow_nonneg hr0.le n)
    _ = r ^ n / (1 - r) := (div_eq_mul_inv _ _).symm

end IsingModel
