import IsingModel.GibbsMeasure
import Mathlib.Data.Fintype.BigOperators

/-!
# Single-site moments of the fourfold duplicate Ising variables (GJ §4.3)

The single-site core of GJ Theorem 4.3.1 for Ising spins (the Ising replacement of the φ⁴
computation (4.3.6)–(4.3.7)): on the sixteen-point fourfold spin space, the Hadamard (Walsh)
variables `u₁ = ξ+χ+ξ'+χ'`, `u₂ = ξ+χ−ξ'−χ'`, `u₃ = ξ−χ+ξ'−χ'`, `u₄ = −ξ+χ+ξ'−χ'` have
non-negative joint moments. The sixteen points split into eight *aligned* points
(`u = ±4·e_r`, contributing `(1 + (−1)^e)·(nonneg)` in cancelling pairs) and eight *generic*
points (`u = 2s` with sign patterns forming the subgroup `{s : s₁s₂s₃s₄ = +1}`), whose
character sum factorises as
`½·(∏(1+(−1)^{eᵢ}) + ∏(1−(−1)^{eᵢ}))` — manifestly non-negative.

* `signQuad` etc. — the four Hadamard variables on the quadruple site space.
* `siteMoment` — the joint moment `∑_v u₁^k u₂^l u₃^m u₄^n`.
* `siteMoment_eq` — the closed sixteen-term form.
* `siteMoment_nonneg` — **the Ising (4.3.6)**: all joint moments are non-negative.

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.3,
Theorem 4.3.1, pp. 59–61; J. L. Lebowitz, Comm. Math. Phys. 35 (1974).
-/

namespace IsingModel

namespace Lebowitz

/-- The fourfold single-site spin space: four independent copies `(ξ, χ, ξ', χ')` of one
Ising spin. -/
abbrev SiteQuad : Type := Spin × Spin × Spin × Spin

/-- Sum over the two spins, explicitly. -/
theorem sum_spin (f : Spin → ℝ) : ∑ s : Spin, f s = f Spin.up + f Spin.down := by
  rw [show (Finset.univ : Finset Spin) = {Spin.up, Spin.down} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

/-- The spin sign of the first copy. -/
noncomputable def s₁ (v : SiteQuad) : ℝ := Spin.sign ℝ v.1
/-- The spin sign of the second copy. -/
noncomputable def s₂ (v : SiteQuad) : ℝ := Spin.sign ℝ v.2.1
/-- The spin sign of the third copy. -/
noncomputable def s₃ (v : SiteQuad) : ℝ := Spin.sign ℝ v.2.2.1
/-- The spin sign of the fourth copy. -/
noncomputable def s₄ (v : SiteQuad) : ℝ := Spin.sign ℝ v.2.2.2

/-- First Hadamard variable: `u₁ = ξ + χ + ξ' + χ'` (GJ's `2α`). -/
noncomputable def u₁ (v : SiteQuad) : ℝ := s₁ v + s₂ v + s₃ v + s₄ v
/-- Second Hadamard variable: `u₂ = ξ + χ − ξ' − χ'` (GJ's `2β`). -/
noncomputable def u₂ (v : SiteQuad) : ℝ := s₁ v + s₂ v - s₃ v - s₄ v
/-- Third Hadamard variable: `u₃ = ξ − χ + ξ' − χ'` (GJ's `2γ`). -/
noncomputable def u₃ (v : SiteQuad) : ℝ := s₁ v - s₂ v + s₃ v - s₄ v
/-- Fourth Hadamard variable: `u₄ = −ξ + χ + ξ' − χ'` (GJ's `2δ`; the sign convention is
fixed so that the eight generic sign patterns form the **even** subgroup
`{s : s₁s₂s₃s₄ = +1}` — with the opposite sign the patterns are odd and the moment
positivity fails, e.g. for exponents `(1,1,1,1)`). -/
noncomputable def u₄ (v : SiteQuad) : ℝ := -s₁ v + s₂ v + s₃ v - s₄ v

/-- **Single-site joint moment** of the four Hadamard variables. -/
noncomputable def siteMoment (k l m n : ℕ) : ℝ :=
  ∑ v : SiteQuad, u₁ v ^ k * u₂ v ^ l * u₃ v ^ m * u₄ v ^ n

/-- **Closed sixteen-term form of the site moment**: eight aligned points (`±4` in one
variable, `0` in the others) and eight generic points (all variables `±2`, sign patterns in
the even subgroup). -/
theorem siteMoment_eq (k l m n : ℕ) :
    siteMoment k l m n =
      ((4 : ℝ) ^ k * 0 ^ l * 0 ^ m * 0 ^ n + (-4 : ℝ) ^ k * 0 ^ l * 0 ^ m * 0 ^ n) +
      ((0 : ℝ) ^ k * 4 ^ l * 0 ^ m * 0 ^ n + (0 : ℝ) ^ k * (-4) ^ l * 0 ^ m * 0 ^ n) +
      ((0 : ℝ) ^ k * 0 ^ l * 4 ^ m * 0 ^ n + (0 : ℝ) ^ k * 0 ^ l * (-4) ^ m * 0 ^ n) +
      ((0 : ℝ) ^ k * 0 ^ l * 0 ^ m * 4 ^ n + (0 : ℝ) ^ k * 0 ^ l * 0 ^ m * (-4) ^ n) +
      ((2 : ℝ) ^ k * 2 ^ l * 2 ^ m * 2 ^ n + (-2 : ℝ) ^ k * (-2) ^ l * (-2) ^ m * (-2) ^ n) +
      ((2 : ℝ) ^ k * 2 ^ l * (-2) ^ m * (-2) ^ n +
        (-2 : ℝ) ^ k * (-2) ^ l * 2 ^ m * 2 ^ n) +
      ((2 : ℝ) ^ k * (-2) ^ l * 2 ^ m * (-2) ^ n +
        (-2 : ℝ) ^ k * 2 ^ l * (-2) ^ m * 2 ^ n) +
      ((2 : ℝ) ^ k * (-2) ^ l * (-2) ^ m * 2 ^ n +
        (-2 : ℝ) ^ k * 2 ^ l * 2 ^ m * (-2) ^ n) := by
  unfold siteMoment
  rw [Fintype.sum_prod_type, sum_spin]
  simp only [Fintype.sum_prod_type, sum_spin]
  unfold u₁ u₂ u₃ u₄ s₁ s₂ s₃ s₄
  simp only [Spin.sign, Spin.toSign]
  push_cast
  ring

/-- `0 ≤ 1 + (−1)^e` for the real sign `(−1)^e`. -/
theorem one_add_neg_one_pow_nonneg (e : ℕ) : (0 : ℝ) ≤ 1 + (-1) ^ e := by
  rcases Nat.even_or_odd e with he | he
  · rw [he.neg_one_pow]; norm_num
  · rw [he.neg_one_pow]; norm_num

/-- `0 ≤ 1 − (−1)^e` for the real sign `(−1)^e`. -/
theorem one_sub_neg_one_pow_nonneg (e : ℕ) : (0 : ℝ) ≤ 1 - (-1) ^ e := by
  rcases Nat.even_or_odd e with he | he
  · rw [he.neg_one_pow]; norm_num
  · rw [he.neg_one_pow]; norm_num

/-- **Single-site moment positivity — the Ising (4.3.6)**: every joint moment of the four
Hadamard variables over the sixteen-point fourfold spin space is non-negative. The aligned
points contribute `(1 + (−1)^e)` pair sums against non-negative bases, and the generic
character sum factorises as
`½·2^{k+l+m+n}·(∏(1+(−1)^{eᵢ}) + ∏(1−(−1)^{eᵢ}))`. -/
theorem siteMoment_nonneg (k l m n : ℕ) : 0 ≤ siteMoment k l m n := by
  have hneg : ∀ (x : ℝ) (e : ℕ), (-x) ^ e = (-1) ^ e * x ^ e := by
    intro x e
    rw [← neg_one_mul, mul_pow]
  have hkey : 2 * siteMoment k l m n =
      2 * ((1 + (-1) ^ k) * ((4 : ℝ) ^ k * 0 ^ l * 0 ^ m * 0 ^ n)
        + (1 + (-1) ^ l) * ((0 : ℝ) ^ k * 4 ^ l * 0 ^ m * 0 ^ n)
        + (1 + (-1) ^ m) * ((0 : ℝ) ^ k * 0 ^ l * 4 ^ m * 0 ^ n)
        + (1 + (-1) ^ n) * ((0 : ℝ) ^ k * 0 ^ l * 0 ^ m * 4 ^ n))
      + (2 : ℝ) ^ k * 2 ^ l * 2 ^ m * 2 ^ n *
        ((1 + (-1) ^ k) * (1 + (-1) ^ l) * (1 + (-1) ^ m) * (1 + (-1) ^ n)
          + (1 - (-1) ^ k) * (1 - (-1) ^ l) * (1 - (-1) ^ m) * (1 - (-1) ^ n)) := by
    rw [siteMoment_eq, hneg 4 k, hneg 4 l, hneg 4 m, hneg 4 n,
      hneg 2 k, hneg 2 l, hneg 2 m, hneg 2 n]
    ring
  have hgen : (0 : ℝ) ≤
      (1 + (-1) ^ k) * (1 + (-1) ^ l) * (1 + (-1) ^ m) * (1 + (-1) ^ n)
        + (1 - (-1) ^ k) * (1 - (-1) ^ l) * (1 - (-1) ^ m) * (1 - (-1) ^ n) :=
    add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (one_add_neg_one_pow_nonneg k)
        (one_add_neg_one_pow_nonneg l)) (one_add_neg_one_pow_nonneg m))
        (one_add_neg_one_pow_nonneg n))
      (mul_nonneg (mul_nonneg (mul_nonneg (one_sub_neg_one_pow_nonneg k)
        (one_sub_neg_one_pow_nonneg l)) (one_sub_neg_one_pow_nonneg m))
        (one_sub_neg_one_pow_nonneg n))
  have haligned : ∀ (e : ℕ) (x : ℝ), 0 ≤ x → (0 : ℝ) ≤ (1 + (-1) ^ e) * x := fun e x hx =>
    mul_nonneg (one_add_neg_one_pow_nonneg e) hx
  have h2M : (0 : ℝ) ≤ 2 * siteMoment k l m n := by
    rw [hkey]
    refine add_nonneg ?_ (mul_nonneg (by positivity) hgen)
    have t1 := haligned k ((4 : ℝ) ^ k * 0 ^ l * 0 ^ m * 0 ^ n) (by positivity)
    have t2 := haligned l ((0 : ℝ) ^ k * 4 ^ l * 0 ^ m * 0 ^ n) (by positivity)
    have t3 := haligned m ((0 : ℝ) ^ k * 0 ^ l * 4 ^ m * 0 ^ n) (by positivity)
    have t4 := haligned n ((0 : ℝ) ^ k * 0 ^ l * 0 ^ m * 4 ^ n) (by positivity)
    linarith
  linarith

end Lebowitz

end IsingModel
