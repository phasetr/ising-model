import IsingModel.Conditioning.Reflection.EuclideanBasic

/-!
# Reflection positivity — Euclidean polarization, norm-squared, and constant formulas

This module is part of the split `IsingModel.Conditioning.Reflection`
development. It collects the polarization identity, `norm_sq_add` /
`norm_sq_sub`, the Pythagorean identity, `norm_sq` for scalar/neg/zero/one
inputs, small-`Fin` specialisations (empty / single / two / three), and
constant-vector helpers.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §10.4, pp.~198--200.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Euclidean polarization identity**:
`4·∑ xᵢ·yᵢ = ∑ (xᵢ + yᵢ)² - ∑ (xᵢ - yᵢ)²`. Expresses the inner
product as a difference of squared norms. -/
theorem euclidean_polarization {n : ℕ} (x y : Fin n → ℝ) :
    4 * (∑ i : Fin n, x i * y i)
      = (∑ i : Fin n, (x i + y i) ^ 2) - (∑ i : Fin n, (x i - y i) ^ 2) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean norm squared of a sum**:
`∑ (xᵢ + yᵢ)² = ∑ xᵢ² + 2·∑ xᵢ·yᵢ + ∑ yᵢ²`. -/
theorem euclidean_norm_sq_add {n : ℕ} (x y : Fin n → ℝ) :
    (∑ i : Fin n, (x i + y i) ^ 2)
      = (∑ i : Fin n, (x i) ^ 2) + 2 * (∑ i : Fin n, x i * y i)
          + (∑ i : Fin n, (y i) ^ 2) := by
  have h : ∀ i : Fin n, (x i + y i) ^ 2 = (x i) ^ 2 + 2 * (x i * y i) + (y i) ^ 2 :=
    fun i => by ring
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- **Euclidean norm squared of a difference**:
`∑ (xᵢ - yᵢ)² = ∑ xᵢ² - 2·∑ xᵢ·yᵢ + ∑ yᵢ²`. -/
theorem euclidean_norm_sq_sub {n : ℕ} (x y : Fin n → ℝ) :
    (∑ i : Fin n, (x i - y i) ^ 2)
      = (∑ i : Fin n, (x i) ^ 2) - 2 * (∑ i : Fin n, x i * y i)
          + (∑ i : Fin n, (y i) ^ 2) := by
  have h : ∀ i : Fin n, (x i - y i) ^ 2 = (x i) ^ 2 - 2 * (x i * y i) + (y i) ^ 2 :=
    fun i => by ring
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- **Euclidean Pythagorean identity**: if `x, y : Fin n → ℝ` are
orthogonal (`∑ xᵢ·yᵢ = 0`), then `∑ (xᵢ+yᵢ)² = ∑ xᵢ² + ∑ yᵢ²`.
Immediate from `euclidean_norm_sq_add` with the middle term vanishing. -/
theorem euclidean_pythagorean {n : ℕ} (x y : Fin n → ℝ)
    (h_ortho : (∑ i : Fin n, x i * y i) = 0) :
    (∑ i : Fin n, (x i + y i) ^ 2)
      = (∑ i : Fin n, (x i) ^ 2) + (∑ i : Fin n, (y i) ^ 2) := by
  rw [euclidean_norm_sq_add x y, h_ortho]
  ring

/-- **Euclidean norm squared under scalar multiplication**:
`∑ (c · xᵢ)² = c² · ∑ xᵢ²`. -/
theorem euclidean_norm_sq_smul {n : ℕ} (c : ℝ) (x : Fin n → ℝ) :
    (∑ i : Fin n, (c * x i) ^ 2) = c ^ 2 * (∑ i : Fin n, (x i) ^ 2) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean norm squared of negation**: `∑ (-xᵢ)² = ∑ xᵢ²`. -/
theorem euclidean_norm_sq_neg {n : ℕ} (x : Fin n → ℝ) :
    (∑ i : Fin n, (-x i) ^ 2) = (∑ i : Fin n, (x i) ^ 2) := by
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean norm squared of zero function**: `∑ (0 : ℝ)² = 0`. -/
theorem euclidean_norm_sq_zero_fn {n : ℕ} :
    (∑ _ : Fin n, ((0 : ℝ)) ^ 2) = 0 := by
  apply Finset.sum_eq_zero
  intros i _
  ring

/-- **Euclidean sum swap**: for a double-indexed family
`f : Fin m → Fin n → ℝ`, swap the order of summation:
`∑ i, ∑ j, f i j = ∑ j, ∑ i, f i j`. -/
theorem euclidean_sum_swap {m n : ℕ} (f : Fin m → Fin n → ℝ) :
    (∑ i : Fin m, ∑ j : Fin n, f i j) = ∑ j : Fin n, ∑ i : Fin m, f i j :=
  Finset.sum_comm

/-- **Empty-dimension Euclidean norm squared**: `∑ i : Fin 0, (xᵢ)² = 0`. -/
theorem euclidean_norm_sq_empty (x : Fin 0 → ℝ) :
    (∑ i : Fin 0, (x i) ^ 2) = 0 := by
  simp

/-- **Single-element Euclidean norm squared**: `∑ i : Fin 1, (xᵢ)² = (x 0)²`. -/
theorem euclidean_norm_sq_single (x : Fin 1 → ℝ) :
    (∑ i : Fin 1, (x i) ^ 2) = (x 0) ^ 2 := by
  simp

/-- **Two-element Euclidean norm squared**: `∑ i : Fin 2, (xᵢ)² = (x 0)² + (x 1)²`. -/
theorem euclidean_norm_sq_two (x : Fin 2 → ℝ) :
    (∑ i : Fin 2, (x i) ^ 2) = (x 0) ^ 2 + (x 1) ^ 2 := by
  simp [Fin.sum_univ_two]

/-- **Three-element Euclidean norm squared**:
`∑ i : Fin 3, (xᵢ)² = (x 0)² + (x 1)² + (x 2)²`. -/
theorem euclidean_norm_sq_three (x : Fin 3 → ℝ) :
    (∑ i : Fin 3, (x i) ^ 2) = (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
  simp [Fin.sum_univ_three]

/-- **Single-element Euclidean inner**:
`∑ i : Fin 1, x i * y i = x 0 * y 0`. -/
theorem euclidean_inner_single (x y : Fin 1 → ℝ) :
    (∑ i : Fin 1, x i * y i) = x 0 * y 0 := by
  simp

/-- **Two-element Euclidean inner**:
`∑ i : Fin 2, x i * y i = x 0 * y 0 + x 1 * y 1`. -/
theorem euclidean_inner_two (x y : Fin 2 → ℝ) :
    (∑ i : Fin 2, x i * y i) = x 0 * y 0 + x 1 * y 1 := by
  simp [Fin.sum_univ_two]

/-- **Three-element Euclidean inner**:
`∑ i : Fin 3, x i * y i = x 0 * y 0 + x 1 * y 1 + x 2 * y 2`. -/
theorem euclidean_inner_three (x y : Fin 3 → ℝ) :
    (∑ i : Fin 3, x i * y i) = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp [Fin.sum_univ_three]

/-- **Euclidean constant-function norm squared**: `∑ c² over Fin n = n · c²`. -/
theorem euclidean_norm_sq_const {n : ℕ} (c : ℝ) :
    (∑ _ : Fin n, c ^ 2) = n * c ^ 2 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Euclidean constant-constant inner**: `∑ c · d over Fin n = n · c · d`. -/
theorem euclidean_inner_const {n : ℕ} (c d : ℝ) :
    (∑ _ : Fin n, c * d) = n * (c * d) := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Euclidean norm squared of constant-one vector**: `∑ 1² over Fin n = n`. -/
theorem euclidean_norm_sq_one_fn {n : ℕ} :
    (∑ _ : Fin n, ((1 : ℝ)) ^ 2) = n := by
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- **Euclidean inner with constant-one vector equals sum**:
`∑ i, (fun _ => 1) i · x i = ∑ i, x i`. -/
theorem euclidean_inner_one_fn_left {n : ℕ} (x : Fin n → ℝ) :
    (∑ i : Fin n, (1 : ℝ) * x i) = ∑ i : Fin n, x i := by
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean inner with constant-one right vector equals sum**:
`∑ i, x i · 1 = ∑ i, x i`. -/
theorem euclidean_inner_one_fn_right {n : ℕ} (x : Fin n → ℝ) :
    (∑ i : Fin n, x i * (1 : ℝ)) = ∑ i : Fin n, x i := by
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean inner of negated pair**: `∑ (-xᵢ) · (-yᵢ) = ∑ xᵢ · yᵢ`. -/
theorem euclidean_inner_neg_neg {n : ℕ} (x y : Fin n → ℝ) :
    (∑ i : Fin n, (-x i) * (-y i)) = ∑ i : Fin n, x i * y i := by
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean inner with scalar multiples on both sides**:
`∑ (c·xᵢ) · (d·yᵢ) = (c·d) · ∑ xᵢ · yᵢ`. -/
theorem euclidean_inner_smul_smul {n : ℕ} (c d : ℝ) (x y : Fin n → ℝ) :
    (∑ i : Fin n, (c * x i) * (d * y i)) = c * d * (∑ i : Fin n, x i * y i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean scale by 1 is identity**: `∑ 1·xᵢ · 1·yᵢ = ∑ xᵢ·yᵢ`. -/
theorem euclidean_inner_one_smul_one_smul {n : ℕ} (x y : Fin n → ℝ) :
    (∑ i : Fin n, ((1 : ℝ) * x i) * ((1 : ℝ) * y i)) = ∑ i : Fin n, x i * y i := by
  rw [euclidean_inner_smul_smul]
  ring

/-- **Euclidean scale by 0 vanishes, left side**: `∑ 0·xᵢ · yᵢ = 0`. -/
theorem euclidean_inner_zero_smul_left {n : ℕ} (x y : Fin n → ℝ) :
    (∑ i : Fin n, ((0 : ℝ) * x i) * y i) = 0 := by
  apply Finset.sum_eq_zero
  intros i _
  ring

/-- **Euclidean scale by 0 vanishes, right side**: `∑ xᵢ · 0·yᵢ = 0`. -/
theorem euclidean_inner_zero_smul_right {n : ℕ} (x y : Fin n → ℝ) :
    (∑ i : Fin n, x i * ((0 : ℝ) * y i)) = 0 := by
  apply Finset.sum_eq_zero
  intros i _
  ring

end IsingModel
