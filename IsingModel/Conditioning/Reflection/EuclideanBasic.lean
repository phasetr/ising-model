import IsingModel.Conditioning.Reflection.Predicates

/-!
# Reflection positivity — basic Euclidean inner product on `Fin n → ℝ`

This module is part of the split `IsingModel.Conditioning.Reflection`
development. It provides the dot product as a concrete reflection-positive
example, the classical Cauchy--Schwarz inequality (and its absolute form),
and the basic linearity / symmetry / norm-squared identities for the
Euclidean inner product.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §10.4, pp.~198--200.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Euclidean example**: the dot product `(·, ·)` on `Fin n → ℝ`
defined as `fun x y => ∑ i, x i * y i` is reflection positive. Concrete
instance of `ReflectionPositive` obtained from a sum of nonneg diagonal
squares `x i * x i = (x i)² ≥ 0`. -/
theorem ReflectionPositive.euclidean_dot {n : ℕ} :
    ReflectionPositive (fun x y : Fin n → ℝ => ∑ i : Fin n, x i * y i) := by
  intro x
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

/-- **Classical Cauchy-Schwarz on `Fin n → ℝ`**: for `x, y : Fin n → ℝ`,
`(∑ xᵢ yᵢ)² ≤ (∑ xᵢ²) · (∑ yᵢ²)`. Direct consequence of mathlib's
`Finset.sum_mul_sq_le_sq_mul_sq`; a concrete instance of the RP
framework's Cauchy-Schwarz pattern on the Euclidean inner product. -/
theorem euclidean_cauchy_schwarz {n : ℕ} (x y : Fin n → ℝ) :
    (∑ i : Fin n, x i * y i) ^ 2
      ≤ (∑ i : Fin n, (x i) ^ 2) * (∑ i : Fin n, (y i) ^ 2) :=
  Finset.sum_mul_sq_le_sq_mul_sq _ x y

/-- **Euclidean Cauchy-Schwarz abs form**: `|∑ xᵢ yᵢ| ≤ √((∑ xᵢ²) · (∑ yᵢ²))`
on `Fin n → ℝ`. Direct sqrt-monotone consequence of
`euclidean_cauchy_schwarz`. -/
theorem abs_euclidean_inner_le_sqrt {n : ℕ} (x y : Fin n → ℝ) :
    |∑ i : Fin n, x i * y i|
      ≤ Real.sqrt ((∑ i : Fin n, (x i) ^ 2) * (∑ i : Fin n, (y i) ^ 2)) := by
  have hsq := euclidean_cauchy_schwarz x y
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq_eq_abs] at this

/-- **Euclidean norm-squared nonneg**: `0 ≤ ∑ (xᵢ)²` on `Fin n → ℝ`. -/
theorem euclidean_norm_sq_nonneg {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ ∑ i : Fin n, (x i) ^ 2 :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- **Euclidean dot product is symmetric**: `∑ xᵢ yᵢ = ∑ yᵢ xᵢ`. -/
theorem euclidean_inner_comm {n : ℕ} (x y : Fin n → ℝ) :
    ∑ i : Fin n, x i * y i = ∑ i : Fin n, y i * x i := by
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean self-inner = norm squared**: `∑ xᵢ · xᵢ = ∑ (xᵢ)²`. -/
theorem euclidean_inner_self {n : ℕ} (x : Fin n → ℝ) :
    ∑ i : Fin n, x i * x i = ∑ i : Fin n, (x i) ^ 2 := by
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean non-degeneracy**: `∑ (xᵢ)² = 0 ↔ ∀ i, x i = 0`. -/
theorem euclidean_norm_sq_eq_zero_iff {n : ℕ} (x : Fin n → ℝ) :
    (∑ i : Fin n, (x i) ^ 2) = 0 ↔ ∀ i, x i = 0 := by
  constructor
  · intro h i
    have h_each : ∀ j ∈ Finset.univ, (x j) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp h
    exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp (h_each i (Finset.mem_univ _))
  · intro h
    apply Finset.sum_eq_zero
    intros i _
    rw [h i]; ring

/-- **Euclidean dot product vanishes with zero left-argument**:
`∑ (fun i => 0) i * yᵢ = 0`. -/
theorem euclidean_inner_zero_left {n : ℕ} (y : Fin n → ℝ) :
    ∑ i : Fin n, (0 : ℝ) * y i = 0 := by
  apply Finset.sum_eq_zero
  intros i _
  ring

/-- **Euclidean dot product vanishes with zero right-argument**:
`∑ xᵢ · (fun _ => 0) i = 0`. -/
theorem euclidean_inner_zero_right {n : ℕ} (x : Fin n → ℝ) :
    ∑ i : Fin n, x i * (0 : ℝ) = 0 := by
  apply Finset.sum_eq_zero
  intros i _
  ring

/-- **Euclidean dot product with constant-one left-argument**:
`∑ 1 · yᵢ = ∑ yᵢ`. -/
theorem euclidean_inner_one_left {n : ℕ} (y : Fin n → ℝ) :
    ∑ i : Fin n, (1 : ℝ) * y i = ∑ i : Fin n, y i := by
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean dot product with constant-one right-argument**:
`∑ xᵢ · 1 = ∑ xᵢ`. -/
theorem euclidean_inner_one_right {n : ℕ} (x : Fin n → ℝ) :
    ∑ i : Fin n, x i * (1 : ℝ) = ∑ i : Fin n, x i := by
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean dot product distributes over left addition**:
`∑ (xᵢ + yᵢ) · zᵢ = ∑ xᵢ · zᵢ + ∑ yᵢ · zᵢ`. -/
theorem euclidean_inner_add_left {n : ℕ} (x y z : Fin n → ℝ) :
    ∑ i : Fin n, (x i + y i) * z i
      = (∑ i : Fin n, x i * z i) + (∑ i : Fin n, y i * z i) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean dot product distributes over right addition**:
`∑ xᵢ · (yᵢ + zᵢ) = ∑ xᵢ · yᵢ + ∑ xᵢ · zᵢ`. -/
theorem euclidean_inner_add_right {n : ℕ} (x y z : Fin n → ℝ) :
    ∑ i : Fin n, x i * (y i + z i)
      = (∑ i : Fin n, x i * y i) + (∑ i : Fin n, x i * z i) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean dot product pulls out left scalar**:
`∑ (c · xᵢ) · yᵢ = c · ∑ xᵢ · yᵢ`. -/
theorem euclidean_inner_smul_left {n : ℕ} (c : ℝ) (x y : Fin n → ℝ) :
    ∑ i : Fin n, (c * x i) * y i = c * ∑ i : Fin n, x i * y i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean dot product pulls out right scalar**:
`∑ xᵢ · (c · yᵢ) = c · ∑ xᵢ · yᵢ`. -/
theorem euclidean_inner_smul_right {n : ℕ} (c : ℝ) (x y : Fin n → ℝ) :
    ∑ i : Fin n, x i * (c * y i) = c * ∑ i : Fin n, x i * y i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean dot product negation, left**:
`∑ (-xᵢ) · yᵢ = - ∑ xᵢ · yᵢ`. -/
theorem euclidean_inner_neg_left {n : ℕ} (x y : Fin n → ℝ) :
    ∑ i : Fin n, (-x i) * y i = -(∑ i : Fin n, x i * y i) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean dot product negation, right**:
`∑ xᵢ · (-yᵢ) = - ∑ xᵢ · yᵢ`. -/
theorem euclidean_inner_neg_right {n : ℕ} (x y : Fin n → ℝ) :
    ∑ i : Fin n, x i * (-y i) = -(∑ i : Fin n, x i * y i) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean dot product distributes over left subtraction**:
`∑ (xᵢ - yᵢ) · zᵢ = ∑ xᵢ · zᵢ - ∑ yᵢ · zᵢ`. -/
theorem euclidean_inner_sub_left {n : ℕ} (x y z : Fin n → ℝ) :
    ∑ i : Fin n, (x i - y i) * z i
      = (∑ i : Fin n, x i * z i) - (∑ i : Fin n, y i * z i) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean dot product distributes over right subtraction**:
`∑ xᵢ · (yᵢ - zᵢ) = ∑ xᵢ · yᵢ - ∑ xᵢ · zᵢ`. -/
theorem euclidean_inner_sub_right {n : ℕ} (x y z : Fin n → ℝ) :
    ∑ i : Fin n, x i * (y i - z i)
      = (∑ i : Fin n, x i * y i) - (∑ i : Fin n, x i * z i) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intros i _
  ring

end IsingModel
