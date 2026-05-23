import IsingModel.Conditioning.Reflection.DiscriminantSchwarz

/-!
# Reflection positivity — Schwarz-type corollaries for RP bilinear forms

This module is part of the split `IsingModel.Conditioning.Reflection`
development. It collects the non-symmetric reflection-positive Schwarz
estimate, its AM-GM and sum-abs corollaries, the classical (symmetric)
Schwarz inequality under symmetry, and the diagonal-zero off-diagonal
vanishing corollaries.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §10.6, pp.~204--206.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Non-symmetric reflection-positive Schwarz** (§10.6 main):
for a bilinear `b : α → α → ℝ` on an ℝ-module `α` satisfying
`ReflectionPositive b` (i.e., `b x x ≥ 0` for all x), the
symmetrized off-diagonal entries satisfy the Schwarz-style bound

  `((b x y + b y x) / 2)² ≤ b x x · b y y`.

Proof: for all `t : ℝ`, bilinearity expands `b (x + t•y) (x + t•y)`
to `b x x + t·(b x y + b y x) + t²·b y y`; reflection positivity
gives this quadratic ≥ 0 for all t; `nonsymmetric_discriminant_mean`
yields the Schwarz bound. -/
theorem schwarz_of_reflection_positive
    {α : Type*} [AddCommGroup α] [Module ℝ α]
    (b : α → α → ℝ)
    (hbi_left : ∀ x y z : α, b (x + y) z = b x z + b y z)
    (hbi_right : ∀ x y z : α, b x (y + z) = b x y + b x z)
    (hbi_smul_left : ∀ (c : ℝ) (x y : α), b (c • x) y = c * b x y)
    (hbi_smul_right : ∀ (c : ℝ) (x y : α), b x (c • y) = c * b x y)
    (hRP : ReflectionPositive b) (x y : α) :
    ((b x y + b y x) / 2) ^ 2 ≤ b x x * b y y := by
  have hquad : ∀ t : ℝ,
      0 ≤ b y y * t ^ 2 + (b x y + b y x) * t + b x x := by
    intro t
    have hrp := hRP (x + t • y)
    have hexpand : b (x + t • y) (x + t • y)
        = b y y * t ^ 2 + (b x y + b y x) * t + b x x := by
      rw [hbi_left]
      rw [hbi_right, hbi_right]
      rw [hbi_smul_right, hbi_smul_left, hbi_smul_right, hbi_smul_left]
      ring
    linarith [hrp, hexpand]
  have := nonsymmetric_discriminant_mean (b y y) (b x y) (b y x) (b x x) hquad
  linarith [this, mul_comm (b y y) (b x x)]

/-- **Reflection-positive Schwarz, AM-GM form** (§10.6 corollary):
`|b x y + b y x| / 2 ≤ √(b x x · b y y)` from
`schwarz_of_reflection_positive` (PR #685) + sqrt monotonicity. -/
theorem reflection_positive_mean_le_geom_mean
    {α : Type*} [AddCommGroup α] [Module ℝ α]
    (b : α → α → ℝ)
    (hbi_left : ∀ x y z : α, b (x + y) z = b x z + b y z)
    (hbi_right : ∀ x y z : α, b x (y + z) = b x y + b x z)
    (hbi_smul_left : ∀ (c : ℝ) (x y : α), b (c • x) y = c * b x y)
    (hbi_smul_right : ∀ (c : ℝ) (x y : α), b x (c • y) = c * b x y)
    (hRP : ReflectionPositive b) (x y : α) :
    |(b x y + b y x) / 2| ≤ Real.sqrt (b x x * b y y) := by
  have hsq := schwarz_of_reflection_positive b hbi_left hbi_right
    hbi_smul_left hbi_smul_right hRP x y
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq_eq_abs] at this

/-- **Reflection-positive Schwarz, sum abs bound**:
`|b x y + b y x| ≤ 2·√(b x x · b y y)` from `_mean_le_geom_mean`
by multiplying both sides by 2. -/
theorem reflection_positive_sum_abs_bound
    {α : Type*} [AddCommGroup α] [Module ℝ α]
    (b : α → α → ℝ)
    (hbi_left : ∀ x y z : α, b (x + y) z = b x z + b y z)
    (hbi_right : ∀ x y z : α, b x (y + z) = b x y + b x z)
    (hbi_smul_left : ∀ (c : ℝ) (x y : α), b (c • x) y = c * b x y)
    (hbi_smul_right : ∀ (c : ℝ) (x y : α), b x (c • y) = c * b x y)
    (hRP : ReflectionPositive b) (x y : α) :
    |b x y + b y x| ≤ 2 * Real.sqrt (b x x * b y y) := by
  have hmean := reflection_positive_mean_le_geom_mean b hbi_left hbi_right
    hbi_smul_left hbi_smul_right hRP x y
  have habs_half : |(b x y + b y x) / 2| = |b x y + b y x| / 2 := by
    rw [abs_div]
    simp
  rw [habs_half] at hmean
  linarith

/-- **Classical symmetric Cauchy-Schwarz** (§10.6 corollary for
symmetric `b`): for symmetric bilinear `b` (i.e., `b x y = b y x`)
satisfying `ReflectionPositive b`, the classical Schwarz inequality
`(b x y)² ≤ b x x · b y y` holds. Direct reduction of
`schwarz_of_reflection_positive` using `(b x y + b y x)/2 = b x y`
under symmetry. -/
theorem classical_schwarz_of_symmetric_reflection_positive
    {α : Type*} [AddCommGroup α] [Module ℝ α]
    (b : α → α → ℝ)
    (hbi_left : ∀ x y z : α, b (x + y) z = b x z + b y z)
    (hbi_right : ∀ x y z : α, b x (y + z) = b x y + b x z)
    (hbi_smul_left : ∀ (c : ℝ) (x y : α), b (c • x) y = c * b x y)
    (hbi_smul_right : ∀ (c : ℝ) (x y : α), b x (c • y) = c * b x y)
    (hRP : ReflectionPositive b)
    (hsym : ∀ x y : α, b x y = b y x) (x y : α) :
    (b x y) ^ 2 ≤ b x x * b y y := by
  have hsq := schwarz_of_reflection_positive b hbi_left hbi_right
    hbi_smul_left hbi_smul_right hRP x y
  -- `(b x y + b y x)/2 = (b x y + b x y)/2 = b x y` under symmetry.
  have hmean : (b x y + b y x) / 2 = b x y := by
    rw [hsym y x]; ring
  rw [hmean] at hsq
  exact hsq

/-- **Classical symmetric Schwarz absolute-value form** (§10.6
corollary): `|b x y| ≤ √(b x x · b y y)` under symmetric bilinear +
reflection positive. Immediate from
`classical_schwarz_of_symmetric_reflection_positive` + sqrt
monotonicity. -/
theorem classical_schwarz_abs_of_symmetric_reflection_positive
    {α : Type*} [AddCommGroup α] [Module ℝ α]
    (b : α → α → ℝ)
    (hbi_left : ∀ x y z : α, b (x + y) z = b x z + b y z)
    (hbi_right : ∀ x y z : α, b x (y + z) = b x y + b x z)
    (hbi_smul_left : ∀ (c : ℝ) (x y : α), b (c • x) y = c * b x y)
    (hbi_smul_right : ∀ (c : ℝ) (x y : α), b x (c • y) = c * b x y)
    (hRP : ReflectionPositive b)
    (hsym : ∀ x y : α, b x y = b y x) (x y : α) :
    |b x y| ≤ Real.sqrt (b x x * b y y) := by
  have hsq := classical_schwarz_of_symmetric_reflection_positive b
    hbi_left hbi_right hbi_smul_left hbi_smul_right hRP hsym x y
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq_eq_abs] at this

/-- **Symmetric degenerate case** (§10.6 corollary): if `b` is symmetric
bilinear with reflection positivity and `b x x = 0`, then `b x y = 0`
for all `y`. Proof: `(b x y)² ≤ b x x · b y y = 0`, so `b x y = 0`. -/
theorem symmetric_reflection_positive_off_diag_zero_of_diag_zero
    {α : Type*} [AddCommGroup α] [Module ℝ α]
    (b : α → α → ℝ)
    (hbi_left : ∀ x y z : α, b (x + y) z = b x z + b y z)
    (hbi_right : ∀ x y z : α, b x (y + z) = b x y + b x z)
    (hbi_smul_left : ∀ (c : ℝ) (x y : α), b (c • x) y = c * b x y)
    (hbi_smul_right : ∀ (c : ℝ) (x y : α), b x (c • y) = c * b x y)
    (hRP : ReflectionPositive b)
    (hsym : ∀ x y : α, b x y = b y x) (x y : α) (hxx : b x x = 0) :
    b x y = 0 := by
  have hsq := classical_schwarz_of_symmetric_reflection_positive b
    hbi_left hbi_right hbi_smul_left hbi_smul_right hRP hsym x y
  rw [hxx, zero_mul] at hsq
  have hnn : 0 ≤ (b x y) ^ 2 := sq_nonneg _
  have hzero : (b x y) ^ 2 = 0 := le_antisymm hsq hnn
  exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp hzero

/-- **Degenerate case variant** (§10.6 corollary): if `b y y = 0`,
then `b x y + b y x = 0`. Symmetric partner of
`reflection_positive_off_diag_zero_of_diag_zero`. -/
theorem reflection_positive_off_diag_zero_of_diag_zero_right
    {α : Type*} [AddCommGroup α] [Module ℝ α]
    (b : α → α → ℝ)
    (hbi_left : ∀ x y z : α, b (x + y) z = b x z + b y z)
    (hbi_right : ∀ x y z : α, b x (y + z) = b x y + b x z)
    (hbi_smul_left : ∀ (c : ℝ) (x y : α), b (c • x) y = c * b x y)
    (hbi_smul_right : ∀ (c : ℝ) (x y : α), b x (c • y) = c * b x y)
    (hRP : ReflectionPositive b) (x y : α) (hyy : b y y = 0) :
    b x y + b y x = 0 := by
  have hsq := schwarz_of_reflection_positive b hbi_left hbi_right
    hbi_smul_left hbi_smul_right hRP x y
  rw [hyy, mul_zero] at hsq
  have hnn : 0 ≤ ((b x y + b y x) / 2) ^ 2 := sq_nonneg _
  have hzero : ((b x y + b y x) / 2) ^ 2 = 0 := le_antisymm hsq hnn
  have hhalf_zero : (b x y + b y x) / 2 = 0 :=
    pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp hzero
  linarith

/-- **Degenerate reflection-positive case** (§10.6 corollary): if
`b x x = 0`, then `b x y + b y x = 0` (the symmetrized off-diagonal
vanishes). Immediate from Schwarz: `((b x y + b y x)/2)² ≤ 0` forces
`b x y + b y x = 0`. -/
theorem reflection_positive_off_diag_zero_of_diag_zero
    {α : Type*} [AddCommGroup α] [Module ℝ α]
    (b : α → α → ℝ)
    (hbi_left : ∀ x y z : α, b (x + y) z = b x z + b y z)
    (hbi_right : ∀ x y z : α, b x (y + z) = b x y + b x z)
    (hbi_smul_left : ∀ (c : ℝ) (x y : α), b (c • x) y = c * b x y)
    (hbi_smul_right : ∀ (c : ℝ) (x y : α), b x (c • y) = c * b x y)
    (hRP : ReflectionPositive b) (x y : α) (hxx : b x x = 0) :
    b x y + b y x = 0 := by
  have hsq := schwarz_of_reflection_positive b hbi_left hbi_right
    hbi_smul_left hbi_smul_right hRP x y
  rw [hxx, zero_mul] at hsq
  have hnn : 0 ≤ ((b x y + b y x) / 2) ^ 2 := sq_nonneg _
  have hzero : ((b x y + b y x) / 2) ^ 2 = 0 := le_antisymm hsq hnn
  have hhalf_zero : (b x y + b y x) / 2 = 0 := pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp hzero
  linarith

end IsingModel
