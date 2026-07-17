import IsingModel.Conditioning.Reflection.Predicates

/-!
# Reflection positivity — parallelogram identity and closure properties

This module is part of the split `IsingModel.Conditioning.Reflection`
development. It records the parallelogram identity for the Euclidean norm
squared and the operator-theoretic closure properties of
`ReflectionPositive` (`.of_diag_nonneg`, `.add`, `.smul_nonneg`, `.comp`,
`.sum`, `.weighted_sum`).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §10.4, pp.~198--200.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Parallelogram identity for Euclidean norm squared**:
`∑ (xᵢ + yᵢ)² + ∑ (xᵢ - yᵢ)² = 2·(∑ xᵢ² + ∑ yᵢ²)`. -/
theorem euclidean_parallelogram {n : ℕ} (x y : Fin n → ℝ) :
    (∑ i : Fin n, (x i + y i) ^ 2) + (∑ i : Fin n, (x i - y i) ^ 2)
      = 2 * ((∑ i : Fin n, (x i) ^ 2) + (∑ i : Fin n, (y i) ^ 2)) := by
  have h_left : (∑ i : Fin n, (x i + y i) ^ 2)
      + (∑ i : Fin n, (x i - y i) ^ 2)
      = ∑ i : Fin n, ((x i + y i) ^ 2 + (x i - y i) ^ 2) := by
    rw [← Finset.sum_add_distrib]
  have h_pointwise : ∀ i : Fin n,
      (x i + y i) ^ 2 + (x i - y i) ^ 2 = 2 * ((x i) ^ 2 + (y i) ^ 2) := by
    intros i; ring
  rw [h_left]
  calc ∑ i : Fin n, ((x i + y i) ^ 2 + (x i - y i) ^ 2)
      = ∑ i : Fin n, 2 * ((x i) ^ 2 + (y i) ^ 2) :=
        Finset.sum_congr rfl (fun i _ => h_pointwise i)
    _ = 2 * ∑ i : Fin n, ((x i) ^ 2 + (y i) ^ 2) := (Finset.mul_sum _ _ _).symm
    _ = 2 * ((∑ i : Fin n, (x i) ^ 2) + (∑ i : Fin n, (y i) ^ 2)) := by
        rw [Finset.sum_add_distrib]

/-- **Constant-diagonal instance**: if `f : α → ℝ` is nonneg, then
the form `fun x _ => f x` (constant in the second argument) is
reflection positive. -/
theorem ReflectionPositive.of_diag_nonneg {α : Type*} (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    ReflectionPositive (fun (x _ : α) => f x) :=
  fun x => hf x

/-- **Sum of reflection-positive forms is reflection positive**. -/
theorem ReflectionPositive.add {α : Type*} {b₁ b₂ : α → α → ℝ}
    (h₁ : ReflectionPositive b₁) (h₂ : ReflectionPositive b₂) :
    ReflectionPositive (fun x y => b₁ x y + b₂ x y) :=
  fun x => add_nonneg (h₁ x) (h₂ x)

/-- **Non-negative scalar multiple of a reflection-positive form is
reflection positive**. -/
theorem ReflectionPositive.smul_nonneg {α : Type*} {b : α → α → ℝ}
    {c : ℝ} (hc : 0 ≤ c) (h : ReflectionPositive b) :
    ReflectionPositive (fun x y => c * b x y) :=
  fun x => mul_nonneg hc (h x)

/-- **Reparametrization preserves reflection positivity**: for any
map `g : β → α` and RP form `b : α → α → ℝ`, the pullback
`fun x y => b (g x) (g y)` is RP on `β`. -/
theorem ReflectionPositive.comp {α β : Type*} {b : α → α → ℝ}
    (h : ReflectionPositive b) (g : β → α) :
    ReflectionPositive (fun x y : β => b (g x) (g y)) :=
  fun x => h (g x)

/-- **Finite-sum closure**: a sum of finitely many reflection-positive
forms indexed by a `Finset` is reflection positive. -/
theorem ReflectionPositive.sum {α ι : Type*} {b : ι → α → α → ℝ}
    (s : Finset ι) (h : ∀ i ∈ s, ReflectionPositive (b i)) :
    ReflectionPositive (fun x y => ∑ i ∈ s, b i x y) := by
  intro x
  exact Finset.sum_nonneg (fun i hi => h i hi x)

/-- **Weighted-sum closure**: a nonneg-weighted sum of
reflection-positive forms is reflection positive. Combines
`.smul_nonneg` and `.sum`. -/
theorem ReflectionPositive.weighted_sum {α ι : Type*}
    {b : ι → α → α → ℝ} {c : ι → ℝ} (s : Finset ι)
    (hc : ∀ i ∈ s, 0 ≤ c i)
    (h : ∀ i ∈ s, ReflectionPositive (b i)) :
    ReflectionPositive (fun x y => ∑ i ∈ s, c i * b i x y) := by
  intro x
  exact Finset.sum_nonneg (fun i hi => mul_nonneg (hc i hi) (h i hi x))

end IsingModel
