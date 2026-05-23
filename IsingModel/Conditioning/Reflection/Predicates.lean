import IsingModel.Conditioning.Bounds

/-!
# Reflection positivity — basic predicate (§10.4)

This module is part of the split `IsingModel.Conditioning.Reflection`
development. It defines `ReflectionPositive` and its diagonal closure
properties: trivial/constant instances, diagonal transfer, definitional
unfolding, and monotone-diagonal closure.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §10.4, pp.~198--200.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A bilinear form is **reflection-positive** if `b(x, x) ≥ 0` for all `x`.
This is the semi-inner product property (Glimm–Jaffe, §10.4, p. 198). -/
def ReflectionPositive {α : Type*} (b : α → α → ℝ) : Prop :=
  ∀ x, 0 ≤ b x x

/-- **Trivial instance**: the identically-zero bilinear form is
reflection positive. -/
theorem ReflectionPositive.zero {α : Type*} :
    ReflectionPositive (fun (_ _ : α) => (0 : ℝ)) :=
  fun _ => le_refl 0

/-- **Constant instance**: a constant bilinear form with nonneg value
is reflection positive. Generalization of `.zero`. -/
theorem ReflectionPositive.const {α : Type*} {c : ℝ} (hc : 0 ≤ c) :
    ReflectionPositive (fun (_ _ : α) => c) :=
  fun _ => hc

/-- **Diagonal-transfer**: if two bilinear forms agree on the diagonal
(i.e., `b₁ x x = b₂ x x` for all x) and one is RP, the other is too. -/
theorem ReflectionPositive.of_diag_eq {α : Type*} {b₁ b₂ : α → α → ℝ}
    (hb : ∀ x, b₁ x x = b₂ x x) (h : ReflectionPositive b₁) :
    ReflectionPositive b₂ :=
  fun x => (hb x) ▸ h x

/-- **Definitional unfolding**: `ReflectionPositive b ↔ ∀ x, 0 ≤ b x x`. -/
theorem ReflectionPositive.iff_forall_diag_nonneg {α : Type*}
    (b : α → α → ℝ) : ReflectionPositive b ↔ ∀ x : α, 0 ≤ b x x := Iff.rfl

/-- **Monotone-diagonal closure**: if `b₁` is RP and `b₁(x, x) ≤ b₂(x, x)`
pointwise on the diagonal, then `b₂` is RP. -/
theorem ReflectionPositive.of_le_diag {α : Type*} {b₁ b₂ : α → α → ℝ}
    (h : ReflectionPositive b₁) (hle : ∀ x, b₁ x x ≤ b₂ x x) :
    ReflectionPositive b₂ :=
  fun x => (h x).trans (hle x)

end IsingModel
