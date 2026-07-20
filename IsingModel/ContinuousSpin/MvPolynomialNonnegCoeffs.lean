import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Real.Basic

/-!
# Non-negative-coefficient polynomials over an arbitrary index type

This module isolates the *non-negative-coefficient* predicate on a multivariate
polynomial `MvPolynomial σ ℝ` over an arbitrary index type `σ`, together with the
closure lemmas that make `NonnegCoeffs` a positive cone: it contains `0`, `1`,
every variable `X v` and every non-negative constant `C c`, and it is closed
under addition, multiplication, finite sums, finite products and powers.

The predicate and its algebra are entirely index-type agnostic (each proof
supplies its own `DecidableEq σ` via `classical`), so this single generic file
replaces the two byte-identical copies that previously lived in
`TwoComponentGriffithsI.lean` (index type `ι ⊕ ι`) and
`TwoComponentGriffithsV.lean` (index type `ι × Fin 4`).  Downstream files use it
by instantiating `σ` at the concrete index type they need.

This file depends only on Mathlib (no `IsingModel` imports) so that it can sit at
the base of the `ContinuousSpin` import graph.
-/

namespace IsingModel.ContinuousSpin

open MvPolynomial
open scoped BigOperators

variable {σ : Type*}

/-- A polynomial has non-negative coefficients. -/
def NonnegCoeffs (p : MvPolynomial σ ℝ) : Prop := ∀ m, 0 ≤ MvPolynomial.coeff m p

/-- The zero polynomial has non-negative coefficients. -/
theorem NonnegCoeffs.zero : NonnegCoeffs (0 : MvPolynomial σ ℝ) := fun m => by
  simp

/-- The unit polynomial has non-negative coefficients. -/
theorem NonnegCoeffs.one : NonnegCoeffs (1 : MvPolynomial σ ℝ) := fun m => by
  classical rw [coeff_one]; split <;> norm_num

/-- Each variable has non-negative coefficients. -/
theorem NonnegCoeffs.X (v : σ) : NonnegCoeffs (MvPolynomial.X v : MvPolynomial σ ℝ) :=
  fun m => by classical rw [coeff_X']; split <;> norm_num

/-- A non-negative constant has non-negative coefficients. -/
theorem NonnegCoeffs.C {c : ℝ} (hc : 0 ≤ c) :
    NonnegCoeffs (MvPolynomial.C c : MvPolynomial σ ℝ) := fun m => by
  classical rw [coeff_C]; split <;> [exact hc; exact le_refl 0]

/-- Non-negative coefficients are closed under addition. -/
theorem NonnegCoeffs.add {p q : MvPolynomial σ ℝ}
    (hp : NonnegCoeffs p) (hq : NonnegCoeffs q) : NonnegCoeffs (p + q) := fun m => by
  rw [coeff_add]; exact add_nonneg (hp m) (hq m)

/-- Non-negative coefficients are closed under multiplication (`coeff_mul` is a
sum of products of coefficients). -/
theorem NonnegCoeffs.mul {p q : MvPolynomial σ ℝ}
    (hp : NonnegCoeffs p) (hq : NonnegCoeffs q) : NonnegCoeffs (p * q) := fun m => by
  classical
  rw [coeff_mul]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hp _) (hq _)

/-- Non-negative coefficients are closed under finite sums. -/
theorem NonnegCoeffs.sum {α : Type*} {s : Finset α} {f : α → MvPolynomial σ ℝ}
    (h : ∀ a ∈ s, NonnegCoeffs (f a)) : NonnegCoeffs (∑ a ∈ s, f a) :=
  Finset.sum_induction f NonnegCoeffs (fun _ _ => NonnegCoeffs.add) NonnegCoeffs.zero h

/-- Non-negative coefficients are closed under finite products. -/
theorem NonnegCoeffs.prod {α : Type*} {s : Finset α} {f : α → MvPolynomial σ ℝ}
    (h : ∀ a ∈ s, NonnegCoeffs (f a)) : NonnegCoeffs (∏ a ∈ s, f a) :=
  Finset.prod_induction f NonnegCoeffs (fun _ _ => NonnegCoeffs.mul) NonnegCoeffs.one h

/-- Non-negative coefficients are closed under powers. -/
theorem NonnegCoeffs.pow {p : MvPolynomial σ ℝ} (hp : NonnegCoeffs p) :
    ∀ k : ℕ, NonnegCoeffs (p ^ k)
  | 0 => by simpa using NonnegCoeffs.one
  | k + 1 => by rw [pow_succ]; exact (NonnegCoeffs.pow hp k).mul hp

end IsingModel.ContinuousSpin
