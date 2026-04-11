import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Powerset

/-!
# Multilinear polynomials and Asano contraction

A multilinear polynomial over `ℂ` with variables indexed by `ι` is
a function `Finset ι → ℂ` giving the coefficient of each monomial `∏_{i ∈ X} z_i`.

The Asano contraction merges two variables by keeping only the "both present"
and "both absent" parts.

Reference: Friedli–Velenik, §3.7, pp. 122–127.
-/

namespace IsingModel

open Finset Complex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Multilinear polynomials -/

/-- A multilinear polynomial over `ℂ` with variables indexed by `ι`.
The coefficient `p X` corresponds to the monomial `∏_{i ∈ X} z_i`. -/
abbrev MultilinPoly (ι : Type*) [Fintype ι] := Finset ι → ℂ

/-- Evaluate a multilinear polynomial at `z : ι → ℂ`. -/
noncomputable def MultilinPoly.eval (p : MultilinPoly ι) (z : ι → ℂ) : ℂ :=
  ∑ X : Finset ι, p X * ∏ i ∈ X, z i

/-- The constant polynomial `1`. -/
def MultilinPoly.one : MultilinPoly ι := fun X => if X = ∅ then 1 else 0

/-- Multiply two multilinear polynomials on disjoint variable sets.
Given `p : MultilinPoly ι₁` and `q : MultilinPoly ι₂`,
the product is a polynomial on `ι₁ ⊕ ι₂`. -/
noncomputable def MultilinPoly.disjointMul {ι₁ ι₂ : Type*}
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (p : MultilinPoly ι₁) (q : MultilinPoly ι₂) : MultilinPoly (ι₁ ⊕ ι₂) :=
  fun X => p (X.preimage Sum.inl (by intro a b _ _ h; exact Sum.inl_injective h)) *
           q (X.preimage Sum.inr (by intro a b _ _ h; exact Sum.inr_injective h))

/-! ## Asano contraction -/

/-- Asano contraction: given a polynomial `p` on `ι` and two distinct variables
`i, j : ι`, contract `j` into `i`. The result is a polynomial on `ι` that
does not depend on `j`.

Mathematically: write `P = P_{--} z_i z_j + P_{+-} z_j + P_{-+} z_i + P_{++}`.
The contraction is `P_{--} z_i + P_{++}`.

In terms of coefficients:
- For `X` with `i ∈ X`: `(contract p i j)(X) = p(X ∪ {j})` (the `P_{--}` part)
- For `X` with `i ∉ X`: `(contract p i j)(X) = p(X)` (the `P_{++}` part)
- For `X` with `j ∈ X`: `(contract p i j)(X) = 0` (contracted variable is eliminated)

Reference: Friedli–Velenik, pp. 123–124. -/
def MultilinPoly.asanoContract (p : MultilinPoly ι) (i j : ι) (_hij : i ≠ j) :
    MultilinPoly ι :=
  fun X =>
    if j ∈ X then 0
    else if i ∈ X then p (insert j X)
    else p X

/-! ## Asano contraction preserves non-vanishing -/

/-- Key property: Asano contraction preserves non-vanishing on the open unit polydisk.

Write `P = P_{--} z_i z_j + P_{+-} z_j + P_{-+} z_i + P_{++}`.
The contraction is `Q(z) = P_{--}(z) z_i + P_{++}(z)`.
If `Q(z₀) = 0` for some `z₀` with `|z₀_k| < 1 ∀k`, then
`z₀_i = -P_{++}/P_{--}`. But `P(z₀_with_j=w) = P_{--} z₀_i w + P_{+-} w + P_{-+} z₀_i + P_{++}`
is linear in `w`, and vanishes at `w = -(P_{-+} z₀_i + P_{++})/(P_{--} z₀_i + P_{+-})`.
The hypothesis says this `w` must have `|w| ≥ 1`. But by algebraic manipulation,
`|w| < 1` leads to a contradiction. -/
theorem MultilinPoly.asanoContract_nonvanishing (p : MultilinPoly ι) (i j : ι) (hij : i ≠ j)
    (hp : ∀ z : ι → ℂ, (∀ k, ‖z k‖ < 1) → p.eval z ≠ 0) :
    ∀ z : ι → ℂ, (∀ k, ‖z k‖ < 1) → (p.asanoContract i j hij).eval z ≠ 0 := by
  sorry

/-! ## Base case: single edge -/

/-- The partition polynomial for a single edge `{i, j}` with coupling `t = e^{-2β}`:
`P(z_i, z_j) = z_i z_j + t(z_i + z_j) + 1`
where `0 ≤ t < 1`. -/
def singleEdgePoly (i j : ι) (t : ℝ) : MultilinPoly ι :=
  fun X =>
    if X = {i, j} then 1
    else if X = {i} then ↑t
    else if X = {j} then ↑t
    else if X = ∅ then 1
    else 0

/-- The Möbius transformation `z ↦ -(tz + 1)/(z + t)` maps the open unit disk
to the complement of the closed unit disk when `0 ≤ t < 1`. -/
theorem moebius_maps_disk_to_complement (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (z : ℂ) (hz : ‖z‖ < 1) :
    1 < ‖-(↑t * z + 1) / (z + ↑t)‖ := by
  -- ‖-(tz+1)/(z+t)‖ = ‖tz+1‖/‖z+t‖
  -- Need: ‖tz+1‖ > ‖z+t‖
  -- ‖tz+1‖² - ‖z+t‖² = (t²|z|²+2t Re z+1) - (|z|²+2t Re z+t²)
  --                    = (t²-1)|z|² + (1-t²) = (1-t²)(1-|z|²) > 0
  -- Strategy: ‖-(tz+1)/(z+t)‖ = ‖tz+1‖/‖z+t‖ > 1
  -- ⟺ ‖tz+1‖² > ‖z+t‖²
  -- ‖tz+1‖² - ‖z+t‖² = (1-t²)(1-‖z‖²) > 0 since t < 1 and ‖z‖ < 1
  sorry

/-- The single-edge polynomial does not vanish on the open unit polydisk.
If `P(z_i, z_j) = 0`, then `z_i = -(tz_j+1)/(z_j+t)`, but the Möbius
transformation maps `|z_j| < 1` to `|z_i| > 1`, contradiction. -/
theorem singleEdgePoly_nonvanishing (i j : ι) (hij : i ≠ j)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (z : ι → ℂ) (hz : ∀ k, ‖z k‖ < 1) :
    (singleEdgePoly i j t).eval z ≠ 0 := by
  -- P(z) = z_i z_j + t(z_i + z_j) + 1 (plus zero terms for other subsets)
  -- If P = 0 then z_i(z_j + t) = -(tz_j + 1), so z_i = -(tz_j+1)/(z_j+t)
  -- But Möbius gives |z_i| > 1 while |z_i| < 1, contradiction
  sorry

/-! ## Lee-Yang circle theorem -/

/-- The Ising partition polynomial `P_E(z_V) = Σ_{X⊆V} a_E(X) ∏_{i∈X} z_i`
with coefficients in `[0,1]` and `a(∅) = a(V) = 1`.
This is the multilinear form of the partition function with `z = e^{-2h}`. -/
structure IsingPartitionPoly (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The underlying multilinear polynomial. -/
  poly : MultilinPoly ι
  /-- All coefficients are in `[0, 1]`. -/
  coeff_nonneg : ∀ X, 0 ≤ (poly X).re ∧ (poly X).re ≤ 1 ∧ (poly X).im = 0
  /-- Coefficient of the empty set is `1`. -/
  coeff_empty : poly ∅ = 1
  /-- Coefficient of the full set is `1`. -/
  coeff_full : poly Finset.univ = 1

/-- **Lee-Yang circle theorem**: The Ising partition polynomial does not vanish
on the open unit polydisk `{z : ‖z_i‖ < 1 ∀i}`.

Equivalently, all zeros of `Z(z)` (as a function of `z = e^{-2h}`) lie on `|z| = 1`.

Reference: Friedli–Velenik, Theorem 3.43, pp. 122–127.
Proof by induction on the edge set using Asano contraction. -/
theorem lee_yang_circle (p : IsingPartitionPoly ι)
    (z : ι → ℂ) (hz : ∀ k, ‖z k‖ < 1) :
    p.poly.eval z ≠ 0 := by
  sorry

end IsingModel
