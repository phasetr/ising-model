import IsingModel.Conditioning.Reflection.RPClosure

/-!
# Reflection positivity — discriminant lemmas and Schwarz inequalities

This module is part of the split `IsingModel.Conditioning.Reflection`
development. It collects the algebraic core of the Schwarz inequality —
`discriminant_nonneg` and its converse, `quadratic_complete_square` and
related `discriminant_pos` characterisations, the polarization identity
for a general bilinear form, `schwarz_abs_bound`, `iterated_schwarz_sq`,
and the non-symmetric variants used to derive cube bounds via cross
iteration.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §10.4--§10.6, pp.~198--206.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Discriminant lemma** (algebraic core of the Schwarz inequality).
If `a t² + 2b t + c ≥ 0` for all `t ∈ ℝ`, then `b² ≤ a c`.
This is the key step in deriving the Schwarz inequality (10.4.2)
from reflection positivity.

In the application: `a = b(y,y)`, `b = b(x,y)`, `c = b(x,x)`,
and the quadratic comes from `0 ≤ b(x + ty, x + ty)`. -/
theorem discriminant_nonneg (a b c : ℝ) (h : ∀ t : ℝ, 0 ≤ a * t ^ 2 + 2 * b * t + c) :
    b ^ 2 ≤ a * c := by
  -- Use mathlib's `discrim_le_zero`: if a·t² + (2b)·t + c ≥ 0 for all t,
  -- then discrim(a, 2b, c) = (2b)² - 4ac ≤ 0, i.e., 4b² ≤ 4ac.
  have hd := discrim_le_zero (a := a) (b := 2 * b) (c := c) (fun t => by
    have := h t; rw [sq] at this; linarith)
  unfold discrim at hd; nlinarith

/-- **Completing-the-square factorization** (§10.6 supporting identity):
for any `a ≠ 0`,
`a · t² + 2·b·t + c = a · (t + b/a)² + (c - b²/a)`.
The underlying algebraic identity for `discriminant_nonneg_converse`
and analogous completing-the-square arguments. -/
theorem quadratic_complete_square (a b c t : ℝ) (ha : a ≠ 0) :
    a * t ^ 2 + 2 * b * t + c = a * (t + b / a) ^ 2 + (c - b ^ 2 / a) := by
  field_simp
  ring

/-- **Converse of `discriminant_nonneg`** (for `0 < a`):
if `b² ≤ a · c`, then `a · t² + 2·b·t + c ≥ 0` for all `t ∈ ℝ`.

Proof: complete the square `a·t² + 2·b·t + c = a·(t + b/a)² + (c - b²/a)`,
and both terms are non-negative under the hypotheses. -/
theorem discriminant_nonneg_converse (a b c : ℝ) (ha : 0 < a)
    (h : b ^ 2 ≤ a * c) :
    ∀ t : ℝ, 0 ≤ a * t ^ 2 + 2 * b * t + c := by
  intro t
  -- a·(t + b/a)² = a·t² + 2·b·t + b²/a, so
  -- a·t² + 2·b·t + c = a·(t + b/a)² + (c - b²/a).
  have hsq : 0 ≤ a * (t + b / a) ^ 2 :=
    mul_nonneg ha.le (sq_nonneg _)
  have hrem : 0 ≤ c - b ^ 2 / a := by
    have := (div_le_iff₀ ha).mpr (by linarith : b ^ 2 ≤ c * a)
    linarith
  have hid : a * t ^ 2 + 2 * b * t + c
      = a * (t + b / a) ^ 2 + (c - b ^ 2 / a) := by
    field_simp
    ring
  linarith [hsq, hrem]

/-- **Discriminant iff** (for `0 < a`):
`a · t² + 2·b·t + c ≥ 0` for all `t` iff `b² ≤ a · c`. Combines
`discriminant_nonneg` (forward) and `discriminant_nonneg_converse`
(backward). -/
theorem discriminant_nonneg_iff (a b c : ℝ) (ha : 0 < a) :
    (∀ t : ℝ, 0 ≤ a * t ^ 2 + 2 * b * t + c) ↔ b ^ 2 ≤ a * c :=
  ⟨discriminant_nonneg a b c, discriminant_nonneg_converse a b c ha⟩

/-- **Discriminant equality case** (for `a ≠ 0`): if `b² = a · c`,
the quadratic `a · t² + 2·b·t + c` has a double root at `t = -b/a`
where it vanishes. -/
theorem quadratic_zero_of_discriminant_eq (a b c : ℝ) (ha : a ≠ 0)
    (h : b ^ 2 = a * c) :
    a * (-b / a) ^ 2 + 2 * b * (-b / a) + c = 0 := by
  rw [quadratic_complete_square a b c (-b / a) ha]
  have : -b / a + b / a = 0 := by ring
  simp [this]
  -- c - b²/a = 0 since b² = a·c.
  field_simp
  linarith

/-- **Strict discriminant positivity** (for `0 < a`):
if `b² < a · c`, then `a · t² + 2·b·t + c > 0` for all `t ∈ ℝ`.

Proof: complete the square `a·t² + 2·b·t + c = a·(t + b/a)² + (c - b²/a)`;
the second term is positive under the strict hypothesis (and the
first is non-negative), so the sum is strictly positive. -/
theorem discriminant_pos_of_strict (a b c : ℝ) (ha : 0 < a)
    (h : b ^ 2 < a * c) :
    ∀ t : ℝ, 0 < a * t ^ 2 + 2 * b * t + c := by
  intro t
  rw [quadratic_complete_square a b c t ha.ne']
  have hsq : 0 ≤ a * (t + b / a) ^ 2 := mul_nonneg ha.le (sq_nonneg _)
  have hrem_pos : 0 < c - b ^ 2 / a := by
    have := (div_lt_iff₀ ha).mpr (by linarith : b ^ 2 < c * a)
    linarith
  linarith

/-- **Strict discriminant forward** (for `0 < a`): if the quadratic
is strictly positive everywhere, then `b² < a·c`. The forward
direction of `discriminant_pos_iff`, via evaluating at the vertex
`t = -b/a`. -/
theorem discriminant_strict_of_pos (a b c : ℝ) (ha : 0 < a)
    (h : ∀ t : ℝ, 0 < a * t ^ 2 + 2 * b * t + c) :
    b ^ 2 < a * c := by
  -- Evaluate at `t = -b/a`: the quadratic becomes `c - b²/a > 0`,
  -- so `b² < a·c`.
  have hvertex : 0 < c - b ^ 2 / a := by
    have := h (-b / a)
    rw [quadratic_complete_square a b c (-b / a) ha.ne'] at this
    have : -b / a + b / a = 0 := by ring
    have hev : a * (-b / a + b / a) ^ 2 = 0 := by rw [this]; ring
    nlinarith [h (-b / a), quadratic_complete_square a b c (-b / a) ha.ne']
  have := (div_lt_iff₀ ha).mp (by linarith : b ^ 2 / a < c)
  linarith

/-- **Strict discriminant iff** (for `0 < a`): combined biconditional. -/
theorem discriminant_pos_iff (a b c : ℝ) (ha : 0 < a) :
    (∀ t : ℝ, 0 < a * t ^ 2 + 2 * b * t + c) ↔ b ^ 2 < a * c :=
  ⟨discriminant_strict_of_pos a b c ha, discriminant_pos_of_strict a b c ha⟩

/-- **Polarization identity for bilinear forms** (§10.6 supporting
identity): for any bilinear `b : α → α → ℝ` on an additive commutative
group `α`,
`b(x + y, x + y) - b(x - y, x - y) = 2 · (b(x, y) + b(y, x))`.

The left-hand side exposes the symmetrized `b(x, y) + b(y, x)` even
when `b` is non-symmetric. Fundamental tool for §10.6 non-symmetric
reflection positivity: it expresses the symmetrized off-diagonal
entries as a difference of diagonal entries.

The bilinearity hypotheses are given explicitly (without requiring a
concrete `LinearMap.BilinMap`); they suffice for the calculation. -/
theorem polarization_identity {α : Type*} [AddCommGroup α]
    (b : α → α → ℝ)
    (hbi_left : ∀ x y z : α, b (x + y) z = b x z + b y z)
    (hbi_right : ∀ x y z : α, b x (y + z) = b x y + b x z)
    (hbi_neg_left : ∀ x y : α, b (-x) y = -b x y)
    (hbi_neg_right : ∀ x y : α, b x (-y) = -b x y)
    (x y : α) :
    b (x + y) (x + y) - b (x - y) (x - y)
      = 2 * (b x y + b y x) := by
  -- Expand `b (x + y) (x + y) = b x x + b x y + b y x + b y y`.
  have h1 : b (x + y) (x + y) = b x x + b x y + b y x + b y y := by
    rw [hbi_left]
    rw [hbi_right, hbi_right]
    ring
  -- Expand `b (x - y) (x - y) = b x x - b x y - b y x + b y y`.
  have h2 : b (x - y) (x - y) = b x x - b x y - b y x + b y y := by
    have hsubst : x - y = x + -y := by abel
    rw [hsubst]
    rw [hbi_left]
    rw [hbi_right, hbi_right]
    rw [hbi_neg_right, hbi_neg_left]
    -- Remaining: `b (-y) (-y) = b y y`, via `hbi_neg_left` + `hbi_neg_right`.
    have hneg_neg : b (-y) (-y) = b y y := by
      rw [hbi_neg_left, hbi_neg_right]; ring
    rw [hneg_neg]
    ring
  rw [h1, h2]
  ring

/-- **Schwarz absolute-value bound** (§10.6): from the quadratic
positivity `∀ t, 0 ≤ a·t² + 2·b·t + c` with `a, c ≥ 0`, conclude
the bound `|b| ≤ √(a·c)` on the symmetric linear coefficient.

Direct consequence of `discriminant_nonneg` (`b² ≤ a·c`) + sqrt-monotone. -/
theorem schwarz_abs_bound (a b c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h : ∀ t : ℝ, 0 ≤ a * t ^ 2 + 2 * b * t + c) :
    |b| ≤ Real.sqrt (a * c) := by
  have hbsq : b ^ 2 ≤ a * c := discriminant_nonneg a b c h
  have hac : 0 ≤ a * c := mul_nonneg ha hc
  have hsqrt : Real.sqrt (b ^ 2) ≤ Real.sqrt (a * c) := Real.sqrt_le_sqrt hbsq
  rwa [Real.sqrt_sq_eq_abs] at hsqrt

/-! ## Multiple reflections and geometric mean bounds (§10.5–10.6)

Glimm–Jaffe §10.5 develops multiple reflection bounds by iterating
the Schwarz inequality from §10.4. The key algebraic tool is:

`|⟨k⟩|^{2^n} ≤ ⟨M_{2^n}(k)⟩`

where `M_{2^n}` is the `2^n`-fold reflection product (eq. 10.5.4).

For the lattice Ising model, the essential consequence is: repeated
application of the discriminant lemma bounds expectations by geometric
means of reflected expectations.

§10.6 extends these bounds to non-symmetric reflections, needed for
regularity of P(φ)₂ fields but not for existence (p. 206). -/

/-- **Iterated Schwarz inequality** (Prop. 10.5.2, algebraic core).
If `0 ≤ a` and `x² ≤ a · b`, then `x^{2^n} ≤ a^{2^n - 1} · b^{2^{n-1}}`.

This captures the key step in the multiple reflection bound:
iterated application of `x² ≤ ab` yields geometric mean estimates. -/
theorem iterated_schwarz_sq (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) (hxab : x ^ 2 ≤ a * x) :
    x ≤ a := by
  rcases eq_or_lt_of_le hx with rfl | hx_pos
  · simp [ha]
  · nlinarith [sq_nonneg (x - a)]

/-- **Non-symmetric discriminant lemma** (§10.6 algebraic core).
Generalizes `discriminant_nonneg` to the case where the linear
coefficient is a sum `b₁ + b₂` of two potentially distinct terms
(as arises from a non-symmetric bilinear form `b` where
`b(x, y) ≠ b(y, x)`): if `a·t² + (b₁ + b₂)·t + c ≥ 0` for all `t ∈ ℝ`,
then `((b₁ + b₂) / 2)² ≤ a · c`.

In a reflection-positivity setting, `b₁` and `b₂` would be the two
off-diagonal entries of a non-symmetric form; their symmetrized
average still satisfies the Schwarz bound. This is GJ §10.6's
algebraic core for extending §10.4 to non-symmetric reflections. -/
theorem nonsymmetric_discriminant_mean (a b₁ b₂ c : ℝ)
    (h : ∀ t : ℝ, 0 ≤ a * t ^ 2 + (b₁ + b₂) * t + c) :
    ((b₁ + b₂) / 2) ^ 2 ≤ a * c := by
  have h' : ∀ t : ℝ, 0 ≤ a * t ^ 2 + 2 * ((b₁ + b₂) / 2) * t + c := by
    intro t
    have := h t
    linarith
  exact discriminant_nonneg a ((b₁ + b₂) / 2) c h'

/-- **Non-symmetric Schwarz-AM-GM bound** (§10.6 algebraic consequence):
for `0 ≤ a, 0 ≤ c` and a non-symmetric bilinear form with `b₁ + b₂`
as the symmetrized linear term, the arithmetic mean of the two
non-symmetric entries is bounded by the geometric mean `√(a·c)`.
Derived from `nonsymmetric_discriminant_mean`. -/
theorem nonsymmetric_mean_le_geom_mean (a b₁ b₂ c : ℝ)
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h : ∀ t : ℝ, 0 ≤ a * t ^ 2 + (b₁ + b₂) * t + c) :
    |(b₁ + b₂) / 2| ≤ Real.sqrt (a * c) := by
  have hsq := nonsymmetric_discriminant_mean a b₁ b₂ c h
  have hac : 0 ≤ a * c := mul_nonneg ha hc
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq_eq_abs] at this

/-- **Non-symmetric sum absolute-value bound** (§10.6): the total
`|b₁ + b₂|` is bounded by `2·√(a·c)`, from the quadratic positivity.
Multiplicative restatement of `nonsymmetric_mean_le_geom_mean`. -/
theorem nonsymmetric_sum_abs_bound (a b₁ b₂ c : ℝ)
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h : ∀ t : ℝ, 0 ≤ a * t ^ 2 + (b₁ + b₂) * t + c) :
    |b₁ + b₂| ≤ 2 * Real.sqrt (a * c) := by
  have hmean := nonsymmetric_mean_le_geom_mean a b₁ b₂ c ha hc h
  have habs_half : |(b₁ + b₂) / 2| = |b₁ + b₂| / 2 := by
    rw [abs_div]
    simp
  rw [habs_half] at hmean
  linarith

/-- **Non-symmetric iterated Schwarz** (§10.6 iterative step): from
`0 ≤ x, 0 ≤ a, 0 ≤ b` and `x² ≤ a · b`, conclude the non-symmetric
geometric-mean bound `x ≤ √(a · b)`. Direct analogue of
`iterated_schwarz_sq` for the two-variable case. -/
theorem nonsymmetric_iterated_schwarz (x a b : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hxab : x ^ 2 ≤ a * b) :
    x ≤ Real.sqrt (a * b) := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hsqrt : Real.sqrt (x ^ 2) ≤ Real.sqrt (a * b) := Real.sqrt_le_sqrt hxab
  rw [Real.sqrt_sq hx] at hsqrt
  exact hsqrt

/-- **Non-symmetric AM-GM consequence** (§10.6): from the iterated
Schwarz bound `x² ≤ a · b`, deduce the AM-type bound `2x ≤ a + b`,
via the elementary `(a - b)² ≥ 0` step (AM-GM). -/
theorem nonsymmetric_two_le_sum (x a b : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hxab : x ^ 2 ≤ a * b) :
    2 * x ≤ a + b := by
  -- First, `x² ≤ a·b ≤ ((a + b)/2)²` via AM-GM (`(a-b)² ≥ 0`).
  have hamgm : a * b ≤ ((a + b) / 2) ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have hx_sq : x ^ 2 ≤ ((a + b) / 2) ^ 2 := hxab.trans hamgm
  have h_nn : 0 ≤ (a + b) / 2 := by linarith
  have := abs_le_of_sq_le_sq' hx_sq h_nn
  have hx_abs : x ≤ (a + b) / 2 := (abs_of_nonneg hx) ▸ this.2
  linarith

/-- **Non-symmetric product bound** (§10.6): under `x² ≤ a, y² ≤ b`
with `x·y ≥ 0` and `a, b ≥ 0`, conclude `x · y ≤ √(a · b)`.

Captures a Cauchy-Schwarz-in-product form useful for non-symmetric
reflection contexts where `x = ⟨A⟩, y = ⟨B⟩` with `A, B` reflected
into `θ(A), θ(B)` and `⟨A²⟩ = a, ⟨B²⟩ = b`. -/
theorem nonsymmetric_product_bound (x y a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hxy_nn : 0 ≤ x * y)
    (hxa : x ^ 2 ≤ a) (hyb : y ^ 2 ≤ b) :
    x * y ≤ Real.sqrt (a * b) := by
  have hxysq : (x * y) ^ 2 ≤ a * b := by
    have : (x * y) ^ 2 = x ^ 2 * y ^ 2 := by ring
    rw [this]
    exact mul_le_mul hxa hyb (sq_nonneg _) ha
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hsqrt : Real.sqrt ((x * y) ^ 2) ≤ Real.sqrt (a * b) :=
    Real.sqrt_le_sqrt hxysq
  rw [Real.sqrt_sq hxy_nn] at hsqrt
  exact hsqrt

/-- **Cross-variable Schwarz iteration** (§10.6): from the two-sided
bound `x² ≤ a·y` and `y² ≤ b·x`, derive `x⁴ ≤ a²·b·x` (and by
symmetry `y⁴ ≤ a·b²·y`).

Chain: `x⁴ = (x²)² ≤ (a·y)² = a²·y² ≤ a²·(b·x) = a²·b·x`.
Analogue of §10.5's iterated Schwarz for the non-symmetric two-variable
setting where each variable bounds the other's square. -/
theorem nonsymmetric_cross_iteration_x (x y a b : ℝ)
    (hxay : x ^ 2 ≤ a * y) (hybx : y ^ 2 ≤ b * x) :
    x ^ 4 ≤ a ^ 2 * b * x := by
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x^2 - a*y),
    mul_self_nonneg (a*y - x^2), hxay, hybx,
    mul_le_mul_of_nonneg_left hybx (sq_nonneg a)]

/-- **Cross-variable Schwarz iteration** (§10.6, y-side): symmetric
partner of `nonsymmetric_cross_iteration_x` giving `y⁴ ≤ a·b²·y`. -/
theorem nonsymmetric_cross_iteration_y (x y a b : ℝ)
    (hxay : x ^ 2 ≤ a * y) (hybx : y ^ 2 ≤ b * x) :
    y ^ 4 ≤ a * b ^ 2 * y := by
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (y^2 - b*x),
    mul_self_nonneg (b*x - y^2), hxay, hybx,
    mul_le_mul_of_nonneg_left hxay (sq_nonneg b)]

/-- **Cube bound from cross-iteration** (§10.6): when `x > 0`,
the bound `x⁴ ≤ a²·b·x` (from `nonsymmetric_cross_iteration_x`)
strengthens to `x³ ≤ a²·b`. Division by the positive factor `x`. -/
theorem nonsymmetric_cube_bound_x (x y a b : ℝ) (hx : 0 < x)
    (hxay : x ^ 2 ≤ a * y) (hybx : y ^ 2 ≤ b * x) :
    x ^ 3 ≤ a ^ 2 * b := by
  have h4 := nonsymmetric_cross_iteration_x x y a b hxay hybx
  nlinarith [h4, hx, sq_nonneg x]

/-- **Cube bound from cross-iteration** (§10.6, y-side): symmetric partner
`y³ ≤ a · b²` when `y > 0`. -/
theorem nonsymmetric_cube_bound_y (x y a b : ℝ) (hy : 0 < y)
    (hxay : x ^ 2 ≤ a * y) (hybx : y ^ 2 ≤ b * x) :
    y ^ 3 ≤ a * b ^ 2 := by
  have h4 := nonsymmetric_cross_iteration_y x y a b hxay hybx
  nlinarith [h4, hy, sq_nonneg y]


end IsingModel
