import IsingModel.ContinuousSpin.Phi4

/-!
# Sign-symmetrisation core for the φ⁴ single-site positivity

The integrability-free building blocks for the four-fold sign symmetrisation
of GJ Theorem 4.3.1 (the single-site computation, p. 59): the invariance of
the real integral under `x ↦ -x` (the four sign flips are measure-preserving)
and the sign-character trichotomy that, after averaging the integrand over
the sixteen sign patterns, collapses to `cosh` / `sinh` / `0` according to the
joint parity of the exponents.

This file is part of the discharge of the `phi4_single_site_nonneg` axiom
(Issue #3913).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.3, Theorem 4.3.1, p. 59
-/

namespace IsingModel.ContinuousSpin

open Real MeasureTheory

/-- **Sign-flip invariance of the real integral**: composing with `x ↦ -x`
leaves the Lebesgue integral unchanged (the reflection is measure-preserving).
Holds unconditionally — both sides take the junk value `0` together when the
integrand is not integrable. -/
theorem integral_comp_neg_real (f : ℝ → ℝ) :
    ∫ x, f (-x) = ∫ x, f x := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
    (MeasurableEquiv.neg ℝ).measurableEmbedding f
  simpa using h

/-- The real sign attached to a `Bool`: `true ↦ +1`, `false ↦ −1`. -/
def boolSign (b : Bool) : ℝ := if b then 1 else -1

/-- A signed power: `boolSign b ^ e`. Equals `1` for even `e`, and
`boolSign b` for odd `e`. -/
def boolSignPow (b : Bool) (e : ℕ) : ℝ := boolSign b ^ e

/-- The sign of `true` is `+1`. -/
@[simp] theorem boolSign_true : boolSign true = 1 := rfl

/-- The sign of `false` is `−1`. -/
@[simp] theorem boolSign_false : boolSign false = -1 := rfl

/-- A bool sign squares to one. -/
theorem boolSign_sq (b : Bool) : boolSign b ^ 2 = 1 := by
  cases b <;> norm_num [boolSign]

/-- A signed power collapses to `1` for even exponents. -/
theorem boolSignPow_even {e : ℕ} (he : Even e) (b : Bool) :
    boolSignPow b e = 1 := by
  cases b <;> simp [boolSignPow, boolSign, he.neg_one_pow]

/-- A signed power collapses to the sign itself for odd exponents. -/
theorem boolSignPow_odd {e : ℕ} (ho : Odd e) (b : Bool) :
    boolSignPow b e = boolSign b := by
  cases b <;> simp [boolSignPow, boolSign, ho.neg_one_pow]

/-- **Sign-average, all-even case** (GJ p. 59): when every exponent is even,
the signed-exponential average over the sixteen sign patterns is
`16·cosh(c·t)`. -/
theorem sign_average_all_even (c t : ℝ) {k l m n : ℕ}
    (hk : Even k) (hl : Even l) (hm : Even m) (hn : Even n) :
    (∑ b : Bool × Bool × Bool × Bool,
        boolSignPow b.1 k * boolSignPow b.2.1 l *
          boolSignPow b.2.2.1 m * boolSignPow b.2.2.2 n *
          Real.exp (c * (boolSign b.1 * boolSign b.2.1 *
            boolSign b.2.2.1 * boolSign b.2.2.2) * t))
      = 16 * Real.cosh (c * t) := by
  rw [Real.cosh_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool,
    boolSignPow_even hk, boolSignPow_even hl, boolSignPow_even hm,
    boolSignPow_even hn, boolSign_true, boolSign_false,
    mul_one, one_mul, neg_mul, neg_neg, mul_neg]
  ring

/-- **Sign-average, all-odd case** (GJ p. 59): when every exponent is odd,
the signed-exponential average over the sixteen sign patterns is
`16·sinh(c·t)`. -/
theorem sign_average_all_odd (c t : ℝ) {k l m n : ℕ}
    (hk : Odd k) (hl : Odd l) (hm : Odd m) (hn : Odd n) :
    (∑ b : Bool × Bool × Bool × Bool,
        boolSignPow b.1 k * boolSignPow b.2.1 l *
          boolSignPow b.2.2.1 m * boolSignPow b.2.2.2 n *
          Real.exp (c * (boolSign b.1 * boolSign b.2.1 *
            boolSign b.2.2.1 * boolSign b.2.2.2) * t))
      = 16 * Real.sinh (c * t) := by
  rw [Real.sinh_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool,
    boolSignPow_odd hk, boolSignPow_odd hl, boolSignPow_odd hm,
    boolSignPow_odd hn, boolSign_true, boolSign_false,
    mul_one, one_mul, neg_mul, neg_neg, mul_neg]
  ring

/-- **Sign-average, mixed-parity case** (GJ p. 59): when the exponents do not
all share the same parity, the signed-exponential average over the sixteen
sign patterns vanishes. The cancellation comes from summing over the sign of
one even-exponent variable and one odd-exponent variable. -/
theorem sign_average_mixed (c t : ℝ) {k l m n : ℕ}
    (hmix : ¬ ((Even k ∧ Even l ∧ Even m ∧ Even n) ∨
              (Odd k ∧ Odd l ∧ Odd m ∧ Odd n))) :
    (∑ b : Bool × Bool × Bool × Bool,
        boolSignPow b.1 k * boolSignPow b.2.1 l *
          boolSignPow b.2.2.1 m * boolSignPow b.2.2.2 n *
          Real.exp (c * (boolSign b.1 * boolSign b.2.1 *
            boolSign b.2.2.1 * boolSign b.2.2.2) * t))
      = 0 := by
  -- expand every signed power to `1` (even) or `boolSign` (odd) via the parity
  -- of each exponent, then the explicit 16-term sum cancels in pairs
  rcases Nat.even_or_odd k with hk | hk <;>
    rcases Nat.even_or_odd l with hl | hl <;>
    rcases Nat.even_or_odd m with hm | hm <;>
    rcases Nat.even_or_odd n with hn | hn <;>
    -- the two pure-parity cases contradict `hmix`; the rest cancel in pairs
    first
      | exact absurd (Or.inl ⟨‹Even k›, ‹Even l›, ‹Even m›, ‹Even n›⟩) hmix
      | exact absurd (Or.inr ⟨‹Odd k›, ‹Odd l›, ‹Odd m›, ‹Odd n›⟩) hmix
      | (simp only [Fintype.sum_prod_type, Fintype.sum_bool,
          boolSignPow_even, boolSignPow_odd, hk, hl, hm, hn,
          boolSign_true, boolSign_false, mul_one, one_mul,
          neg_mul, neg_neg, mul_neg]
         ring)

/-- **The four-fold sign-average trichotomy** (GJ p. 59), assembled form:
averaging `boolSignᵏˡᵐⁿ · exp(c·σ·t)` over the sixteen sign patterns gives
`16·cosh(c·t)` (all exponents even), `16·sinh(c·t)` (all odd), or `0`
(mixed parity). -/
theorem sign_average_trichotomy (c t : ℝ) (k l m n : ℕ) :
    (∑ b : Bool × Bool × Bool × Bool,
        boolSignPow b.1 k * boolSignPow b.2.1 l *
          boolSignPow b.2.2.1 m * boolSignPow b.2.2.2 n *
          Real.exp (c * (boolSign b.1 * boolSign b.2.1 *
            boolSign b.2.2.1 * boolSign b.2.2.2) * t))
      = if Even k ∧ Even l ∧ Even m ∧ Even n then 16 * Real.cosh (c * t)
        else if Odd k ∧ Odd l ∧ Odd m ∧ Odd n then 16 * Real.sinh (c * t)
        else 0 := by
  split_ifs with he ho
  · exact sign_average_all_even c t he.1 he.2.1 he.2.2.1 he.2.2.2
  · exact sign_average_all_odd c t ho.1 ho.2.1 ho.2.2.1 ho.2.2.2
  · exact sign_average_mixed c t (not_or.mpr ⟨he, ho⟩)

end IsingModel.ContinuousSpin
