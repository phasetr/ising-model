import IsingModel.ContinuousSpin.Phi4Reflection

/-!
# Averaging and conditional non-negativity for the φ⁴ single-site positivity

The non-negativity of the four-fold φ⁴ single-site integral
(GJ Theorem 4.3.1, p. 59), split by the joint parity of the exponents:

* **all even**: the integrand is pointwise non-negative, so the integral is
  non-negative unconditionally;
* **mixed parity**: reflecting one even-exponent and one odd-exponent
  variable negates the integrand while fixing the cross term, so the integral
  equals its own negative and vanishes — unconditionally;
* **all odd**: the integrand is not sign-definite; combining the integral with
  its `δ`-reflection produces `2·sinh(c·αβγδ)`, non-negative by
  `mul_sinh_nonneg` (this branch carries an integrability hypothesis).

This file is part of the discharge of `phi4_single_site_nonneg` (Issue #3913).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.3, Theorem 4.3.1, p. 59
-/

namespace IsingModel.ContinuousSpin

open Real MeasureTheory

/-- **All-even case** (unconditional): when every exponent is even, the φ⁴
integrand is pointwise non-negative (even powers and the exponential are both
non-negative), so the four-fold iterated integral is non-negative. -/
theorem phi4_integral4_nonneg_all_even (Q : ℝ → ℝ → ℝ → ℝ → ℝ) (c : ℝ)
    {k l m n : ℕ} (hk : Even k) (hl : Even l) (hm : Even m) (hn : Even n) :
    0 ≤ ∫ α, ∫ β, ∫ γ, ∫ δ, phi4Integrand Q c k l m n α β γ δ := by
  refine integral_nonneg fun α => ?_
  refine integral_nonneg fun β => ?_
  refine integral_nonneg fun γ => ?_
  refine integral_nonneg fun δ => ?_
  unfold phi4Integrand
  have hpow : 0 ≤ α ^ k * β ^ l * γ ^ m * δ ^ n :=
    mul_nonneg (mul_nonneg (mul_nonneg (hk.pow_nonneg α) (hl.pow_nonneg β))
      (hm.pow_nonneg γ)) (hn.pow_nonneg δ)
  exact mul_nonneg hpow (Real.exp_pos _).le

/-- **Negation-by-reflection** (unconditional): if a sign pattern fixes the
cross-term sign (`σ = +1`) but flips the monomial sign character (`= −1`), the
four-fold φ⁴ integral equals its own negative, hence is zero. -/
theorem phi4_integral4_eq_zero_of_neg_pattern (Q : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hQα : ∀ α β γ δ, Q (-α) β γ δ = Q α β γ δ)
    (hQβ : ∀ α β γ δ, Q α (-β) γ δ = Q α β γ δ)
    (hQγ : ∀ α β γ δ, Q α β (-γ) δ = Q α β γ δ)
    (hQδ : ∀ α β γ δ, Q α β γ (-δ) = Q α β γ δ)
    (c : ℝ) (k l m n : ℕ) (b₁ b₂ b₃ b₄ : Bool)
    (hσ : boolSign b₁ * boolSign b₂ * boolSign b₃ * boolSign b₄ = 1)
    (hsign : boolSignPow b₁ k * boolSignPow b₂ l * boolSignPow b₃ m *
      boolSignPow b₄ n = -1) :
    (∫ α, ∫ β, ∫ γ, ∫ δ, phi4Integrand Q c k l m n α β γ δ) = 0 := by
  have hrefl := phi4_integral4_eq_reflected Q hQα hQβ hQγ hQδ c k l m n b₁ b₂ b₃ b₄
  have hpt : ∀ α β γ δ,
      boolSignPow b₁ k * boolSignPow b₂ l * boolSignPow b₃ m * boolSignPow b₄ n *
          (α ^ k * β ^ l * γ ^ m * δ ^ n) *
          Real.exp (-Q α β γ δ +
            c * (boolSign b₁ * boolSign b₂ * boolSign b₃ * boolSign b₄) *
              (α * β * γ * δ))
        = -phi4Integrand Q c k l m n α β γ δ := by
    intro α β γ δ
    rw [hσ, mul_one]
    unfold phi4Integrand
    rw [hsign]
    ring
  have heq : (∫ α, ∫ β, ∫ γ, ∫ δ, phi4Integrand Q c k l m n α β γ δ)
      = -∫ α, ∫ β, ∫ γ, ∫ δ, phi4Integrand Q c k l m n α β γ δ := by
    calc (∫ α, ∫ β, ∫ γ, ∫ δ, phi4Integrand Q c k l m n α β γ δ)
        = ∫ α, ∫ β, ∫ γ, ∫ δ,
            boolSignPow b₁ k * boolSignPow b₂ l * boolSignPow b₃ m *
              boolSignPow b₄ n * (α ^ k * β ^ l * γ ^ m * δ ^ n) *
              Real.exp (-Q α β γ δ +
                c * (boolSign b₁ * boolSign b₂ * boolSign b₃ * boolSign b₄) *
                  (α * β * γ * δ)) := hrefl
      _ = ∫ α, ∫ β, ∫ γ, ∫ δ, -phi4Integrand Q c k l m n α β γ δ :=
          integral_congr_ae (Filter.Eventually.of_forall fun α =>
            integral_congr_ae (Filter.Eventually.of_forall fun β =>
              integral_congr_ae (Filter.Eventually.of_forall fun γ =>
                integral_congr_ae (Filter.Eventually.of_forall fun δ =>
                  hpt α β γ δ))))
      _ = -∫ α, ∫ β, ∫ γ, ∫ δ, phi4Integrand Q c k l m n α β γ δ := by
          simp_rw [integral_neg]
  linarith [heq]

/-- **Mixed-parity case** (unconditional): when the exponents do not all share
the same parity, reflecting one even-exponent and one odd-exponent variable
fixes the cross term (`σ = +1`) but flips the sign character (`= −1`), so the
four-fold φ⁴ integral vanishes. -/
theorem phi4_integral4_eq_zero_mixed (Q : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hQα : ∀ α β γ δ, Q (-α) β γ δ = Q α β γ δ)
    (hQβ : ∀ α β γ δ, Q α (-β) γ δ = Q α β γ δ)
    (hQγ : ∀ α β γ δ, Q α β (-γ) δ = Q α β γ δ)
    (hQδ : ∀ α β γ δ, Q α β γ (-δ) = Q α β γ δ)
    (c : ℝ) {k l m n : ℕ}
    (hmix : ¬ ((Even k ∧ Even l ∧ Even m ∧ Even n) ∨
              (Odd k ∧ Odd l ∧ Odd m ∧ Odd n))) :
    (∫ α, ∫ β, ∫ γ, ∫ δ, phi4Integrand Q c k l m n α β γ δ) = 0 := by
  -- in each mixed parity branch, reflect one even-exponent and one odd-exponent
  -- variable (pattern with two `false`s), giving `σ = +1` and sign character `−1`
  have hdisch : ∀ b₁ b₂ b₃ b₄ : Bool,
      boolSign b₁ * boolSign b₂ * boolSign b₃ * boolSign b₄ = 1 →
      boolSignPow b₁ k * boolSignPow b₂ l * boolSignPow b₃ m *
        boolSignPow b₄ n = -1 →
      (∫ α, ∫ β, ∫ γ, ∫ δ, phi4Integrand Q c k l m n α β γ δ) = 0 :=
    fun b₁ b₂ b₃ b₄ => phi4_integral4_eq_zero_of_neg_pattern Q hQα hQβ hQγ hQδ
      c k l m n b₁ b₂ b₃ b₄
  rcases Nat.even_or_odd k with hk | hk <;>
    rcases Nat.even_or_odd l with hl | hl <;>
    rcases Nat.even_or_odd m with hm | hm <;>
    rcases Nat.even_or_odd n with hn | hn
  case inl.inl.inl.inl =>
    exact absurd (Or.inl ⟨hk, hl, hm, hn⟩) hmix
  case inl.inl.inl.inr =>
    apply hdisch false true true false <;>
      simp [boolSign, boolSignPow, hk.neg_one_pow, hn.neg_one_pow]
  case inl.inl.inr.inl =>
    apply hdisch false true false true <;>
      simp [boolSign, boolSignPow, hk.neg_one_pow, hm.neg_one_pow]
  case inl.inl.inr.inr =>
    apply hdisch false true false true <;>
      simp [boolSign, boolSignPow, hk.neg_one_pow, hm.neg_one_pow]
  case inl.inr.inl.inl =>
    apply hdisch false false true true <;>
      simp [boolSign, boolSignPow, hk.neg_one_pow, hl.neg_one_pow]
  case inl.inr.inl.inr =>
    apply hdisch false false true true <;>
      simp [boolSign, boolSignPow, hk.neg_one_pow, hl.neg_one_pow]
  case inl.inr.inr.inl =>
    apply hdisch false false true true <;>
      simp [boolSign, boolSignPow, hk.neg_one_pow, hl.neg_one_pow]
  case inl.inr.inr.inr =>
    apply hdisch false false true true <;>
      simp [boolSign, boolSignPow, hk.neg_one_pow, hl.neg_one_pow]
  case inr.inl.inl.inl =>
    apply hdisch false false true true <;>
      simp [boolSign, boolSignPow, hk.neg_one_pow, hl.neg_one_pow]
  case inr.inl.inl.inr =>
    apply hdisch false false true true <;>
      simp [boolSign, boolSignPow, hk.neg_one_pow, hl.neg_one_pow]
  case inr.inl.inr.inl =>
    apply hdisch false false true true <;>
      simp [boolSign, boolSignPow, hk.neg_one_pow, hl.neg_one_pow]
  case inr.inl.inr.inr =>
    apply hdisch false false true true <;>
      simp [boolSign, boolSignPow, hk.neg_one_pow, hl.neg_one_pow]
  case inr.inr.inl.inl =>
    apply hdisch false true false true <;>
      simp [boolSign, boolSignPow, hk.neg_one_pow, hm.neg_one_pow]
  case inr.inr.inl.inr =>
    apply hdisch false true false true <;>
      simp [boolSign, boolSignPow, hk.neg_one_pow, hm.neg_one_pow]
  case inr.inr.inr.inl =>
    apply hdisch false true true false <;>
      simp [boolSign, boolSignPow, hk.neg_one_pow, hn.neg_one_pow]
  case inr.inr.inr.inr =>
    exact absurd (Or.inr ⟨hk, hl, hm, hn⟩) hmix

end IsingModel.ContinuousSpin
