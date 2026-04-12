import IsingModel.ContinuousSpin.Measure
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# φ⁴ inequalities

The φ⁴ correlation inequalities from Glimm–Jaffe §4.3, pp. 59–62.

## Main results (proved)

* `quartic_identity` — the quartic algebraic identity for the orthogonal transformation
* `sum_sq_identity`, `inner_product_identity` — orthogonality identities
* `integral_odd_eq_zero` (in Measure.lean) — odd function integral vanishes

## Main results (axiom, to be proved)

* `phi4_single_site_nonneg` — single-site non-negativity:
  `∫ α^k β^l γ^m δ^n exp(-Q) dαdβdγdδ ≥ 0` where Q is even + ferromagnetic

## References

* Glimm–Jaffe, *Quantum Physics*, §4.3, pp. 59–62.
-/

namespace IsingModel.ContinuousSpin

open Real MeasureTheory Finset

/-! ## Single-site orthogonal transformation -/

/-- The `α` variable: `α = (ξ + χ + ξ' + χ') / 2`. -/
noncomputable def phi4Alpha (ξ χ ξ' χ' : ℝ) : ℝ := (ξ + χ + ξ' + χ') / 2

/-- The `β` variable: `β = (ξ + χ - ξ' - χ') / 2`. -/
noncomputable def phi4Beta (ξ χ ξ' χ' : ℝ) : ℝ := (ξ + χ - ξ' - χ') / 2

/-- The `γ` variable: `γ = (ξ - χ + ξ' - χ') / 2`. -/
noncomputable def phi4Gamma (ξ χ ξ' χ' : ℝ) : ℝ := (ξ - χ + ξ' - χ') / 2

/-- The `δ` variable: `δ = (ξ - χ - ξ' + χ') / 2`. -/
noncomputable def phi4Delta (ξ χ ξ' χ' : ℝ) : ℝ := (ξ - χ - ξ' + χ') / 2

/-! ## Algebraic identities -/

/-- The quartic identity:
`4(ξ⁴ + χ⁴ + ξ'⁴ + χ'⁴) = (α⁴+β⁴+γ⁴+δ⁴) + 6·Σα²β² + 24·αβγδ`.
Reference: Glimm–Jaffe, §4.3, p. 61. -/
theorem quartic_identity (ξ χ ξ' χ' : ℝ) :
    let α := phi4Alpha ξ χ ξ' χ'
    let β := phi4Beta ξ χ ξ' χ'
    let γ := phi4Gamma ξ χ ξ' χ'
    let δ := phi4Delta ξ χ ξ' χ'
    4 * (ξ ^ 4 + χ ^ 4 + ξ' ^ 4 + χ' ^ 4) =
    (α ^ 4 + β ^ 4 + γ ^ 4 + δ ^ 4) +
    6 * (α ^ 2 * β ^ 2 + α ^ 2 * γ ^ 2 + α ^ 2 * δ ^ 2 +
         β ^ 2 * γ ^ 2 + β ^ 2 * δ ^ 2 + γ ^ 2 * δ ^ 2) +
    24 * (α * β * γ * δ) := by
  simp only [phi4Alpha, phi4Beta, phi4Gamma, phi4Delta]; ring

/-- Sum of squares identity (orthogonality):
`ξ² + χ² + ξ'² + χ'² = α² + β² + γ² + δ²`. -/
theorem sum_sq_identity (ξ χ ξ' χ' : ℝ) :
    let α := phi4Alpha ξ χ ξ' χ'
    let β := phi4Beta ξ χ ξ' χ'
    let γ := phi4Gamma ξ χ ξ' χ'
    let δ := phi4Delta ξ χ ξ' χ'
    ξ ^ 2 + χ ^ 2 + ξ' ^ 2 + χ' ^ 2 = α ^ 2 + β ^ 2 + γ ^ 2 + δ ^ 2 := by
  simp only [phi4Alpha, phi4Beta, phi4Gamma, phi4Delta]; ring

/-- Linear identity: `ξ + χ + ξ' + χ' = 2α`. -/
theorem sum_linear_identity (ξ χ ξ' χ' : ℝ) :
    ξ + χ + ξ' + χ' = 2 * phi4Alpha ξ χ ξ' χ' := by
  simp only [phi4Alpha]; ring

/-- Inner product identity (interaction term):
`ξ₁ξ₂ + χ₁χ₂ + ξ'₁ξ'₂ + χ'₁χ'₂ = α₁α₂ + β₁β₂ + γ₁γ₂ + δ₁δ₂`. -/
theorem inner_product_identity (ξ₁ χ₁ ξ'₁ χ'₁ ξ₂ χ₂ ξ'₂ χ'₂ : ℝ) :
    ξ₁ * ξ₂ + χ₁ * χ₂ + ξ'₁ * ξ'₂ + χ'₁ * χ'₂ =
    phi4Alpha ξ₁ χ₁ ξ'₁ χ'₁ * phi4Alpha ξ₂ χ₂ ξ'₂ χ'₂ +
    phi4Beta ξ₁ χ₁ ξ'₁ χ'₁ * phi4Beta ξ₂ χ₂ ξ'₂ χ'₂ +
    phi4Gamma ξ₁ χ₁ ξ'₁ χ'₁ * phi4Gamma ξ₂ χ₂ ξ'₂ χ'₂ +
    phi4Delta ξ₁ χ₁ ξ'₁ χ'₁ * phi4Delta ξ₂ χ₂ ξ'₂ χ'₂ := by
  simp only [phi4Alpha, phi4Beta, phi4Gamma, phi4Delta]; ring

/-! ## Single-site non-negativity (Theorem 4.3.1 core)

The proof of Theorem 4.3.1 reduces, per site, to showing that
`∫ α^k β^l γ^m δ^n exp(-Q(α,β,γ,δ) + c·αβγδ) dαdβdγdδ ≥ 0`
where Q is even in each variable and c > 0.

Strategy:
1. Expand `exp(c·αβγδ) = Σ_j (c·αβγδ)^j / j!`
2. `∫ α^{k+j} β^{l+j} γ^{m+j} δ^{n+j} exp(-Q) = 0` unless k+j, l+j, m+j, n+j all even
3. When all even, the integral factors as a product of 1D integrals of even functions
   times |x|^{2p} exp(-even(x)), which are all non-negative.
4. So the total is a sum of non-negative terms × positive coefficients c^j/j! ≥ 0.

The integrability is guaranteed by `integrableOn_rpow_mul_exp_neg_mul_rpow`
from `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`.

For now, this is stated as an axiom. The measure-theoretic proof
(Fubini + integral_tsum + integrability) will be developed incrementally. -/

/-- The integral of an odd-power monomial times an even weight vanishes.
`∫ x^(2k+1) exp(-P(x²)) dx = 0` because the integrand is odd.
This is used repeatedly in the single-site φ⁴ proof. -/
theorem integral_odd_power_even_weight_eq_zero (P : ℝ → ℝ) (k : ℕ) :
    ∫ x, x ^ (2 * k + 1) * Real.exp (-P (x ^ 2)) ∂volume = 0 := by
  apply integral_odd_eq_zero
  intro x
  have hodd : (-x) ^ (2 * k + 1) = -(x ^ (2 * k + 1)) :=
    (Odd.neg_pow ⟨k, rfl⟩) x
  rw [hodd, neg_sq]
  ring

/-- `t * sinh(c * t) ≥ 0` for `c ≥ 0`: both factors have the same sign.
This is the key positivity lemma for the ALL-ODD case of `phi4_single_site_nonneg`. -/
theorem mul_sinh_nonneg (c t : ℝ) (hc : 0 ≤ c) : 0 ≤ t * Real.sinh (c * t) := by
  by_cases ht : 0 ≤ t
  · exact mul_nonneg ht (Real.sinh_nonneg_iff.mpr (mul_nonneg hc ht))
  · push Not at ht
    -- t * sinh(ct) = (-t) * sinh(-(ct)) = (-t) * sinh(-ct), both ≥ 0
    rw [show t * Real.sinh (c * t) = (-t) * Real.sinh (-(c * t)) from by
      rw [Real.sinh_neg]; ring]
    exact mul_nonneg (neg_nonneg.mpr ht.le)
      (Real.sinh_nonneg_iff.mpr (by
        rw [neg_nonneg]; exact mul_nonpos_of_nonneg_of_nonpos hc ht.le))

/-- The integral of a non-negative function is non-negative.
Helper for the even-power case of `phi4_single_site_nonneg`. -/
private theorem integral_nonneg_of_nonneg_ae (f : ℝ → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    0 ≤ ∫ x, f x ∂volume :=
  integral_nonneg hf

/-- **Single-site non-negativity** (core of Theorem 4.3.1):
For even `Q` and `c ≥ 0`, the monomial integral against `exp(-Q + c·αβγδ)` is ≥ 0.

Proof sketch:
- `exp(-Q + c·αβγδ) = exp(-Q) · Σ_j (c·αβγδ)^j / j!`
- Each term: `∫ α^{k+j} β^{l+j} γ^{m+j} δ^{n+j} exp(-Q)`
- If any exponent is odd, the integral vanishes by `integral_odd_eq_zero`
  (Q is even in that variable, so the integrand is odd).
- If all exponents are even, the integrand is ≥ 0, so the integral is ≥ 0.
- The sum has coefficients c^j/j! ≥ 0, so the total is ≥ 0.

The full proof requires Fubini (nested integrals), integrability estimates
(`integrableOn_rpow_mul_exp_neg_mul_rpow`), and `integral_tsum` (swap sum/integral).
These are available in mathlib but the assembly is deferred. -/
theorem phi4_single_site_nonneg
    (Q : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hQ_even_α : ∀ α β γ δ, Q (-α) β γ δ = Q α β γ δ)
    (hQ_even_β : ∀ α β γ δ, Q α (-β) γ δ = Q α β γ δ)
    (hQ_even_γ : ∀ α β γ δ, Q α β (-γ) δ = Q α β γ δ)
    (hQ_even_δ : ∀ α β γ δ, Q α β γ (-δ) = Q α β γ δ)
    (c : ℝ) (hc : 0 ≤ c)
    (k l m n : ℕ) :
    0 ≤ ∫ α, ∫ β, ∫ γ, ∫ δ,
      α ^ k * β ^ l * γ ^ m * δ ^ n *
      Real.exp (-Q α β γ δ + c * (α * β * γ * δ))
      ∂volume ∂volume ∂volume ∂volume := by
  -- Symmetrization via α → -α. Let f(α) = inner triple integral.
  let f : ℝ → ℝ := fun α =>
    ∫ β, ∫ γ, ∫ δ,
      α ^ k * β ^ l * γ ^ m * δ ^ n *
      Real.exp (-Q α β γ δ + c * (α * β * γ * δ))
      ∂volume ∂volume ∂volume
  -- ∫ f(α) = ∫ f(-α) by integral_neg_eq_self
  have hsymm : ∫ α, f α ∂volume = ∫ α, f (-α) ∂volume :=
    (integral_neg_eq_self f volume).symm
  -- 2∫f = ∫(f + f∘neg), so it suffices to show f(α) + f(-α) ≥ 0 pointwise
  suffices hpw : ∀ α, 0 ≤ f α + f (-α) by
    have h2 : 2 * ∫ α, f α ∂volume =
        ∫ α, f α ∂volume + ∫ α, f (-α) ∂volume := by rw [hsymm]; ring
    -- ∫(f + f∘neg) ≥ 0 by integral_nonneg
    -- But we need integrability to split the integral. Use sorry for now.
    sorry
  -- Pointwise: f(α) + f(-α). Use Q(-α,...) = Q(α,...) and parity of α^k.
  -- f(-α) = ∫∫∫ (-α)^k β^l γ^m δ^n exp(-Q(-α,β,γ,δ) + c(-α)βγδ)
  --       = (-1)^k ∫∫∫ α^k β^l γ^m δ^n exp(-Q(α,β,γ,δ) - cαβγδ)  [Q even in α]
  -- So f(α) + f(-α) = ∫∫∫ α^k β^l γ^m δ^n exp(-Q) [exp(cαβγδ) + (-1)^k exp(-cαβγδ)]
  -- If k even: [...] = 2 cosh(cαβγδ) ≥ 0
  -- If k odd: [...] = 2 sinh(cαβγδ), sign depends on αβγδ — need further symmetrization
  -- Full pointwise analysis requires nested symmetrization for all 4 variables.
  -- Deferred pending integral linearity assembly.
  intro α
  sorry

/-! ## Corollary 4.3.2: Lebowitz inequality

For continuous spins with φ⁴ distribution, the Lebowitz inequality states:
1. `0 ≤ ⟨t^A t^B⟩ - ⟨t^A⟩⟨t^B⟩`  (= GKS-II for the duplicate system)
2. `0 ≤ ⟨q^A q^B⟩ - ⟨q^A⟩⟨q^B⟩`
3. `0 ≤ ⟨t^A⟩⟨q^B⟩ - ⟨t^A q^B⟩`  (the NEW inequality)

where `t_i = (ξ_i + χ_i)/√2`, `q_i = (ξ_i - χ_i)/√2` are the duplicate variables.

The proof of (3) uses Theorem 4.3.1:
```
⟨t^A⟩⟨q^B⟩ - ⟨t^A q^B⟩ = ⟨t^A (⟨q^B⟩ - q^B)⟩
  = 2^{-(|A|+|B|)/2} ⟨(α+β)^A [(γ+δ)^B - (γ-δ)^B]⟩
```
Then `(α+β)^A [(γ+δ)^B - (γ-δ)^B]` is a sum of monomials α^a β^b γ^c δ^d
with non-negative coefficients, and each `⟨α^a β^b γ^c δ^d⟩ ≥ 0` by
Theorem 4.3.1.

Reference: Glimm–Jaffe, Corollary 4.3.2, p. 60. -/

-- The Lebowitz inequality requires the full multi-site theory with
-- product measures, expectations, and the duplicate variable framework
-- for continuous spins. This infrastructure builds on cExpectation
-- and phi4_single_site_nonneg, and will be developed in subsequent work.

/-! ## Corollary 4.3.4: truncated three-point correlation ≤ 0

For continuous spins with φ⁴ distribution and `h_i ≥ 0`:
```
⟨ξ_i ξ_j ξ_k⟩ - ⟨ξ_i⟩⟨ξ_j ξ_k⟩ - ⟨ξ_j⟩⟨ξ_i ξ_k⟩
  - ⟨ξ_k⟩⟨ξ_i ξ_j⟩ + 2⟨ξ_i⟩⟨ξ_j⟩⟨ξ_k⟩ ≤ 0
```

The proof uses Corollary 4.3.2(3) and GKS-II (`⟨ξ_i⟩ ≥ 0`).

Reference: Glimm–Jaffe, Corollary 4.3.4, p. 62. -/

-- This follows algebraically from Corollary 4.3.2(3) and GKS-I/II.
-- The formalization requires the multi-site duplicate variable framework.

end IsingModel.ContinuousSpin
