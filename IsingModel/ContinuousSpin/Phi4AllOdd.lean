import IsingModel.ContinuousSpin.Phi4Averaging

/-!
# The all-odd case and the φ⁴ single-site positivity

The remaining parity case of GJ Theorem 4.3.1 (p. 59): when all exponents are
odd the integrand is not sign-definite. The key observation is that the
combining can be done at the **innermost** `δ`-integral, where the
integrability dichotomy is handled locally — so no global integrability
hypothesis and no Fubini bridge are needed, and the full single-site
positivity is unconditional, exactly as stated.

For fixed `α, β, γ` and all `k,l,m,n` odd, the `δ`-reflection gives
`∫δ G = −∫δ G''` (with `G''` the `c ↦ −c` integrand), so on the integrable
branch `2·∫δ G = ∫δ (G − G'') = ∫δ 2·(even powers)·e^{−Q}·(δαβγ)·sinh(c·αβγδ)
≥ 0` by `mul_sinh_nonneg`; on the non-integrable branch `∫δ G = 0`. Either
way the inner integral is non-negative, and four iterations of
`integral_nonneg` give the result.

This file completes the discharge of `phi4_single_site_nonneg` (Issue #3913).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.3, Theorem 4.3.1, p. 59
-/

namespace IsingModel.ContinuousSpin

open Real MeasureTheory

/-- The `δ`-reflection identity for the φ⁴ integrand at all-odd exponents:
`phi4Integrand` at `(α,β,γ,−δ)` equals `−(phi4Integrand with c ↦ −c)` at
`(α,β,γ,δ)`, using `Q` even in `δ` and `n` odd. -/
theorem phi4Integrand_neg_delta_all_odd (Q : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hQδ : ∀ α β γ δ, Q α β γ (-δ) = Q α β γ δ)
    (c : ℝ) (k l m : ℕ) {n : ℕ} (hn : Odd n) (α β γ δ : ℝ) :
    phi4Integrand Q c k l m n α β γ (-δ)
      = -phi4Integrand Q (-c) k l m n α β γ δ := by
  unfold phi4Integrand
  rw [hQδ, hn.neg_pow]
  ring

/-- **Inner `δ`-integral non-negativity, all-odd case** (unconditional): for
`c ≥ 0`, all exponents odd, and `Q` even in `δ`, the innermost integral of the
φ⁴ integrand is non-negative. -/
theorem phi4_inner_delta_nonneg_all_odd (Q : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hQδ : ∀ α β γ δ, Q α β γ (-δ) = Q α β γ δ)
    {c : ℝ} (hc : 0 ≤ c) {k l m n : ℕ}
    (hk : Odd k) (hl : Odd l) (hm : Odd m) (hn : Odd n) (α β γ : ℝ) :
    0 ≤ ∫ δ, phi4Integrand Q c k l m n α β γ δ := by
  set G : ℝ → ℝ := fun δ => phi4Integrand Q c k l m n α β γ δ with hG
  set G'' : ℝ → ℝ := fun δ => phi4Integrand Q (-c) k l m n α β γ δ with hG''
  -- reflection: ∫ G = -∫ G''
  have hrefl : (∫ δ, G δ) = -∫ δ, G'' δ := by
    have h1 : (∫ δ, G δ) = ∫ δ, G (-δ) := (integral_comp_neg_real G).symm
    have h2 : (fun δ => G (-δ)) = fun δ => -G'' δ := by
      funext δ
      exact phi4Integrand_neg_delta_all_odd Q hQδ c k l m hn α β γ δ
    rw [h1, h2, integral_neg]
  -- pointwise non-negativity of G - G''
  have hpt : ∀ δ, 0 ≤ G δ - G'' δ := by
    intro δ
    have hGsub : G δ - G'' δ
        = (α ^ (k - 1) * β ^ (l - 1) * γ ^ (m - 1) * δ ^ (n - 1)) *
            Real.exp (-Q α β γ δ) * (2 * ((α * β * γ * δ) *
              Real.sinh (c * (α * β * γ * δ)))) := by
      simp only [hG, hG'']
      unfold phi4Integrand
      rw [Real.exp_add, Real.exp_add, neg_mul, Real.sinh_eq]
      obtain ⟨k', rfl⟩ := hk
      obtain ⟨l', rfl⟩ := hl
      obtain ⟨m', rfl⟩ := hm
      obtain ⟨n', rfl⟩ := hn
      simp only [Nat.add_sub_cancel]
      ring
    rw [hGsub]
    have heven : 0 ≤ α ^ (k - 1) * β ^ (l - 1) * γ ^ (m - 1) * δ ^ (n - 1) := by
      obtain ⟨k', rfl⟩ := hk
      obtain ⟨l', rfl⟩ := hl
      obtain ⟨m', rfl⟩ := hm
      obtain ⟨n', rfl⟩ := hn
      simp only [Nat.add_sub_cancel]
      have : ∀ x : ℝ, ∀ j : ℕ, 0 ≤ x ^ (2 * j) := fun x j => (even_two_mul j).pow_nonneg x
      exact mul_nonneg (mul_nonneg (mul_nonneg (this α k') (this β l'))
        (this γ m')) (this δ n')
    have hsinh : 0 ≤ 2 * ((α * β * γ * δ) * Real.sinh (c * (α * β * γ * δ))) :=
      mul_nonneg (by norm_num) (mul_sinh_nonneg c (α * β * γ * δ) hc)
    exact mul_nonneg (mul_nonneg heven (Real.exp_pos _).le) hsinh
  by_cases hint : Integrable G
  · have hint'' : Integrable G'' := by
      have hcomp : Integrable (fun δ => G (-δ)) :=
        ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_emb
          (MeasurableEquiv.neg ℝ).measurableEmbedding).mpr hint
      have : G'' = fun δ => -G (-δ) := by
        funext δ
        have := phi4Integrand_neg_delta_all_odd Q hQδ c k l m hn α β γ δ
        simp only [hG, hG'']
        rw [← neg_eq_iff_eq_neg]
        exact (phi4Integrand_neg_delta_all_odd Q hQδ c k l m hn α β γ δ).symm
      rw [this]
      exact hcomp.neg
    have h2 : 2 * (∫ δ, G δ) = ∫ δ, (G δ - G'' δ) := by
      rw [integral_sub hint hint'']
      linarith [hrefl]
    have hnn : 0 ≤ ∫ δ, (G δ - G'' δ) := integral_nonneg hpt
    linarith [h2, hnn]
  · rw [integral_undef hint]

/-- **All-odd case** (unconditional): four iterations of `integral_nonneg`
from the inner-`δ` non-negativity. -/
theorem phi4_integral4_nonneg_all_odd (Q : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hQδ : ∀ α β γ δ, Q α β γ (-δ) = Q α β γ δ)
    {c : ℝ} (hc : 0 ≤ c) {k l m n : ℕ}
    (hk : Odd k) (hl : Odd l) (hm : Odd m) (hn : Odd n) :
    0 ≤ ∫ α, ∫ β, ∫ γ, ∫ δ, phi4Integrand Q c k l m n α β γ δ := by
  refine integral_nonneg fun α => ?_
  refine integral_nonneg fun β => ?_
  refine integral_nonneg fun γ => ?_
  exact phi4_inner_delta_nonneg_all_odd Q hQδ hc hk hl hm hn α β γ

/-- **GJ Theorem 4.3.1, the φ⁴ single-site positivity** (formerly the axiom
`phi4_single_site_nonneg`): for `Q` even in each variable and `c ≥ 0`,
`0 ≤ ∫∫∫∫ α^k β^l γ^m δ^n exp(−Q + c·αβγδ)`. Proven unconditionally by the
four-fold sign symmetrisation, split by joint parity: all-even (pointwise
non-negative), mixed parity (vanishes by an even/odd reflection pair), and
all-odd (inner-`δ` `sinh` non-negativity). Reference: Glimm–Jaffe, 2nd ed.,
§4.3, Theorem 4.3.1, p. 59. -/
theorem phi4_single_site_nonneg (Q : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hQα : ∀ α β γ δ, Q (-α) β γ δ = Q α β γ δ)
    (hQβ : ∀ α β γ δ, Q α (-β) γ δ = Q α β γ δ)
    (hQγ : ∀ α β γ δ, Q α β (-γ) δ = Q α β γ δ)
    (hQδ : ∀ α β γ δ, Q α β γ (-δ) = Q α β γ δ)
    (c : ℝ) (hc : 0 ≤ c)
    (k l m n : ℕ) :
    0 ≤ ∫ α, ∫ β, ∫ γ, ∫ δ,
      α ^ k * β ^ l * γ ^ m * δ ^ n *
      Real.exp (-Q α β γ δ + c * (α * β * γ * δ))
      ∂volume ∂volume ∂volume ∂volume := by
  change 0 ≤ ∫ α, ∫ β, ∫ γ, ∫ δ, phi4Integrand Q c k l m n α β γ δ
  by_cases hall_even : Even k ∧ Even l ∧ Even m ∧ Even n
  · exact phi4_integral4_nonneg_all_even Q c hall_even.1 hall_even.2.1
      hall_even.2.2.1 hall_even.2.2.2
  by_cases hall_odd : Odd k ∧ Odd l ∧ Odd m ∧ Odd n
  · exact phi4_integral4_nonneg_all_odd Q hQδ hc hall_odd.1 hall_odd.2.1
      hall_odd.2.2.1 hall_odd.2.2.2
  · rw [phi4_integral4_eq_zero_mixed Q hQα hQβ hQγ hQδ c (not_or.mpr ⟨hall_even, hall_odd⟩)]

end IsingModel.ContinuousSpin
