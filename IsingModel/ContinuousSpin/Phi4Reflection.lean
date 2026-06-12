import IsingModel.ContinuousSpin.Phi4Symmetrization

/-!
# Iterated-integral sign reflection for the φ⁴ single-site positivity

The unconditional reflection step of GJ's four-fold sign symmetrisation
(Theorem 4.3.1, p. 59): the four-fold iterated integral of the single-site
integrand `α^k β^l γ^m δ^n · exp(−Q + c·αβγδ)` is invariant under every sign
pattern `(b₁,b₂,b₃,b₄) ∈ Bool⁴` acting by `x ↦ boolSign bᵢ · x`. Because `Q`
is even in each variable, the reflected integrand is the original one times
the sign character `boolSignᵏˡᵐⁿ` with the cross term `c·αβγδ` carrying the
joint sign `σ = ∏ boolSign bᵢ`.

No integrability hypothesis is needed here: each sign flip is the
measure-preserving reflection of `integral_comp_neg_real`, applied at one
level of the iterated integral. The averaging over the sixteen patterns
(which does need integrability) is carried out in a subsequent PR.

This file is part of the discharge of `phi4_single_site_nonneg` (Issue #3913).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.3, Theorem 4.3.1, p. 59
-/

namespace IsingModel.ContinuousSpin

open Real MeasureTheory

/-- The single-site φ⁴ integrand of GJ Theorem 4.3.1:
`α^k β^l γ^m δ^n · exp(−Q(α,β,γ,δ) + c·αβγδ)`. -/
noncomputable def phi4Integrand (Q : ℝ → ℝ → ℝ → ℝ → ℝ) (c : ℝ)
    (k l m n : ℕ) (α β γ δ : ℝ) : ℝ :=
  α ^ k * β ^ l * γ ^ m * δ ^ n *
    Real.exp (-Q α β γ δ + c * (α * β * γ * δ))

/-- **Sign-flip invariance of the real integral, multiplier form**: composing
with `x ↦ boolSign b · x` leaves the Lebesgue integral unchanged. -/
theorem integral_comp_boolSign_mul (b : Bool) (f : ℝ → ℝ) :
    ∫ x, f (boolSign b * x) = ∫ x, f x := by
  cases b with
  | true => simp [boolSign]
  | false => simpa [boolSign] using integral_comp_neg_real f

/-- **The reflected integrand identity** (pointwise): substituting
`boolSign bᵢ · (variable)` into the φ⁴ integrand, with `Q` even in each
variable, yields the sign character `boolSignᵏˡᵐⁿ` times the original
monomial `α^k β^l γ^m δ^n` and the weight `exp(−Q)` with the cross term
`c·αβγδ` carrying the joint sign `σ = ∏ boolSign bᵢ`. -/
theorem phi4Integrand_boolSign_mul (Q : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hQα : ∀ α β γ δ, Q (-α) β γ δ = Q α β γ δ)
    (hQβ : ∀ α β γ δ, Q α (-β) γ δ = Q α β γ δ)
    (hQγ : ∀ α β γ δ, Q α β (-γ) δ = Q α β γ δ)
    (hQδ : ∀ α β γ δ, Q α β γ (-δ) = Q α β γ δ)
    (c : ℝ) (k l m n : ℕ) (b₁ b₂ b₃ b₄ : Bool) (α β γ δ : ℝ) :
    phi4Integrand Q c k l m n
        (boolSign b₁ * α) (boolSign b₂ * β) (boolSign b₃ * γ) (boolSign b₄ * δ)
      = boolSignPow b₁ k * boolSignPow b₂ l * boolSignPow b₃ m * boolSignPow b₄ n *
        (α ^ k * β ^ l * γ ^ m * δ ^ n) *
        Real.exp (-Q α β γ δ +
          c * (boolSign b₁ * boolSign b₂ * boolSign b₃ * boolSign b₄) *
            (α * β * γ * δ)) := by
  have hQ : Q (boolSign b₁ * α) (boolSign b₂ * β) (boolSign b₃ * γ)
      (boolSign b₄ * δ) = Q α β γ δ := by
    cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;>
      simp only [boolSign_true, boolSign_false, one_mul, neg_one_mul,
        hQα, hQβ, hQγ, hQδ]
  unfold phi4Integrand boolSignPow
  rw [hQ, mul_pow, mul_pow, mul_pow, mul_pow]
  have hcross : c * (boolSign b₁ * α * (boolSign b₂ * β) *
      (boolSign b₃ * γ) * (boolSign b₄ * δ))
      = c * (boolSign b₁ * boolSign b₂ * boolSign b₃ * boolSign b₄) *
        (α * β * γ * δ) := by ring
  rw [hcross]
  ring

/-- **Iterated reflection of the four-fold integral** (unconditional): for any
sign pattern `(b₁,b₂,b₃,b₄)`, the four-fold iterated integral of `F` is
unchanged when each variable is multiplied by `boolSign bᵢ`. Each flip is the
measure-preserving reflection `integral_comp_boolSign_mul`, applied at one
nesting level. -/
theorem integral4_comp_boolSign_mul (b₁ b₂ b₃ b₄ : Bool)
    (F : ℝ → ℝ → ℝ → ℝ → ℝ) :
    (∫ α, ∫ β, ∫ γ, ∫ δ, F (boolSign b₁ * α) (boolSign b₂ * β)
        (boolSign b₃ * γ) (boolSign b₄ * δ))
      = ∫ α, ∫ β, ∫ γ, ∫ δ, F α β γ δ := by
  calc
    (∫ α, ∫ β, ∫ γ, ∫ δ, F (boolSign b₁ * α) (boolSign b₂ * β)
        (boolSign b₃ * γ) (boolSign b₄ * δ))
      = ∫ α, ∫ β, ∫ γ, ∫ δ, F α (boolSign b₂ * β)
          (boolSign b₃ * γ) (boolSign b₄ * δ) :=
        integral_comp_boolSign_mul b₁
          (fun α => ∫ β, ∫ γ, ∫ δ, F α (boolSign b₂ * β)
            (boolSign b₃ * γ) (boolSign b₄ * δ))
    _ = ∫ α, ∫ β, ∫ γ, ∫ δ, F α β (boolSign b₃ * γ) (boolSign b₄ * δ) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun α => ?_)
        exact integral_comp_boolSign_mul b₂
          (fun β => ∫ γ, ∫ δ, F α β (boolSign b₃ * γ) (boolSign b₄ * δ))
    _ = ∫ α, ∫ β, ∫ γ, ∫ δ, F α β γ (boolSign b₄ * δ) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun α => ?_)
        refine integral_congr_ae (Filter.Eventually.of_forall fun β => ?_)
        exact integral_comp_boolSign_mul b₃
          (fun γ => ∫ δ, F α β γ (boolSign b₄ * δ))
    _ = ∫ α, ∫ β, ∫ γ, ∫ δ, F α β γ δ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun α => ?_)
        refine integral_congr_ae (Filter.Eventually.of_forall fun β => ?_)
        refine integral_congr_ae (Filter.Eventually.of_forall fun γ => ?_)
        exact integral_comp_boolSign_mul b₄ (fun δ => F α β γ δ)

/-- **Per-pattern reflected form of the four-fold φ⁴ integral** (unconditional):
for any sign pattern, the four-fold integral of the φ⁴ integrand equals the
integral of the sign-transformed integrand (sign character `boolSignᵏˡᵐⁿ`, the
cross term carrying the joint sign `σ`). Combines the reflection invariance
with the reflected-integrand identity; `Q` even in each variable. -/
theorem phi4_integral4_eq_reflected (Q : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hQα : ∀ α β γ δ, Q (-α) β γ δ = Q α β γ δ)
    (hQβ : ∀ α β γ δ, Q α (-β) γ δ = Q α β γ δ)
    (hQγ : ∀ α β γ δ, Q α β (-γ) δ = Q α β γ δ)
    (hQδ : ∀ α β γ δ, Q α β γ (-δ) = Q α β γ δ)
    (c : ℝ) (k l m n : ℕ) (b₁ b₂ b₃ b₄ : Bool) :
    (∫ α, ∫ β, ∫ γ, ∫ δ, phi4Integrand Q c k l m n α β γ δ)
      = ∫ α, ∫ β, ∫ γ, ∫ δ,
          boolSignPow b₁ k * boolSignPow b₂ l * boolSignPow b₃ m *
            boolSignPow b₄ n * (α ^ k * β ^ l * γ ^ m * δ ^ n) *
            Real.exp (-Q α β γ δ +
              c * (boolSign b₁ * boolSign b₂ * boolSign b₃ * boolSign b₄) *
                (α * β * γ * δ)) := by
  rw [← integral4_comp_boolSign_mul b₁ b₂ b₃ b₄ (phi4Integrand Q c k l m n)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun α => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun β => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun γ => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun δ => ?_)
  exact phi4Integrand_boolSign_mul Q hQα hQβ hQγ hQδ c k l m n b₁ b₂ b₃ b₄ α β γ δ

end IsingModel.ContinuousSpin
