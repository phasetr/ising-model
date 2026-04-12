import IsingModel.ContinuousSpin.Measure

/-!
# φ⁴ inequalities

The φ⁴ correlation inequalities from Glimm–Jaffe §4.3, pp. 59–62.
For continuous spins with distribution `dμ = exp(-λξ⁴ - σξ²) dξ`,
these give Lebowitz-type bounds on truncated correlations.

## Main results

* `quartic_identity` — the key algebraic identity for the orthogonal transformation
* `sum_sq_identity`, `inner_product_identity` — orthogonality identities

## References

* Glimm–Jaffe, *Quantum Physics*, §4.3, pp. 59–62.
-/

namespace IsingModel.ContinuousSpin

open Real

/-! ## Single-site orthogonal transformation

The transformation `(ξ, χ, ξ', χ') ↦ (α, β, γ, δ)` is defined by
two stages of averaging with `/2` normalization (not `/√2`).
This is an orthogonal transformation of `ℝ⁴` up to a factor of 2. -/

/-- The `α` variable: `α = (ξ + χ + ξ' + χ') / 2`. -/
noncomputable def phi4Alpha (ξ χ ξ' χ' : ℝ) : ℝ := (ξ + χ + ξ' + χ') / 2

/-- The `β` variable: `β = (ξ + χ - ξ' - χ') / 2`. -/
noncomputable def phi4Beta (ξ χ ξ' χ' : ℝ) : ℝ := (ξ + χ - ξ' - χ') / 2

/-- The `γ` variable: `γ = (ξ - χ + ξ' - χ') / 2`. -/
noncomputable def phi4Gamma (ξ χ ξ' χ' : ℝ) : ℝ := (ξ - χ + ξ' - χ') / 2

/-- The `δ` variable: `δ = (ξ - χ - ξ' + χ') / 2`. -/
noncomputable def phi4Delta (ξ χ ξ' χ' : ℝ) : ℝ := (ξ - χ - ξ' + χ') / 2

/-! ## Algebraic identities -/

/-- The quartic identity for the orthogonal transformation:
`4(ξ⁴ + χ⁴ + ξ'⁴ + χ'⁴) = (α⁴+β⁴+γ⁴+δ⁴) + 6·Σα²β² + 24·αβγδ`.

The `+24αβγδ` term is the ferromagnetic coupling that drives Theorem 4.3.1.
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
  simp only [phi4Alpha, phi4Beta, phi4Gamma, phi4Delta]
  ring

/-- The sum of squares identity (orthogonality):
`ξ² + χ² + ξ'² + χ'² = α² + β² + γ² + δ²`. -/
theorem sum_sq_identity (ξ χ ξ' χ' : ℝ) :
    let α := phi4Alpha ξ χ ξ' χ'
    let β := phi4Beta ξ χ ξ' χ'
    let γ := phi4Gamma ξ χ ξ' χ'
    let δ := phi4Delta ξ χ ξ' χ'
    ξ ^ 2 + χ ^ 2 + ξ' ^ 2 + χ' ^ 2 = α ^ 2 + β ^ 2 + γ ^ 2 + δ ^ 2 := by
  simp only [phi4Alpha, phi4Beta, phi4Gamma, phi4Delta]
  ring

/-- The linear identity: `ξ + χ + ξ' + χ' = 2α` (external field coupling). -/
theorem sum_linear_identity (ξ χ ξ' χ' : ℝ) :
    ξ + χ + ξ' + χ' = 2 * phi4Alpha ξ χ ξ' χ' := by
  simp only [phi4Alpha]; ring

/-- The inner product identity (interaction term preservation):
`ξ₁ξ₂ + χ₁χ₂ + ξ'₁ξ'₂ + χ'₁χ'₂ = α₁α₂ + β₁β₂ + γ₁γ₂ + δ₁δ₂`. -/
theorem inner_product_identity (ξ₁ χ₁ ξ'₁ χ'₁ ξ₂ χ₂ ξ'₂ χ'₂ : ℝ) :
    ξ₁ * ξ₂ + χ₁ * χ₂ + ξ'₁ * ξ'₂ + χ'₁ * χ'₂ =
    phi4Alpha ξ₁ χ₁ ξ'₁ χ'₁ * phi4Alpha ξ₂ χ₂ ξ'₂ χ'₂ +
    phi4Beta ξ₁ χ₁ ξ'₁ χ'₁ * phi4Beta ξ₂ χ₂ ξ'₂ χ'₂ +
    phi4Gamma ξ₁ χ₁ ξ'₁ χ'₁ * phi4Gamma ξ₂ χ₂ ξ'₂ χ'₂ +
    phi4Delta ξ₁ χ₁ ξ'₁ χ'₁ * phi4Delta ξ₂ χ₂ ξ'₂ χ'₂ := by
  simp only [phi4Alpha, phi4Beta, phi4Gamma, phi4Delta]
  ring

/-! ## Ferromagnetic decomposition

The quartic identity shows that `P(ξ)+P(χ)+P(ξ')+P(χ')` decomposes as
an even function `Q(α,β,γ,δ)` minus a ferromagnetic term `c·αβγδ`:

  `λ(ξ⁴+χ⁴+ξ'⁴+χ'⁴) + σ(ξ²+χ²+ξ'²+χ'²)`
  `= [λ/4·(Σα⁴ + 6Σα²β²) + σ(Σα²)] - [-6λ·αβγδ]`
  `= Q(α,β,γ,δ) - c·αβγδ`

where `Q` is even in each variable and `c = -6λ > 0` when `λ > 0`.
This means `exp(c·αβγδ)` is the ferromagnetic factor.

The measure-theoretic proof of Theorem 4.3.1 (that `⟨α^A β^B γ^C δ^D⟩ ≥ 0`)
uses the power series expansion of `exp(c·αβγδ)` and the evenness of `Q`
to show that all contributions are non-negative.

This part requires integrability estimates and is deferred. -/

end IsingModel.ContinuousSpin
