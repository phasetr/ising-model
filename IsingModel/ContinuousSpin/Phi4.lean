import IsingModel.ContinuousSpin.Measure

/-!
# φ⁴ inequalities

The φ⁴ correlation inequalities from Glimm–Jaffe §4.3, pp. 59–62.
For continuous spins with distribution `dμ = exp(-λξ⁴ - σξ²) dξ`,
these give Lebowitz-type bounds on truncated correlations.

## Strategy

The proof proceeds at a single site first:
1. Define the orthogonal transformation `(ξ, χ, ξ', χ') ↦ (α, β, γ, δ)`
2. Prove the quartic identity:
   `ξ⁴ + χ⁴ + ξ'⁴ + χ'⁴ = 4(α⁴+β⁴+γ⁴+δ⁴) + 12(α²β²+...) - 24αβγδ`
3. Conclude that the four-fold measure is ferromagnetic in `(α, β, γ, δ)`
4. Apply GKS-I type argument to get Theorem 4.3.1
5. Derive Corollaries 4.3.2–4.3.4

Reference: Glimm–Jaffe, *Quantum Physics*, §4.3, pp. 59–62.
-/

namespace IsingModel.ContinuousSpin

open Real

/-! ## Single-site orthogonal transformation

The transformation `(ξ, χ, ξ', χ') ↦ (α, β, γ, δ)` is defined by
two stages of averaging: first `(ξ,χ) ↦ (t,q)` and `(ξ',χ') ↦ (t',q')`,
then `(t,t') ↦ (α,β)` and `(q,q') ↦ (γ,δ)`. -/

/-- The `(α, β, γ, δ)` variables as functions of `(ξ, χ, ξ', χ')`.
This is an orthogonal transformation of `ℝ⁴`. -/
noncomputable def phi4Alpha (ξ χ ξ' χ' : ℝ) : ℝ := (ξ + χ + ξ' + χ') / 2
noncomputable def phi4Beta (ξ χ ξ' χ' : ℝ) : ℝ := (ξ + χ - ξ' - χ') / 2
noncomputable def phi4Gamma (ξ χ ξ' χ' : ℝ) : ℝ := (ξ - χ + ξ' - χ') / 2
noncomputable def phi4Delta (ξ χ ξ' χ' : ℝ) : ℝ := (ξ - χ - ξ' + χ') / 2

/-! ## Quartic identity -/

/-- The quartic identity for the orthogonal transformation:
`ξ⁴ + χ⁴ + ξ'⁴ + χ'⁴ = 4(α⁴+β⁴+γ⁴+δ⁴) + 12(α²β²+α²γ²+α²δ²+β²γ²+β²δ²+γ²δ²) - 24αβγδ`.

Equivalently: `2(ξ⁴+χ⁴+ξ'⁴+χ'⁴) = (α+β+γ-δ)⁴ + (α+β-γ+δ)⁴ + (α-β+γ+δ)⁴ + (-α+β+γ+δ)⁴`.

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

/-- The sum of squares identity:
`ξ² + χ² + ξ'² + χ'² = α² + β² + γ² + δ²`.
This follows from the orthogonality of the transformation. -/
theorem sum_sq_identity (ξ χ ξ' χ' : ℝ) :
    let α := phi4Alpha ξ χ ξ' χ'
    let β := phi4Beta ξ χ ξ' χ'
    let γ := phi4Gamma ξ χ ξ' χ'
    let δ := phi4Delta ξ χ ξ' χ'
    ξ ^ 2 + χ ^ 2 + ξ' ^ 2 + χ' ^ 2 = α ^ 2 + β ^ 2 + γ ^ 2 + δ ^ 2 := by
  simp only [phi4Alpha, phi4Beta, phi4Gamma, phi4Delta]
  ring

/-- The linear identity: `ξ + χ + ξ' + χ' = 2α`.
This is used for the external field coupling. -/
theorem sum_linear_identity (ξ χ ξ' χ' : ℝ) :
    ξ + χ + ξ' + χ' = 2 * phi4Alpha ξ χ ξ' χ' := by
  simp only [phi4Alpha]; ring

/-- The inner product identity:
`ξ₁ξ₂ + χ₁χ₂ + ξ'₁ξ'₂ + χ'₁χ'₂ = α₁α₂ + β₁β₂ + γ₁γ₂ + δ₁δ₂`.
This preserves the interaction term under the orthogonal transformation. -/
theorem inner_product_identity (ξ₁ χ₁ ξ'₁ χ'₁ ξ₂ χ₂ ξ'₂ χ'₂ : ℝ) :
    ξ₁ * ξ₂ + χ₁ * χ₂ + ξ'₁ * ξ'₂ + χ'₁ * χ'₂ =
    phi4Alpha ξ₁ χ₁ ξ'₁ χ'₁ * phi4Alpha ξ₂ χ₂ ξ'₂ χ'₂ +
    phi4Beta ξ₁ χ₁ ξ'₁ χ'₁ * phi4Beta ξ₂ χ₂ ξ'₂ χ'₂ +
    phi4Gamma ξ₁ χ₁ ξ'₁ χ'₁ * phi4Gamma ξ₂ χ₂ ξ'₂ χ'₂ +
    phi4Delta ξ₁ χ₁ ξ'₁ χ'₁ * phi4Delta ξ₂ χ₂ ξ'₂ χ'₂ := by
  simp only [phi4Alpha, phi4Beta, phi4Gamma, phi4Delta]
  ring

end IsingModel.ContinuousSpin
