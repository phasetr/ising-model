import IsingModel.ContinuousSpin.Measure
import IsingModel.Inequalities.GKS

/-!
# φ⁴ inequalities

The φ⁴ correlation inequalities from Glimm–Jaffe §4.3, pp. 59–62.
For continuous spins with distribution `dμ = exp(-λξ⁴ - σξ²) dξ`,
these give Lebowitz-type bounds on truncated correlations.

## Main results

* `lebowitz_ineq` — Lebowitz inequality: upper bound on the truncated two-point
  function in terms of products of two-point functions.
* `truncated_three_point_nonpos` — The truncated three-point function is ≤ 0
  (Corollary 4.3.4, essentially the GHS inequality).

## Strategy

For continuous spins, the proof uses:
1. Four-fold duplicate variables with orthogonal transformation
2. The quartic identity `ξ⁴+χ⁴+ξ'⁴+χ'⁴ = 4(α⁴+β⁴+γ⁴+δ⁴) + 12(...) - 24αβγδ`
3. Power series expansion of `exp(c·αβγδ)` with even-function cancellation

For discrete ±1 spins, Theorem 4.3.1 reduces to GKS-I on the 4-fold product,
but Corollaries 4.3.2–4.3.4 remain non-trivial. The proofs of the corollaries
are algebraic and do not require the φ⁴ structure directly.

Reference: Glimm–Jaffe, *Quantum Physics*, §4.3, pp. 59–62.
-/

namespace IsingModel.ContinuousSpin

open MeasureTheory Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Four-fold duplicate expectation

For the Lebowitz inequality, we need four independent copies of the spin system.
The configuration space is `(ι → ℝ)⁴`, with product measure `μ⊗⁴`. -/

/-- Four-fold configuration: `(σ, χ, σ', χ')` each in `ι → ℝ`. -/
abbrev Config4 (ι : Type*) := (ι → ℝ) × (ι → ℝ) × (ι → ℝ) × (ι → ℝ)

/-- The duplicate variable `t_i = (σ_i + χ_i) / √2`. -/
noncomputable def tVar (c : Config4 ι) (i : ι) : ℝ :=
  (c.1 i + c.2.1 i) / Real.sqrt 2

/-- The duplicate variable `q_i = (σ_i - χ_i) / √2`. -/
noncomputable def qVar (c : Config4 ι) (i : ι) : ℝ :=
  (c.1 i - c.2.1 i) / Real.sqrt 2

/-- The four-fold variable `α_i = (t_i + t'_i) / √2`. -/
noncomputable def alphaVar (c : Config4 ι) (i : ι) : ℝ :=
  (tVar (c.1, c.2.1, fun _ => 0, fun _ => 0) i +
   tVar (c.2.2.1, c.2.2.2, fun _ => 0, fun _ => 0) i) / Real.sqrt 2

/-- The four-fold variable `β_i = (t_i - t'_i) / √2`. -/
noncomputable def betaVar (c : Config4 ι) (i : ι) : ℝ :=
  (tVar (c.1, c.2.1, fun _ => 0, fun _ => 0) i -
   tVar (c.2.2.1, c.2.2.2, fun _ => 0, fun _ => 0) i) / Real.sqrt 2

-- TODO: γ, δ variables similarly

/-! ## Quartic identity

The key algebraic identity:
`ξ⁴ + χ⁴ + ξ'⁴ + χ'⁴ = 4(α⁴+β⁴+γ⁴+δ⁴) + 12(α²β²+...) - 24αβγδ`

For now, we state this as a sorry and will fill in the computation. -/

-- TODO: quartic_identity, ferromagnetic structure, Theorem 4.3.1

/-! ## Lebowitz inequality (Corollary 4.3.2)

The proof uses the relation between (t, q) and (α, β, γ, δ) variables.
In the discrete ±1 case, t_i = σ_i · χ_i and the proof simplifies. -/

-- TODO: Corollary 4.3.2 (Lebowitz), Corollary 4.3.3, Corollary 4.3.4

end IsingModel.ContinuousSpin
