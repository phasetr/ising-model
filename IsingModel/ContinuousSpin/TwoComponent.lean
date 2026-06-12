import IsingModel.ContinuousSpin.Phi4AllOdd

/-!
# Two-component (planar rotator) spins: the single-site potential algebra

The algebraic foundation of GJ §4.7 (Theorem 4.7.1, p. 70): the two-component
single-spin potential `P(ξ) = A·(ξ·ξ)² + σ·(ξ·ξ)` (with `ξ = (t, q) ∈ ℝ²`),
doubled across a duplicate spin and written in the rotated variables
`(α,β,γ,δ)` of (4.3.2), is `even − 4A·αβγδ`: even in each rotated variable
plus the single ferromagnetic cross term `−4A·αβγδ` (`A ≥ 0`). This is
exactly the `Q` even, `c = 4A ≥ 0` form fed to
`phi4_single_site_nonneg` (Issue #3913), so the single-site positivity at the
core of Theorem 4.7.1 is supplied by the existing φ⁴ machinery.

This file is part of GJ §4.7 (Issue #3918).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.7, Theorem 4.7.1, p. 70
-/

namespace IsingModel.ContinuousSpin

open Real

/-- The two-component single-spin potential `P(ξ) = A·(t²+q²)² + σ·(t²+q²)`
for `ξ = (t, q)`. -/
noncomputable def twoCompPotential (A σ t q : ℝ) : ℝ :=
  A * (t ^ 2 + q ^ 2) ^ 2 + σ * (t ^ 2 + q ^ 2)

/-- The `δ`-variable of the §4.7 rotation: the negative of `phi4Delta`, chosen
so the ferromagnetic cross term enters the doubled potential as `−4A·αβγδ`
(equivalently, so the single-site weight has `+4A·αβγδ` with `4A ≥ 0`, the
form fed to `phi4_single_site_nonneg`). -/
noncomputable def twoCompDelta (t q t' q' : ℝ) : ℝ := -phi4Delta t q t' q'

/-- The even part of the doubled two-component potential in the rotated
variables `(α,β,γ,δ)`: even in each variable, computed as the quartic
remainder of `(t²+q²)² + (t'²+q'²)²` after extracting the `αβγδ` cross term,
plus the quadratic `σ`-term. -/
noncomputable def twoCompEvenPart (A σ α β γ δ : ℝ) : ℝ :=
  A * ((1 / 2) * (α ^ 4 + β ^ 4 + γ ^ 4 + δ ^ 4) +
        3 * (α ^ 2 * β ^ 2 + γ ^ 2 * δ ^ 2) +
        (α ^ 2 * γ ^ 2 + α ^ 2 * δ ^ 2 + β ^ 2 * γ ^ 2 + β ^ 2 * δ ^ 2)) +
    σ * (α ^ 2 + β ^ 2 + γ ^ 2 + δ ^ 2)

/-- **The doubled two-component potential identity** (the §4.7 analogue of
(4.3.5)): `P(t,q) + P(t',q') = twoCompEvenPart − 4A·αβγδ`, with `(α,β,γ,δ)`
the (4.3.2) rotation of `(t, q, t', q')` (the `δ` slot being `twoCompDelta`).
The cross term is ferromagnetic for `A ≥ 0`. -/
theorem twoCompPotential_double_eq (A σ t q t' q' : ℝ) :
    twoCompPotential A σ t q + twoCompPotential A σ t' q'
      = twoCompEvenPart A σ (phi4Alpha t q t' q') (phi4Beta t q t' q')
          (phi4Gamma t q t' q') (twoCompDelta t q t' q')
        - 4 * A * (phi4Alpha t q t' q' * phi4Beta t q t' q' *
            phi4Gamma t q t' q' * twoCompDelta t q t' q') := by
  simp only [twoCompPotential, twoCompEvenPart, twoCompDelta, phi4Alpha,
    phi4Beta, phi4Gamma, phi4Delta]
  ring

/-- The even part is even in `α`. -/
theorem twoCompEvenPart_even_alpha (A σ α β γ δ : ℝ) :
    twoCompEvenPart A σ (-α) β γ δ = twoCompEvenPart A σ α β γ δ := by
  simp only [twoCompEvenPart]; ring

/-- The even part is even in `β`. -/
theorem twoCompEvenPart_even_beta (A σ α β γ δ : ℝ) :
    twoCompEvenPart A σ α (-β) γ δ = twoCompEvenPart A σ α β γ δ := by
  simp only [twoCompEvenPart]; ring

/-- The even part is even in `γ`. -/
theorem twoCompEvenPart_even_gamma (A σ α β γ δ : ℝ) :
    twoCompEvenPart A σ α β (-γ) δ = twoCompEvenPart A σ α β γ δ := by
  simp only [twoCompEvenPart]; ring

/-- The even part is even in `δ`. -/
theorem twoCompEvenPart_even_delta (A σ α β γ δ : ℝ) :
    twoCompEvenPart A σ α β γ (-δ) = twoCompEvenPart A σ α β γ δ := by
  simp only [twoCompEvenPart]; ring

/-- **Single-site positivity for two-component spins** (the §4.7 core,
reducing to `phi4_single_site_nonneg`): for `A ≥ 0` the rotated single-site
moment with the even potential `twoCompEvenPart` and the ferromagnetic cross
term `+4A·αβγδ` is non-negative. This is the input that drives Theorem 4.7.1,
exactly as `phi4_single_site_nonneg` drives Theorem 4.3.1. -/
theorem twoComp_single_site_nonneg (A σ : ℝ) (hA : 0 ≤ A) (k l m n : ℕ) :
    0 ≤ ∫ α, ∫ β, ∫ γ, ∫ δ,
      α ^ k * β ^ l * γ ^ m * δ ^ n *
      Real.exp (-twoCompEvenPart A σ α β γ δ + 4 * A * (α * β * γ * δ)) :=
  phi4_single_site_nonneg (twoCompEvenPart A σ)
    (twoCompEvenPart_even_alpha A σ) (twoCompEvenPart_even_beta A σ)
    (twoCompEvenPart_even_gamma A σ) (twoCompEvenPart_even_delta A σ)
    (4 * A) (by positivity) k l m n

end IsingModel.ContinuousSpin
