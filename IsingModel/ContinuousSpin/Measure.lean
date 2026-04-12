import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Continuous spin measures

Single-spin measures of the form `dμ = exp(-P(ξ)) dξ` on `ℝ`,
and their product measures on `ι → ℝ` for finite `ι`.

The main application is the φ⁴ single-spin distribution
`dμ = exp(-λ ξ⁴ - σ ξ²) dξ` with `λ > 0` (or `λ = 0, σ > 0`).

Reference: Glimm–Jaffe, §4.3, pp. 59–62.
-/

namespace IsingModel.ContinuousSpin

open MeasureTheory Measure Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Single-spin measure -/

/-- A single-spin measure on `ℝ` with density `exp(-P(ξ))` w.r.t. Lebesgue. -/
noncomputable def singleSpinMeasure (P : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun ξ => .ofReal (Real.exp (-P ξ)))

/-- The product measure on `ι → ℝ` for independent spins. -/
noncomputable def productSpinMeasure (P : ι → ℝ → ℝ) : Measure (ι → ℝ) :=
  Measure.pi (fun i => singleSpinMeasure (P i))

/-! ## Monomial character -/

/-- The monomial character `χ(A, ξ) = ∏_{i ∈ A} ξ_i`. -/
def monomialChar (A : Finset ι) (ξ : ι → ℝ) : ℝ :=
  ∏ i ∈ A, ξ i

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem monomialChar_empty (ξ : ι → ℝ) : monomialChar (∅ : Finset ι) ξ = 1 :=
  Finset.prod_empty

omit [Fintype ι] [DecidableEq ι] in
theorem monomialChar_singleton (i : ι) (ξ : ι → ℝ) :
    monomialChar {i} ξ = ξ i := by
  simp [monomialChar]

omit [Fintype ι] in
theorem monomialChar_mul (A B : Finset ι) (hAB : Disjoint A B) (ξ : ι → ℝ) :
    monomialChar (A ∪ B) ξ = monomialChar A ξ * monomialChar B ξ :=
  Finset.prod_union hAB

/-! ## Non-negative correlations (abstract) -/

/-- Abstract non-negative correlations property for a weight function `f`
w.r.t. a measure `μ` and character `χ`:
`∀ A, 0 ≤ ∫ ω, χ(A, ω) · f(ω) dμ(ω)`. -/
def HasNonnegCorrelationsM {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (χ : Finset ι → Ω → ℝ) (f : Ω → ℝ) : Prop :=
  ∀ A : Finset ι, 0 ≤ ∫ ω, χ A ω * f ω ∂μ

end IsingModel.ContinuousSpin
