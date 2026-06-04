import IsingModel.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Generic linearity of a normalised weighted expectation

Every flavour of Gibbs expectation in the FKG/Holley development has the shape

  `⟨F⟩ = Z⁻¹ · ∑_σ F(σ) · w(σ)`

for a partition value `Z` (the total weight `∑_σ w(σ)`) and a nonnegative weight
`w` (the Boltzmann weight, the inhomogeneous Boltzmann weight, or the
boundary-condition Boltzmann weight).  The constant / additivity / scalar
linearity of such a normalised weighted average is purely algebraic and does not
depend on which weight is used, so it is proved **once** here and reused by the
concrete `gibbsExpectation_*`, `gibbsExpectationJ_*`, and `gibbsExpectationBC_*`
wrappers.

* `weightedExpectation_const` — `Z⁻¹ ∑ c·w = c` (needs `∑ w = Z ≠ 0`).
* `weightedExpectation_add` — `Z⁻¹ ∑ (F+H)·w = Z⁻¹ ∑ F·w + Z⁻¹ ∑ H·w`.
* `weightedExpectation_const_mul` — `Z⁻¹ ∑ (c·F)·w = c·(Z⁻¹ ∑ F·w)`.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Constant rule for a normalised weighted expectation**: `Z⁻¹ ∑_σ c·w(σ) = c`,
given that the total weight `∑_σ w(σ)` equals `Z` and `Z ≠ 0`. -/
theorem weightedExpectation_const (Z : ℝ) (w : Config ι → ℝ)
    (hZ_eq : (∑ σ : Config ι, w σ) = Z) (hZ : Z ≠ 0) (c : ℝ) :
    Z⁻¹ * ∑ σ : Config ι, c * w σ = c := by
  rw [← Finset.mul_sum, hZ_eq, ← mul_assoc, mul_comm _ c, mul_assoc, inv_mul_cancel₀ hZ, mul_one]

/-- **Additivity for a normalised weighted expectation**:
`Z⁻¹ ∑_σ (F(σ)+H(σ))·w(σ) = Z⁻¹ ∑_σ F(σ)·w(σ) + Z⁻¹ ∑_σ H(σ)·w(σ)`. -/
theorem weightedExpectation_add (Z : ℝ) (w F H : Config ι → ℝ) :
    Z⁻¹ * ∑ σ : Config ι, (F σ + H σ) * w σ
      = Z⁻¹ * ∑ σ : Config ι, F σ * w σ + Z⁻¹ * ∑ σ : Config ι, H σ * w σ := by
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  ring

/-- **Scalar homogeneity for a normalised weighted expectation**:
`Z⁻¹ ∑_σ (c·F(σ))·w(σ) = c·(Z⁻¹ ∑_σ F(σ)·w(σ))`. -/
theorem weightedExpectation_const_mul (Z : ℝ) (w : Config ι → ℝ) (c : ℝ) (F : Config ι → ℝ) :
    Z⁻¹ * ∑ σ : Config ι, (c * F σ) * w σ
      = c * (Z⁻¹ * ∑ σ : Config ι, F σ * w σ) := by
  rw [show (∑ σ : Config ι, (c * F σ) * w σ) = c * ∑ σ : Config ι, F σ * w σ from by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring]
  ring

end IsingModel
