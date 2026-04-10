import IsingModel.GibbsMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# GKS (Griffiths) inequalities

The first Griffiths inequality for the ferromagnetic Ising model:
for `J ≥ 0`, `h ≥ 0`, `β > 0`, the correlation `⟨σ_A⟩ ≥ 0`.

Reference: Glimm–Jaffe, *Quantum Physics*, Theorem 4.1.1.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Numerator of the Gibbs expectation -/

/-- The unnormalized expectation (numerator): `∑_σ F(σ) · exp(-β H(σ))`. -/
noncomputable def numerator (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (F : Config ι → ℝ) : ℝ :=
  ∑ σ : Config ι, F σ * boltzmannWeight G p σ

/-- The Gibbs expectation equals `Z⁻¹ · numerator`. -/
theorem gibbsExpectation_eq_div (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (F : Config ι → ℝ) :
    gibbsExpectation G p F = (partitionFunction G p)⁻¹ * numerator G p F := by
  unfold gibbsExpectation numerator
  rfl

/-- If the numerator is non-negative, then the Gibbs expectation is non-negative. -/
theorem gibbsExpectation_nonneg_of_numerator_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (F : Config ι → ℝ)
    (hnum : 0 ≤ numerator G p F) :
    0 ≤ gibbsExpectation G p F := by
  rw [gibbsExpectation_eq_div]
  exact mul_nonneg (inv_nonneg.mpr (le_of_lt (partitionFunction_pos G p))) hnum

/-! ## Auxiliary: exp decomposition for ±1 spins -/

/-- For `s ∈ {+1, -1}`, `exp(α * s) = cosh(α) + s * sinh(α)`. -/
theorem exp_sign_decomp (α : ℝ) (s : Spin) :
    Real.exp (α * ↑s.toSign) = Real.cosh α + ↑s.toSign * Real.sinh α := by
  cases s with
  | up => simp [Spin.toSign, Real.cosh_add_sinh]
  | down =>
    simp only [Spin.toSign, Int.cast_neg, Int.cast_one, mul_neg, mul_one, neg_mul, one_mul]
    linarith [Real.cosh_add_sinh α, Real.sinh_add_cosh α,
              Real.cosh_add_sinh (-α), Real.sinh_add_cosh (-α),
              Real.cosh_neg α, Real.sinh_neg α]

/-! ## GKS-I: core non-negativity -/

/-! ## Sum over configurations -/

/-- The sum of `toSign(s)` over all spins is zero: `1 + (-1) = 0`. -/
theorem sum_spin_toSign : ∑ s : Spin, (↑s.toSign : ℝ) = 0 := by
  have : Fintype.elems (α := Spin) = {.up, .down} := by decide
  simp [Finset.sum, Finset.univ, this, Spin.toSign]

/-- The sum of `spinProduct A` over all configurations is zero when `A` is nonempty.
This is because each site `i ∈ A` contributes a factor `∑_{s=±1} s = 0`. -/
theorem sum_config_spinProduct_eq_zero (A : Finset ι) (hA : A.Nonempty) :
    ∑ σ : Config ι, spinProduct A σ = 0 := by
  sorry

/-- The sum of `spinProduct ∅` over all configurations is `2^|ι|`. -/
theorem sum_config_spinProduct_empty :
    ∑ σ : Config ι, spinProduct ∅ σ = (Fintype.card (Config ι) : ℝ) := by
  simp [spinProduct_empty]

/-- The numerator of `⟨σ_A⟩` is non-negative for ferromagnetic parameters.

This is the core of GKS-I. The proof uses the cosh/sinh decomposition of
the Boltzmann weight and the fact that sums over `{±1}` configurations
vanish for odd powers and are positive for even powers.

TODO: complete the proof (currently `sorry`).
-/
theorem gks_numerator_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset ι) :
    0 ≤ numerator G p (spinProduct A) := by
  sorry

/-! ## GKS-I: main theorem -/

/-- **First Griffiths inequality (GKS-I)**: For a ferromagnetic Ising model
(`J ≥ 0`, `h ≥ 0`, `β > 0`), all correlation functions are non-negative:
`⟨σ_A⟩ ≥ 0` for any subset `A`. -/
theorem gks_first (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset ι) :
    0 ≤ correlation G p A := by
  unfold correlation
  exact gibbsExpectation_nonneg_of_numerator_nonneg G p _ (gks_numerator_nonneg G p hf A)

end IsingModel
