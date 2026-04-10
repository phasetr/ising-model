import IsingModel.GibbsMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Finset.SymmDiff

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

/-! ## Sum over configurations -/

/-- The sum of `toSign(s)` over all spins is zero: `1 + (-1) = 0`. -/
theorem sum_spin_toSign : ∑ s : Spin, (↑s.toSign : ℝ) = 0 := by
  have : Fintype.elems (α := Spin) = {.up, .down} := by decide
  simp [Finset.sum, Finset.univ, this, Spin.toSign]

/-- Flip a configuration at a single site `j`. -/
def Config.flipAt {ι : Type*} [DecidableEq ι] (j : ι) (σ : Config ι) : Config ι :=
  Function.update σ j (σ j).flip

/-- `flipAt j` is an involution. -/
@[simp]
theorem Config.flipAt_flipAt {ι : Type*} [DecidableEq ι] (j : ι) (σ : Config ι) :
    (σ.flipAt j).flipAt j = σ := by
  ext i
  simp [Config.flipAt, Function.update]
  split <;> simp_all

/-- A flipped spin is different from the original. -/
theorem Spin.flip_ne (s : Spin) : s.flip ≠ s := by
  cases s <;> simp [Spin.flip]

omit [Fintype ι] in
/-- Flipping at any site produces a different configuration. -/
theorem Config.flipAt_ne (j : ι) (σ : Config ι) : σ.flipAt j ≠ σ := by
  intro h
  have h1 := congr_fun h j
  simp only [Config.flipAt, Function.update_self] at h1
  exact absurd h1 (Spin.flip_ne (σ j))

omit [Fintype ι] in
/-- Flipping at `j ∈ A` negates the spin product.
The factor at `j` changes sign; all other factors are unchanged. -/
theorem spinProduct_flipAt_neg (A : Finset ι) (j : ι) (hj : j ∈ A)
    (σ : Config ι) :
    spinProduct A (σ.flipAt j) = -spinProduct A σ := by
  unfold spinProduct
  rw [← Finset.mul_prod_erase _ _ hj, ← Finset.mul_prod_erase _ _ hj]
  have hj_flip : (↑((σ.flipAt j j).toSign) : ℝ) = -↑(σ j).toSign := by
    simp [Config.flipAt, Function.update_self, Spin.toSign_flip]
  have hrest : ∀ i ∈ A.erase j, (↑((σ.flipAt j i).toSign) : ℝ) = ↑(σ i).toSign := by
    intro i hi
    have hne : i ≠ j := Finset.ne_of_mem_erase hi
    simp [Config.flipAt, Function.update_of_ne hne]
  rw [hj_flip, Finset.prod_congr rfl hrest]
  ring

/-- The sum of `spinProduct A` over all configurations is zero when `A` is nonempty.
Uses the involution `flipAt j` for some `j ∈ A`: each pair `(σ, flipAt j σ)`
contributes `spinProduct A σ + spinProduct A (flipAt j σ) = 0`. -/
theorem sum_config_spinProduct_eq_zero (A : Finset ι) (hA : A.Nonempty) :
    ∑ σ : Config ι, spinProduct A σ = 0 := by
  obtain ⟨j, hj⟩ := hA
  apply Finset.sum_ninvolution (Config.flipAt j)
  · intro σ
    rw [spinProduct_flipAt_neg A j hj σ]
    ring
  · intro σ _
    exact fun h => Config.flipAt_ne j σ h
  · intro _
    exact Finset.mem_univ _
  · intro σ
    exact Config.flipAt_flipAt j σ

/-- The sum of `spinProduct ∅` over all configurations is `2^|ι|`. -/
theorem sum_config_spinProduct_empty :
    ∑ σ : Config ι, spinProduct ∅ σ = (Fintype.card (Config ι) : ℝ) := by
  simp [spinProduct_empty]

/-! ## Spin product multiplication (Fourier structure) -/

omit [Fintype ι] in
/-- Multiplying spin products corresponds to symmetric difference of index sets.
This follows from `s(σ_i)² = 1`: shared indices cancel.

TODO: prove without sorry. The proof requires splitting products over
`A \ C`, `A ∩ C`, `C \ A` and using `s(σ_i)² = 1` on the intersection. -/
theorem spinProduct_mul (A C : Finset ι) (σ : Config ι) :
    spinProduct A σ * spinProduct C σ = spinProduct (symmDiff A C) σ := by
  sorry

/-! ## Preservation of non-negative correlations -/

/-- A function `f` on configurations has **non-negative correlations** if
`∑_σ σ^S · f(σ) ≥ 0` for every subset `S`. -/
def HasNonnegCorrelations (f : Config ι → ℝ) : Prop :=
  ∀ S : Finset ι, 0 ≤ ∑ σ : Config ι, spinProduct S σ * f σ

/-- The constant function `1` has non-negative correlations.
For `S = ∅`, the sum is `2^|ι|`. For `S ≠ ∅`, it is `0`. -/
theorem hasNonnegCorrelations_one : HasNonnegCorrelations (ι := ι) (fun _ => 1) := by
  intro S
  simp only [mul_one]
  by_cases hS : S.Nonempty
  · rw [sum_config_spinProduct_eq_zero S hS]
  · simp only [not_nonempty_iff_eq_empty] at hS
    subst hS
    exact Finset.sum_nonneg fun _ _ => by norm_num

/-- If `f` has non-negative correlations, then so does `f · (a + b · σ^C)`
when `a, b ≥ 0`. This is the key inductive step for GKS-I.

The proof uses: `∑_σ σ^S f(σ)(a + b σ^C) = a ∑_σ σ^S f(σ) + b ∑_σ σ^{S Δ C} f(σ)`,
where both terms are non-negative by hypothesis.

TODO: prove without sorry. Requires spinProduct_mul and sum rearrangement. -/
theorem hasNonnegCorrelations_mul {f : Config ι → ℝ}
    (hf : HasNonnegCorrelations f)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (C : Finset ι) :
    HasNonnegCorrelations fun σ => f σ * (a + b * spinProduct C σ) := by
  sorry

/-- The numerator of `⟨σ_A⟩` is non-negative for ferromagnetic parameters.

Proof strategy: factor `exp(-βH)` using `exp_sign_decomp` into a product
of terms `(cosh + sinh · σ^edge)` and `(cosh + sinh · σ^site)`, then
apply `hasNonnegCorrelations_mul` inductively starting from
`hasNonnegCorrelations_one`.

TODO: prove without sorry. Requires factoring exp(-βH) and applying
the preservation lemma inductively over edges and sites. -/
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
