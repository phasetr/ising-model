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

set_option linter.unusedFintypeInType false in
/-- Multiplying spin products corresponds to symmetric difference of index sets.
This follows from `s(σ_i)² = 1`: shared indices cancel.

The proof converts each `spinProduct S σ` to `∏ i ∈ univ, if i ∈ S then s_i else 1`,
multiplies pointwise using `prod_mul_distrib`, and checks each factor by cases on
membership in `A` and `C`, using `s_i² = 1`. -/
theorem spinProduct_mul (A C : Finset ι) (σ : Config ι) :
    spinProduct A σ * spinProduct C σ = spinProduct (symmDiff A C) σ := by
  let s : ι → ℝ := fun i => ↑(σ i).toSign
  have hsq : ∀ i, s i * s i = 1 :=
    fun i => by simp [s, ← sq, ← Int.cast_pow, Spin.toSign_sq]
  -- Rewrite spinProduct as ∏ over univ with indicator
  have hprod : ∀ S : Finset ι, spinProduct S σ =
      ∏ i ∈ Finset.univ, if i ∈ S then s i else 1 := by
    intro S
    simp only [spinProduct, s]
    conv_lhs => rw [show S = Finset.univ.filter (· ∈ S) from by ext; simp]
    rw [Finset.prod_filter]
  rw [hprod A, hprod C, ← Finset.prod_mul_distrib, hprod]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Finset.mem_symmDiff]
  by_cases hiA : i ∈ A <;> by_cases hiC : i ∈ C <;> simp_all [hsq i]

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
  intro S
  -- Expand: ∑ σ^S · f · (a + b·σ^C) = a · ∑ σ^S·f + b · ∑ σ^{SΔC}·f
  have key : ∑ σ : Config ι, spinProduct S σ * (f σ * (a + b * spinProduct C σ)) =
      a * ∑ σ : Config ι, spinProduct S σ * f σ +
      b * ∑ σ : Config ι, spinProduct (symmDiff S C) σ * f σ := by
    have : ∀ σ : Config ι, spinProduct S σ * (f σ * (a + b * spinProduct C σ)) =
        a * (spinProduct S σ * f σ) + b * (spinProduct S σ * spinProduct C σ * f σ) :=
      fun σ => by ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    congr 1
    simp_rw [spinProduct_mul S C]
  rw [key]
  exact add_nonneg (mul_nonneg ha (hf S)) (mul_nonneg hb (hf (symmDiff S C)))

/-- The Boltzmann weight has non-negative correlations for ferromagnetic parameters.

This is the key technical lemma for GKS-I. The proof factors `exp(-βH)` as
a product of terms `(cosh(βJ) + sinh(βJ) · σ^edge)` and
`(cosh(βh) + sinh(βh) · σ^site)`, then applies `hasNonnegCorrelations_mul`
inductively starting from `hasNonnegCorrelations_one`.

TODO: prove without sorry. Requires:
1. `exp(∑ f) = ∏ exp(f i)` (mathlib: `Real.exp_sum`)
2. Decomposition of `hamiltonian` into edge and site sums
3. `exp_sign_decomp` for each factor
4. `edgeSpin σ e ∈ {-1, 1}` and `Spin.sign (σ i) ∈ {-1, 1}`
5. Inductive application of `hasNonnegCorrelations_mul` over edges then sites
-/
theorem boltzmannWeight_hasNonnegCorrelations (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    HasNonnegCorrelations (boltzmannWeight G p) := by
  sorry

/-- The numerator of `⟨σ_A⟩` is non-negative for ferromagnetic parameters. -/
theorem gks_numerator_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset ι) :
    0 ≤ numerator G p (spinProduct A) :=
  boltzmannWeight_hasNonnegCorrelations G p hf A

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
