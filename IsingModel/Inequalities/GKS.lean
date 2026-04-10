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

set_option linter.unusedDecidableInType false in
/-- Multiplying a function with HNC by a product of `(a + b · σ^C)` factors preserves HNC. -/
theorem hasNonnegCorrelations_mul_prod {α : Type*} [DecidableEq α]
    (S : Finset α) {f : Config ι → ℝ} (hf : HasNonnegCorrelations f)
    (g : α → Config ι → ℝ)
    (hg : ∀ a ∈ S, ∃ c d : ℝ, ∃ C : Finset ι, 0 ≤ c ∧ 0 ≤ d ∧
      ∀ σ, g a σ = c + d * spinProduct C σ) :
    HasNonnegCorrelations fun σ => f σ * ∏ a ∈ S, g a σ := by
  induction S using Finset.induction with
  | empty => simpa using hf
  | @insert x S' hx ih =>
    rw [show (fun σ => f σ * ∏ a ∈ insert x S', g a σ) =
        fun σ => (f σ * ∏ a ∈ S', g a σ) * g x σ from by
      ext σ; rw [Finset.prod_insert hx]; ring]
    obtain ⟨c, d, C, hc, hd, hg_eq⟩ := hg x (Finset.mem_insert_self x S')
    simp_rw [hg_eq]
    exact hasNonnegCorrelations_mul
      (ih fun a ha' => hg a (Finset.mem_insert_of_mem ha')) hc hd C

set_option linter.unusedDecidableInType false in
/-- A product of `(a + b · σ^C)` factors over a finset has non-negative correlations,
provided each `a, b ≥ 0`. Proved by induction on the finset, applying
`hasNonnegCorrelations_mul` at each step. -/
theorem hasNonnegCorrelations_finset_prod {α : Type*} [DecidableEq α]
    (S : Finset α)
    (g : α → Config ι → ℝ)
    (hg : ∀ a ∈ S, ∃ c d : ℝ, ∃ C : Finset ι, 0 ≤ c ∧ 0 ≤ d ∧
      ∀ σ, g a σ = c + d * spinProduct C σ) :
    HasNonnegCorrelations fun σ => ∏ a ∈ S, g a σ := by
  induction S using Finset.induction with
  | empty => simpa using hasNonnegCorrelations_one
  | @insert x S' hx ih =>
    rw [show (fun σ => ∏ a ∈ insert x S', g a σ) =
        fun σ => (∏ a ∈ S', g a σ) * g x σ from by
      ext σ; rw [Finset.prod_insert hx]; ring]
    obtain ⟨c, d, C, hc, hd, hg_eq⟩ := hg x (Finset.mem_insert_self x S')
    simp_rw [hg_eq]
    exact hasNonnegCorrelations_mul
      (ih fun a ha' => hg a (Finset.mem_insert_of_mem ha')) hc hd C

omit [Fintype ι] [DecidableEq ι] in
/-- `edgeSpin σ e` takes values in `{-1, 1}`, so `exp_sign_decomp` applies. -/
theorem edgeSpin_sq (σ : Config ι) (e : Sym2 ι) :
    edgeSpin (K := ℝ) σ e ^ 2 = 1 := by
  refine Sym2.ind (fun i j => ?_) e
  simp only [edgeSpin, Sym2.lift_mk, Spin.sign]
  rw [show ((↑(σ i).toSign : ℝ) * ↑(σ j).toSign) ^ 2 =
      ((↑(σ i).toSign : ℝ) ^ 2) * ((↑(σ j).toSign : ℝ) ^ 2) from by ring]
  simp [← Int.cast_pow, Spin.toSign_sq]

omit [Fintype ι] [DecidableEq ι] in
/-- `exp(α · edgeSpin σ e) = cosh α + sinh α · edgeSpin σ e` for ±1-valued edgeSpin. -/
theorem exp_edgeSpin_decomp (α : ℝ) (σ : Config ι) (e : Sym2 ι) :
    Real.exp (α * edgeSpin (K := ℝ) σ e) =
    Real.cosh α + Real.sinh α * edgeSpin σ e := by
  have hsq := edgeSpin_sq σ e
  have hpm : edgeSpin (K := ℝ) σ e = 1 ∨ edgeSpin (K := ℝ) σ e = -1 := by
    have h0 : (edgeSpin (K := ℝ) σ e - 1) * (edgeSpin (K := ℝ) σ e + 1) = 0 := by
      nlinarith [hsq]
    rcases mul_eq_zero.mp h0 with h | h
    · left; linarith
    · right; linarith
  rcases hpm with h | h
  · simp [h, Real.cosh_add_sinh]
  · simp [h]; linarith [Real.cosh_add_sinh (-α), Real.cosh_neg α, Real.sinh_neg α]

/-- The Boltzmann weight has non-negative correlations for ferromagnetic parameters.
Proved by factoring `exp(-βH)` into `(cosh + sinh · σ)` factors and applying
`hasNonnegCorrelations_finset_prod`. -/
-- The factored form of the Boltzmann weight as a product of (cosh + sinh · spin) terms.
-- This equals boltzmannWeight but is directly amenable to hasNonnegCorrelations_finset_prod.
private noncomputable def bwFactored (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (σ : Config ι) : ℝ :=
  (∏ e ∈ G.edgeFinset, (Real.cosh (p.β * p.J) +
    Real.sinh (p.β * p.J) * edgeSpin (K := ℝ) σ e)) *
  (∏ i : ι, (Real.cosh (p.β * p.h) +
    Real.sinh (p.β * p.h) * Spin.sign ℝ (σ i)))

/-- The factored form has non-negative correlations. -/
private theorem bwFactored_hasNonnegCorrelations (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    HasNonnegCorrelations (bwFactored G p) := by
  unfold bwFactored
  -- Split into edge product and site product using hasNonnegCorrelations_mul
  -- First handle the edge product
  have hcJ := Real.cosh_pos (p.β * p.J) |>.le
  have hsJ := Real.sinh_nonneg_iff.mpr (mul_nonneg hf.hβ.le hf.hJ)
  have hcH := Real.cosh_pos (p.β * p.h) |>.le
  have hsH := Real.sinh_nonneg_iff.mpr (mul_nonneg hf.hβ.le hf.hh)
  -- Edge factors have HNC
  have hedge : HasNonnegCorrelations fun σ =>
      ∏ e ∈ G.edgeFinset, (Real.cosh (p.β * p.J) +
        Real.sinh (p.β * p.J) * edgeSpin (K := ℝ) σ e) := by
    apply hasNonnegCorrelations_finset_prod
    intro e he
    obtain ⟨⟨i, j⟩, rfl⟩ := Quot.exists_rep e
    have hne : i ≠ j := by
      intro h; subst h
      have hadj := SimpleGraph.mem_edgeFinset.mp he
      rw [SimpleGraph.mem_edgeSet] at hadj
      exact hadj.ne rfl
    exact ⟨_, _, {i, j}, hcJ, hsJ, fun σ => by
      simp [edgeSpin, Sym2.lift_mk, spinProduct, Finset.prod_pair hne, Spin.sign]⟩
  -- Multiply edge product by site factors
  have hsite := hasNonnegCorrelations_mul_prod Finset.univ hedge
      (fun i σ => Real.cosh (p.β * p.h) + Real.sinh (p.β * p.h) * Spin.sign ℝ (σ i))
      (fun i _ => ⟨_, _, {i}, hcH, hsH, fun σ => by
        simp [spinProduct, Spin.sign]⟩)
  -- Combine: bwFactored = edge_prod * site_prod
  convert hsite using 1

set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
/-- The factored form equals the Boltzmann weight. -/
private theorem bwFactored_eq_boltzmannWeight (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (σ : Config ι) :
    bwFactored G p σ = boltzmannWeight G p σ := by
  unfold bwFactored boltzmannWeight hamiltonian interactionEnergy externalFieldEnergy
  -- RHS: exp(-β * (-J * ∑_e edgeSpin - h * ∑_i sign)) = exp(βJ * ∑_e edgeSpin + βh * ∑_i sign)
  rw [show -p.β * (-(p.J) * ∑ e ∈ G.edgeFinset, edgeSpin σ e +
      -(p.h) * ∑ i : ι, Spin.sign ℝ (σ i)) =
      p.β * p.J * ∑ e ∈ G.edgeFinset, edgeSpin σ e +
      p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i) from by ring]
  rw [Real.exp_add]
  -- exp(βJ * ∑ edgeSpin) = ∏ exp(βJ * edgeSpin e)
  rw [show p.β * p.J * ∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e =
      ∑ e ∈ G.edgeFinset, p.β * p.J * edgeSpin (K := ℝ) σ e from by
    rw [Finset.mul_sum]]
  rw [Real.exp_sum]
  -- exp(βh * ∑ sign) = ∏ exp(βh * sign(σ i))
  rw [show p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i) =
      ∑ i : ι, p.β * p.h * Spin.sign ℝ (σ i) from by
    rw [Finset.mul_sum]]
  rw [Real.exp_sum]
  -- Each exp(βJ * edgeSpin) = cosh + sinh * edgeSpin
  congr 1
  · apply Finset.prod_congr rfl; intro e _
    exact (exp_edgeSpin_decomp (p.β * p.J) σ e).symm
  · apply Finset.prod_congr rfl; intro i _
    simp only [Spin.sign]
    rw [exp_sign_decomp (p.β * p.h) (σ i)]
    ring

theorem boltzmannWeight_hasNonnegCorrelations (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    HasNonnegCorrelations (boltzmannWeight G p) := by
  intro S
  have h := bwFactored_hasNonnegCorrelations G p hf S
  simp_rw [bwFactored_eq_boltzmannWeight] at h
  exact h

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
