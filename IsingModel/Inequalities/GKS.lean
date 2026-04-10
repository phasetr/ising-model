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

/-- A product of `exp(K_e · edgeSpin ω e)` over edges and `exp(K_i · sign(ω i))` over sites
has non-negative correlations, provided all K_e, K_i ≥ 0.
This is the common core of both GKS-I and GKS-II proofs. -/
theorem hasNonnegCorrelations_edge_site_product
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (edgeK : Sym2 ι → ℝ) (siteK : ι → ℝ)
    (hedgeK : ∀ e ∈ G.edgeFinset, 0 ≤ edgeK e)
    (hsiteK : ∀ i, 0 ≤ siteK i) :
    HasNonnegCorrelations fun σ =>
      (∏ e ∈ G.edgeFinset, Real.exp (edgeK e * edgeSpin (K := ℝ) σ e)) *
      (∏ i : ι, Real.exp (siteK i * Spin.sign ℝ (σ i))) := by
  have hedge : HasNonnegCorrelations fun σ =>
      ∏ e ∈ G.edgeFinset, Real.exp (edgeK e * edgeSpin (K := ℝ) σ e) := by
    apply hasNonnegCorrelations_finset_prod
    intro e he
    obtain ⟨⟨i, j⟩, rfl⟩ := Quot.exists_rep e
    have hne : i ≠ j := by
      intro h; subst h
      have hadj := SimpleGraph.mem_edgeFinset.mp he
      rw [SimpleGraph.mem_edgeSet] at hadj
      exact hadj.ne rfl
    exact ⟨Real.cosh (edgeK (Quot.mk _ (i, j))),
      Real.sinh (edgeK (Quot.mk _ (i, j))), {i, j},
      (Real.cosh_pos _).le, Real.sinh_nonneg_iff.mpr (hedgeK _ he), fun σ => by
        simp only [spinProduct, Finset.prod_pair hne, Spin.sign]
        exact exp_edgeSpin_decomp (edgeK (Quot.mk _ (i, j))) σ (Quot.mk _ (i, j))⟩
  exact hasNonnegCorrelations_mul_prod Finset.univ hedge
    (fun i σ => Real.exp (siteK i * Spin.sign ℝ (σ i)))
    (fun i _ => ⟨Real.cosh (siteK i), Real.sinh (siteK i), {i},
      (Real.cosh_pos _).le, Real.sinh_nonneg_iff.mpr (hsiteK i), fun σ => by
        simp only [Spin.sign, spinProduct, Finset.prod_singleton]
        rw [exp_sign_decomp (siteK i) (σ i)]; ring⟩)

-- The factored form of the Boltzmann weight as a product of (cosh + sinh · spin) terms.
-- This equals boltzmannWeight but is directly amenable to hasNonnegCorrelations_edge_site_product.
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

/-! ## General coupling GKS-I -/

/-- GKS-I for general non-negative coupling constants.
Given a weight function `w(σ) = ∏_{C} exp(K_C · σ^C)` where all `K_C ≥ 0`,
the function `w` has non-negative correlations.

This generalizes `boltzmannWeight_hasNonnegCorrelations` from pair interactions
to arbitrary multi-body couplings. It is needed for GKS-II where the doubled
system has modified coupling constants.

Reference: Friedli–Velenik, Theorem 3.49 (3.54), pp. 127–128. -/
theorem hasNonnegCorrelations_general_coupling
    (couplings : Finset (Finset ι))
    (K : Finset ι → ℝ)
    (hK : ∀ C ∈ couplings, 0 ≤ K C) :
    HasNonnegCorrelations fun σ =>
      ∏ C ∈ couplings, Real.exp (K C * spinProduct C σ) := by
  apply hasNonnegCorrelations_finset_prod
  intro C hC
  -- spinProduct C σ ∈ {-1, 1}, so exp(K_C · spinProduct C σ) = cosh(K_C) + sinh(K_C) · σ^C
  have hKC := hK C hC
  refine ⟨Real.cosh (K C), Real.sinh (K C), C,
    (Real.cosh_pos _).le, Real.sinh_nonneg_iff.mpr hKC, fun σ => ?_⟩
  -- exp(K_C * spinProduct C σ) = cosh(K_C) + sinh(K_C) * spinProduct C σ
  have hsq := spinProduct_sq C σ
  have hpm : spinProduct C σ = 1 ∨ spinProduct C σ = -1 := by
    have h0 : (spinProduct C σ - 1) * (spinProduct C σ + 1) = 0 := by nlinarith [hsq]
    rcases mul_eq_zero.mp h0 with h | h
    · left; linarith
    · right; linarith
  rcases hpm with h | h
  · simp [h, Real.cosh_add_sinh]
  · simp [h]; linarith [Real.cosh_add_sinh (-(K C)), Real.cosh_neg (K C), Real.sinh_neg (K C)]

/-! ## GKS-II: second Griffiths inequality -/

-- GKS-II: ⟨σ_A σ_B⟩ ≥ ⟨σ_A⟩⟨σ_B⟩ (Friedli–Velenik, Theorem 3.49 (3.55), pp. 127–128)
-- Proof by the duplicate variable trick: introduce independent copy χ,
-- change variables to (ω, ω'') where ω''_i = ω_i χ_i, fix ω'', and
-- apply GKS-I with modified coupling constants K_C(1 + ω''_C) ≥ 0.

/-- `1 - spinProduct B σ ≥ 0` pointwise, since `spinProduct B σ ∈ {-1, 1}`. -/
theorem one_sub_spinProduct_nonneg (B : Finset ι) (σ : Config ι) :
    0 ≤ 1 - spinProduct B σ := by
  have hsq := spinProduct_sq B σ
  have : (spinProduct B σ - 1) * (spinProduct B σ + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp this with h | h
  · linarith  -- spinProduct = 1, so 1 - 1 = 0 ≥ 0
  · linarith  -- spinProduct = -1, so 1 - (-1) = 2 ≥ 0

/-- The duplicate variable sum: `Σ_{ω,ω'} ω^A(ω^B - ω'^B) w(ω)w(ω')`.
Equals `Z² (⟨σ^{AΔB}⟩ - ⟨σ^A⟩⟨σ^B⟩)` after unfolding. -/
private noncomputable def duplicateSum (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A B : Finset ι) : ℝ :=
  ∑ ω : Config ι, ∑ ω' : Config ι,
    spinProduct A ω * (spinProduct B ω - spinProduct B ω') *
    boltzmannWeight G p ω * boltzmannWeight G p ω'

/-- The duplicate sum equals `Z²(corr(AΔB) - corr(A)·corr(B))`. -/
private theorem duplicateSum_eq (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A B : Finset ι) :
    duplicateSum G p A B =
    (partitionFunction G p) ^ 2 *
      (correlation G p (symmDiff A B) - correlation G p A * correlation G p B) := by
  have hZ := partitionFunction_ne_zero G p
  unfold duplicateSum correlation gibbsExpectation
  -- LHS = Σ_ω Σ_ω' σ^A(σ^B - σ'^B) w w'
  --     = Σ_ω σ^A σ^B w · Z - Σ_ω σ^A w · Σ_ω' σ'^B w'
  --     = Z · Σ σ^{AΔB} w - (Σ σ^A w)(Σ σ^B w)
  -- RHS = Z² · (Z⁻¹ Σ σ^{AΔB} w - Z⁻¹ Σ σ^A w · Z⁻¹ Σ σ^B w)
  --     = Z · Σ σ^{AΔB} w - (Σ σ^A w)(Σ σ^B w)
  -- Rewrite σ^A · σ^B = σ^{AΔB} in the LHS
  have hmul : ∀ ω : Config ι, spinProduct A ω * spinProduct B ω =
      spinProduct (symmDiff A B) ω := fun ω => spinProduct_mul A B ω
  -- Expand: LHS = Σ_ω (σ^{AΔB}_ω · Z - (Σ σ^A w)(σ^B_ω)) · w_ω ... complicated
  -- Strategy: rewrite both sides to the same expression and use ring/field_simp
  rw [sq]
  have hZne := partitionFunction_ne_zero G p
  field_simp
  -- Expand double sum: Σ_ω Σ_{ω'} f(ω)(g(ω)-g(ω')) w(ω) w(ω')
  -- = Σ_ω f(ω)g(ω)w(ω) · Σ_{ω'} w(ω') - Σ_ω f(ω)w(ω) · Σ_{ω'} g(ω')w(ω')
  have step1 : ∀ ω : Config ι,
      ∑ ω' : Config ι, spinProduct A ω * (spinProduct B ω - spinProduct B ω') *
        boltzmannWeight G p ω * boltzmannWeight G p ω' =
      spinProduct A ω * spinProduct B ω * boltzmannWeight G p ω *
        ∑ ω', boltzmannWeight G p ω' -
      spinProduct A ω * boltzmannWeight G p ω *
        ∑ ω', spinProduct B ω' * boltzmannWeight G p ω' := by
    intro ω
    simp_rw [show ∀ ω' : Config ι,
        spinProduct A ω * (spinProduct B ω - spinProduct B ω') *
        boltzmannWeight G p ω * boltzmannWeight G p ω' =
        spinProduct A ω * spinProduct B ω * boltzmannWeight G p ω *
        boltzmannWeight G p ω' -
        spinProduct A ω * boltzmannWeight G p ω *
        (spinProduct B ω' * boltzmannWeight G p ω')
      from fun ω' => by ring]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp_rw [step1, Finset.sum_sub_distrib, hmul]
  unfold partitionFunction
  simp_rw [← Finset.sum_mul]
  ring

/-- The modified weight for the duplicate variable proof.
For fixed `t : Config ι`, this is `exp(Σ_C K_C(1 + t^C) ω^C)` where
the sum runs over edges (K = βJ, C = {i,j}) and sites (K = βh, C = {i}).
The factor `(1 + t^C)` doubles or zeroes each coupling. -/
private noncomputable def modifiedWeight (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (t ω : Config ι) : ℝ :=
  (∏ e ∈ G.edgeFinset, Real.exp (p.β * p.J * (1 + edgeSpin (K := ℝ) t e) *
      edgeSpin (K := ℝ) ω e)) *
  (∏ i : ι, Real.exp (p.β * p.h * (1 + Spin.sign ℝ (t i)) * Spin.sign ℝ (ω i)))

/-- The variable-changed form of the duplicate sum.
`Σ_t (1 - t^B) · Σ_ω ω^{AΔB} · modifiedWeight(t, ω)` -/
private noncomputable def duplicateSumChanged (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A B : Finset ι) : ℝ :=
  ∑ t : Config ι, (1 - spinProduct B t) *
    ∑ ω : Config ι, spinProduct (symmDiff A B) ω * modifiedWeight G p t ω

/-- The duplicate sum equals its variable-changed form.
Change of variables: ω' ↦ t where t_i = ω_i · ω'_i (Spin.mul).
Reference: Friedli–Velenik, pp. 127–128. -/
private theorem duplicateSum_eq_changed (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A B : Finset ι) :
    duplicateSum G p A B = duplicateSumChanged G p A B := by
  unfold duplicateSum duplicateSumChanged
  -- For each fixed ω, define bijection on Config: ω' ↦ t where t_i = Spin.mul (ω i) (ω' i)
  -- Step 1: Transform each inner sum and rewrite summand
  have hinner : ∀ ω : Config ι,
      ∑ ω', spinProduct A ω * (spinProduct B ω - spinProduct B ω') *
        boltzmannWeight G p ω * boltzmannWeight G p ω' =
      ∑ t, (1 - spinProduct B t) *
        (spinProduct (symmDiff A B) ω * modifiedWeight G p t ω) := by
    intro ω
    -- Change variables: ω' ↦ t = fun i => Spin.mul (ω i) (ω' i)
    let φ : Config ι → Config ι := fun ω' i => Spin.mul (ω i) (ω' i)
    have hφ_inv : Function.Involutive φ := fun t => by ext i; simp [φ, Spin.mul_mul_cancel]
    rw [(Fintype.sum_bijective φ hφ_inv.bijective _ _ fun t => rfl).symm]
    apply Finset.sum_congr rfl; intro t _
    -- spinProduct B (φ t) = spinProduct B ω * spinProduct B t
    have hspB : spinProduct B (φ t) = spinProduct B ω * spinProduct B t := by
      unfold spinProduct; simp_rw [show ∀ i, (↑((φ t i).toSign) : ℝ) = ↑(ω i).toSign * ↑(t i).toSign from
        fun i => by simp [φ, Spin.toSign_mul]]; rw [Finset.prod_mul_distrib]
    rw [hspB]
    have hw : boltzmannWeight G p ω * boltzmannWeight G p (φ t) =
        modifiedWeight G p t ω := by
      -- w(ω) * w(φ t) = modifiedWeight(t, ω)
      -- Both sides are exp(...). Show the exponents are equal.
      unfold boltzmannWeight hamiltonian interactionEnergy externalFieldEnergy modifiedWeight
      rw [← Real.exp_add]
      congr 1
      -- Use: edgeSpin(φ t, e) = edgeSpin(ω,e) * edgeSpin(t,e)
      -- and: sign(φ t, i) = sign(ω i) * sign(t i)
      have hes : ∀ e, edgeSpin (K := ℝ) (φ t) e =
          edgeSpin (K := ℝ) ω e * edgeSpin (K := ℝ) t e := by
        intro e; refine Sym2.ind (fun i j => ?_) e
        simp [edgeSpin, Sym2.lift_mk, φ, Spin.sign, Spin.toSign_mul]; ring
      have hss : ∀ i, Spin.sign ℝ ((φ t) i) = Spin.sign ℝ (ω i) * Spin.sign ℝ (t i) := by
        intro i; simp [φ, Spin.sign, Spin.toSign_mul]
      simp_rw [hes, hss]
      -- After simp_rw: both sides have Σ_e and Σ_i with matching summands
      -- LHS: -β(-J Σ ω^e - h Σ ω_i) + -β(-J Σ (ω^e · t^e) - h Σ (ω_i · t_i))
      -- RHS: Σ_e βJ(1+t^e)ω^e + Σ_i βh(1+t_i)ω_i
      -- These are equal: βJω^e + βJω^e·t^e = βJ(1+t^e)ω^e
      -- Both sides are exp(something) or products of exp.
      -- Convert RHS from ∏ exp to exp(Σ) and show exponents match.
      rw [← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add]
      congr 1
      -- Goal after simp_rw hes, hss and exp manipulations:
      -- -(β * Σ_e -(J*ω^e)) - β * Σ_i -(h*ω_i) - β * Σ_e -(J*ω^e*t^e) - β * Σ_i -(h*ω_i*t_i)
      -- = (Σ_e βJ*t^e*ω^e + βJ*ω^e) + (Σ_i βh*t_i*ω_i + βh*ω_i)
      -- Use Finset.mul_sum to pull β*J inside sums, combine, then ring per term
      simp only [Finset.mul_sum, Finset.sum_neg_distrib, neg_neg,
        ← Finset.sum_add_distrib]
      -- Both sides are exp(exponent). The exponents are equal.
      -- LHS exponent (after congr): -β(H(ω)) + -β(H(φ t))
      -- RHS exponent (after exp_add): Σ_e K'_e·ω^e + Σ_i K'_i·ω_i
      -- where H = -JΣω^e - hΣω_i and K'_e = βJ(1+t^e), K'_i = βh(1+t_i)
      -- The key identity: βJω^e + βJω^e·t^e = βJ(1+t^e)ω^e
      -- Expand and combine sums
      -- LHS: -β(-JΣω^e - hΣω_i) + -β(-JΣω^e·t^e - hΣω_i·t_i)
      -- RHS: Σ βJ(1+t^e)ω^e + Σ βh(1+t_i)ω_i
      -- = Σ(βJω^e + βJω^e·t^e) + Σ(βhω_i + βhω_i·t_i)
      -- = βJΣω^e + βJΣω^e·t^e + βhΣω_i + βhΣω_i·t_i
      -- = -β(-JΣω^e - hΣω_i - JΣω^e·t^e - hΣω_i·t_i)
      -- = LHS
      -- Use Finset.sum_add_distrib to combine the 4 sums into 2
      -- Both sides are in ℝ. Rewrite to match.
      have : -p.β * (∑ i ∈ G.edgeFinset, -p.J * edgeSpin (K := ℝ) ω i +
          ∑ i, -p.h * Spin.sign ℝ (ω i)) +
        -p.β * (∑ i ∈ G.edgeFinset, -p.J * (edgeSpin (K := ℝ) ω i * edgeSpin (K := ℝ) t i) +
          ∑ i, -p.h * (Spin.sign ℝ (ω i) * Spin.sign ℝ (t i))) =
        ∑ e ∈ G.edgeFinset, p.β * p.J * (1 + edgeSpin (K := ℝ) t e) * edgeSpin (K := ℝ) ω e +
        ∑ i, p.β * p.h * (1 + Spin.sign ℝ (t i)) * Spin.sign ℝ (ω i) := by
        simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
        have h1 : ∀ e ∈ G.edgeFinset,
            -p.β * (-p.J * edgeSpin (K := ℝ) ω e) +
            -p.β * (-p.J * (edgeSpin (K := ℝ) ω e * edgeSpin (K := ℝ) t e)) =
            p.β * p.J * (1 + edgeSpin (K := ℝ) t e) * edgeSpin (K := ℝ) ω e :=
          fun _ _ => by ring
        have h2 : ∀ i ∈ (Finset.univ : Finset ι),
            -p.β * (-p.h * Spin.sign ℝ (ω i)) +
            -p.β * (-p.h * (Spin.sign ℝ (ω i) * Spin.sign ℝ (t i))) =
            p.β * p.h * (1 + Spin.sign ℝ (t i)) * Spin.sign ℝ (ω i) :=
          fun _ _ => by ring
        rw [show (∑ i ∈ G.edgeFinset, -p.β * (-p.J * edgeSpin (K := ℝ) ω i)) +
            (∑ i, -p.β * (-p.h * Spin.sign ℝ (ω i))) +
            ((∑ i ∈ G.edgeFinset, -p.β * (-p.J * (edgeSpin (K := ℝ) ω i * edgeSpin (K := ℝ) t i))) +
            (∑ i, -p.β * (-p.h * (Spin.sign ℝ (ω i) * Spin.sign ℝ (t i))))) =
          (∑ i ∈ G.edgeFinset, (-p.β * (-p.J * edgeSpin (K := ℝ) ω i) +
            -p.β * (-p.J * (edgeSpin (K := ℝ) ω i * edgeSpin (K := ℝ) t i)))) +
          (∑ i, (-p.β * (-p.h * Spin.sign ℝ (ω i)) +
            -p.β * (-p.h * (Spin.sign ℝ (ω i) * Spin.sign ℝ (t i)))))
          from by
            have e1 : ∑ i ∈ G.edgeFinset, (-p.β * (-p.J * edgeSpin (K := ℝ) ω i) +
                -p.β * (-p.J * (edgeSpin (K := ℝ) ω i * edgeSpin (K := ℝ) t i))) =
              ∑ i ∈ G.edgeFinset, -p.β * (-p.J * edgeSpin (K := ℝ) ω i) +
              ∑ i ∈ G.edgeFinset, -p.β * (-p.J * (edgeSpin (K := ℝ) ω i * edgeSpin (K := ℝ) t i)) :=
              Finset.sum_add_distrib
            have e2 : ∑ i : ι, (-p.β * (-p.h * Spin.sign ℝ (ω i)) +
                -p.β * (-p.h * (Spin.sign ℝ (ω i) * Spin.sign ℝ (t i)))) =
              ∑ i, -p.β * (-p.h * Spin.sign ℝ (ω i)) +
              ∑ i, -p.β * (-p.h * (Spin.sign ℝ (ω i) * Spin.sign ℝ (t i))) :=
              Finset.sum_add_distrib
            linarith]
        rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
        congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring
      exact this
    rw [show spinProduct A ω * (spinProduct B ω - spinProduct B ω * spinProduct B t) *
        boltzmannWeight G p ω * boltzmannWeight G p (φ t) =
      spinProduct A ω * spinProduct B ω * (1 - spinProduct B t) *
        (boltzmannWeight G p ω * boltzmannWeight G p (φ t)) from by ring,
      hw, spinProduct_mul A B ω]; ring
  simp_rw [hinner]
  -- Step 2: Swap sums Σ_ω Σ_t → Σ_t Σ_ω
  rw [Finset.sum_comm]
  -- Step 3: Factor out (1 - t^B)
  apply Finset.sum_congr rfl; intro t _
  rw [← Finset.mul_sum]

/-- The modified weight has non-negative correlations for each fixed `t`.
Same proof structure as `bwFactored_hasNonnegCorrelations` but with
modified couplings `K_C(1 + t^C) ≥ 0`. -/
private theorem modifiedWeight_nonneg_corr (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (t : Config ι) :
    HasNonnegCorrelations (modifiedWeight G p t) := by
  unfold modifiedWeight
  exact hasNonnegCorrelations_edge_site_product G
    (fun e => p.β * p.J * (1 + edgeSpin (K := ℝ) t e))
    (fun i => p.β * p.h * (1 + Spin.sign ℝ (t i)))
    (fun e _ => by
      apply mul_nonneg (mul_nonneg hf.hβ.le hf.hJ)
      have := edgeSpin_sq t e
      have : (edgeSpin (K := ℝ) t e - 1) * (edgeSpin (K := ℝ) t e + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h <;> linarith)
    (fun i => by
      apply mul_nonneg (mul_nonneg hf.hβ.le hf.hh)
      have := Spin.sign_sq (K := ℝ) (t i)
      have : (Spin.sign ℝ (t i) - 1) * (Spin.sign ℝ (t i) + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h <;> linarith)

private theorem duplicateSumChanged_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A B : Finset ι) :
    0 ≤ duplicateSumChanged G p A B := by
  unfold duplicateSumChanged
  apply Finset.sum_nonneg
  intro t _
  apply mul_nonneg (one_sub_spinProduct_nonneg B t)
  exact modifiedWeight_nonneg_corr G p hf t (symmDiff A B)

private theorem duplicateSum_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A B : Finset ι) :
    0 ≤ duplicateSum G p A B := by
  rw [duplicateSum_eq_changed]
  exact duplicateSumChanged_nonneg G p hf A B

/-- **Second Griffiths inequality (GKS-II)**: For a ferromagnetic Ising model
(`J ≥ 0`, `h ≥ 0`, `β > 0`), correlations are monotone:
`⟨σ_A σ_B⟩ ≥ ⟨σ_A⟩⟨σ_B⟩` for any subsets `A, B`.

Reference: Friedli–Velenik, Theorem 3.49 (3.55), pp. 127–128. -/
theorem gks_second (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A B : Finset ι) :
    correlation G p A * correlation G p B ≤ correlation G p (symmDiff A B) := by
  have hZ := partitionFunction_pos G p
  have hZ2 : (0 : ℝ) < partitionFunction G p ^ 2 := pow_pos hZ 2
  have hdup := duplicateSum_nonneg G p hf A B
  rw [duplicateSum_eq] at hdup
  -- hdup : 0 ≤ Z² * (corr(AΔB) - corr(A)*corr(B))
  -- Since Z² > 0, corr(AΔB) - corr(A)*corr(B) ≥ 0
  have hsub : 0 ≤ correlation G p (symmDiff A B) - correlation G p A * correlation G p B :=
    nonneg_of_mul_nonneg_right hdup hZ2
  linarith

end IsingModel
