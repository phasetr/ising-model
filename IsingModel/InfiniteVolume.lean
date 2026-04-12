import IsingModel.Inequalities.GKS

/-!
# Infinite volume limit

The convergence of Ising model correlation functions as the lattice
grows to infinity. The proof uses GKS-II (monotonicity in coupling
constants) and the boundedness of spin products.

## Main results

* `abs_correlation_le_one` — `|⟨σ^A⟩| ≤ 1` for the Ising model
* `abs_spinProduct_eq_one` — `|σ^A| = 1` for any configuration

## References

* Glimm–Jaffe, *Quantum Physics*, §4.2, pp. 58–59.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Boundedness of spin products (Proposition 4.2.2) -/

omit [Fintype ι] [DecidableEq ι] in
/-- The absolute value of any spin product is `1`: `|σ^A(σ)| = 1`.
Since each `σ_i ∈ {+1, -1}`, the product of `±1` values is `±1`. -/
theorem abs_spinProduct_eq_one (A : Finset ι) (σ : Config ι) :
    |spinProduct A σ| = 1 := by
  have hsq := spinProduct_sq A σ
  have h1 : |spinProduct A σ| ^ 2 = 1 := by rwa [sq_abs]
  nlinarith [abs_nonneg (spinProduct A σ),
    sq_abs (spinProduct A σ)]

omit [Fintype ι] [DecidableEq ι] in
/-- The spin product is bounded: `|σ^A(σ)| ≤ 1`.
Immediate from `abs_spinProduct_eq_one`. -/
theorem abs_spinProduct_le_one (A : Finset ι) (σ : Config ι) :
    |spinProduct A σ| ≤ 1 :=
  le_of_eq (abs_spinProduct_eq_one A σ)

/-- **Proposition 4.2.2** (Glimm–Jaffe, p. 58):
For the Ising model, `|⟨σ^A⟩| ≤ 1` for any correlation function.

Proof: `|σ^A| = 1` for each configuration, so `|⟨σ^A⟩| ≤ ⟨|σ^A|⟩ = 1`. -/
theorem abs_correlation_le_one (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A : Finset ι) :
    |correlation G p A| ≤ 1 := by
  unfold correlation gibbsExpectation
  have hZ := partitionFunction_pos G p
  -- |Z⁻¹ · Σ σ^A w| ≤ Z⁻¹ · Σ |σ^A| w ≤ Z⁻¹ · Σ w = Z⁻¹ · Z = 1
  rw [abs_mul]
  calc |(partitionFunction G p)⁻¹| * |∑ σ, spinProduct A σ * boltzmannWeight G p σ|
      ≤ (partitionFunction G p)⁻¹ * ∑ σ, boltzmannWeight G p σ := by
        rw [abs_inv, abs_of_pos hZ]
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hZ.le)
        calc |∑ σ, spinProduct A σ * boltzmannWeight G p σ|
            ≤ ∑ σ, |spinProduct A σ * boltzmannWeight G p σ| :=
              abs_sum_le_sum_abs _ _
          _ = ∑ σ, |spinProduct A σ| * boltzmannWeight G p σ := by
              congr 1; ext σ
              rw [abs_mul, abs_of_pos (boltzmannWeight_pos G p σ)]
          _ ≤ ∑ σ, 1 * boltzmannWeight G p σ := by
              apply Finset.sum_le_sum; intro σ _
              exact mul_le_mul_of_nonneg_right (abs_spinProduct_le_one A σ)
                (le_of_lt (boltzmannWeight_pos G p σ))
          _ = ∑ σ, boltzmannWeight G p σ := by simp
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hZ)

/-! ## Walsh orthogonality on {±1}^n

The spin products `{σ^S : S ⊆ ι}` form an orthogonal basis for functions
on `Config ι = ι → Spin`. The orthogonality relation is:
`Σ_σ σ^S · σ^T = if S = T then 2^|ι| else 0`. -/

/-- Walsh orthogonality: `Σ_σ σ^S · σ^T = 0` when `S ≠ T`.
This follows from `spinProduct_mul` and `sum_config_spinProduct_eq_zero`. -/
theorem walsh_orthogonality (S T : Finset ι) (hST : S ≠ T) :
    ∑ σ : Config ι, spinProduct S σ * spinProduct T σ = 0 := by
  simp_rw [spinProduct_mul]
  exact sum_config_spinProduct_eq_zero _ (Finset.symmDiff_nonempty.mpr hST)

/-- Walsh normalization: `Σ_σ (σ^S)² = 2^|ι|`. -/
theorem walsh_normalization (S : Finset ι) :
    ∑ σ : Config ι, spinProduct S σ * spinProduct S σ =
    Fintype.card (Config ι) := by
  simp_rw [spinProduct_mul, symmDiff_self]
  exact sum_config_spinProduct_empty

/-- Walsh completeness: `Σ_S σ^S(τ) · σ^S(σ) = card · [τ = σ]`.
This is the dual of Walsh orthogonality: orthogonality sums over
configurations, completeness sums over subsets. -/
theorem walsh_completeness (σ τ : Config ι) :
    ∑ S : Finset ι, spinProduct S σ * spinProduct S τ =
    if σ = τ then (Fintype.card (Config ι) : ℝ) else 0 := by
  -- Define ω = σ · τ (componentwise Spin.mul)
  let ω : Config ι := fun i => Spin.mul (σ i) (τ i)
  -- σ^S · τ^S = ω^S by spinProduct_mul-like identity
  have hmul : ∀ S : Finset ι, spinProduct S σ * spinProduct S τ =
      spinProduct S ω := by
    intro S; simp only [spinProduct, ω]
    rw [← Finset.prod_mul_distrib]
    congr 1; ext i; simp [Spin.toSign_mul]
  simp_rw [hmul]
  -- Σ_S ω^S = ∏_i (1 + ω_i) by Finset.prod_add_one
  have hprod : ∑ S : Finset ι, spinProduct S ω =
      ∏ i : ι, (1 + (↑(ω i).toSign : ℝ)) := by
    rw [show (∑ S : Finset ι, spinProduct S ω) =
        ∑ S ∈ Finset.univ.powerset, ∏ i ∈ S, (↑(ω i).toSign : ℝ) from by
      rw [Finset.powerset_univ]; rfl]
    rw [← Finset.prod_add_one]
    congr 1; ext i; ring
  rw [hprod]
  -- Case split: σ = τ or σ ≠ τ
  split
  · -- σ = τ: each factor = 1 + 1 = 2
    next h =>
    have hfact : ∀ i, (1 : ℝ) + ↑(ω i).toSign = 2 := fun i => by
      have : ω i = Spin.up := by
        simp only [ω]; rw [h]; cases τ i <;> simp [Spin.mul, Spin.flip]
      simp [this, Spin.toSign]; norm_num
    simp_rw [hfact, Finset.prod_const, Finset.card_univ]
    rw [show Fintype.card (Config ι) = 2 ^ Fintype.card ι from
      Fintype.card_fun]; norm_cast
  · -- σ ≠ τ: ∃ i, ω i = down, factor = 1+(-1) = 0
    next hne =>
    have ⟨i, hi⟩ : ∃ i, σ i ≠ τ i := Function.ne_iff.mp hne
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    have : ω i = Spin.down := by
      simp only [ω]; cases hσ : σ i <;> cases hτ : τ i <;>
        simp_all [Spin.mul, Spin.flip]
    simp [this, Spin.toSign]

/-- Fourier inversion on `{±1}^n`: any function `f : Config ι → ℝ` can be
expanded as `f(σ) = Σ_S ĉ_S σ^S` where `ĉ_S = card⁻¹ Σ_τ σ^S(τ) f(τ)`.
This follows from Walsh orthogonality. -/
theorem walsh_fourier_inversion (f : Config ι → ℝ) (σ : Config ι) :
    f σ = ∑ S : Finset ι,
      ((Fintype.card (Config ι) : ℝ)⁻¹ * ∑ τ : Config ι, spinProduct S τ * f τ) *
      spinProduct S σ := by
  have hcard : (Fintype.card (Config ι) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  -- Step 1: RHS → card⁻¹ Σ_τ f(τ) Σ_S σ^S(τ) σ^S(σ)
  symm
  trans ((Fintype.card (Config ι) : ℝ)⁻¹ *
    ∑ τ : Config ι, f τ * ∑ S : Finset ι, spinProduct S τ * spinProduct S σ)
  · -- Both sides equal c⁻¹ Σ_τ Σ_S f(τ) σ^S(τ) σ^S(σ)
    -- where c = Fintype.card (Config ι)
    -- LHS: Σ_S (c⁻¹ Σ_τ σ^S(τ) f(τ)) σ^S(σ)
    -- Pull c⁻¹ out, swap Σ_S Σ_τ to Σ_τ Σ_S, factor f(τ)
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1; ext τ; rw [Finset.sum_mul]; congr 1; ext S; ring
  · -- Apply walsh_completeness: Σ_S σ^S(τ) σ^S(σ) = card · [τ=σ]
    simp_rw [walsh_completeness, mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    field_simp

/-- Covariance of an HNC function with σ^B under ferromagnetic Boltzmann weight is ≥ 0.
For HNC f and ferromagnetic weight w:
`(Σ σ^B f w)(Σ w) - (Σ σ^B w)(Σ f w) ≥ 0`.

Proof: Fourier expand f = Σ_S ĉ_S σ^S (ĉ_S ≥ 0 by HNC). Then LHS =
Σ_S ĉ_S · Z² (corr(B△S) - corr(B)·corr(S)) ≥ 0 by `gks_second`. -/
theorem cov_hnc_boltzmann_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hferm : Ferromagnetic p) (f : Config ι → ℝ)
    (hf : HasNonnegCorrelations f) (B : Finset ι) :
    0 ≤ (∑ σ, spinProduct B σ * f σ * boltzmannWeight G p σ) *
        (∑ σ, boltzmannWeight G p σ) -
      (∑ σ, spinProduct B σ * boltzmannWeight G p σ) *
        (∑ σ, f σ * boltzmannWeight G p σ) := by
  -- Fourier expand f: f(σ) = Σ_S ĉ_S σ^S where ĉ_S ≥ 0
  let ĉ : Finset ι → ℝ := fun S =>
    (Fintype.card (Config ι) : ℝ)⁻¹ * ∑ τ, spinProduct S τ * f τ
  have hĉ_nonneg : ∀ S, 0 ≤ ĉ S := fun S =>
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (hf S)
  -- Rewrite f using Fourier inversion: σ^B f(σ) = Σ_S ĉ_S σ^{B△S}
  let w := boltzmannWeight G p
  -- Step 1: Σ σ^B f w = Σ_S ĉ_S · num(B△S) where num(X) = Σ σ^X w
  have hfourier : ∀ σ, f σ = ∑ S : Finset ι, ĉ S * spinProduct S σ :=
    walsh_fourier_inversion f
  -- Step 2: σ^B f(σ) = Σ_S ĉ_S σ^{B△S}
  have hprod : ∀ σ, spinProduct B σ * f σ =
      ∑ S, ĉ S * spinProduct (symmDiff B S) σ := by
    intro σ; rw [hfourier σ, Finset.mul_sum]
    congr 1; ext S; rw [← spinProduct_mul]; ring
  -- Step 3: Substitute and rearrange to Σ_S ĉ_S · bracket
  -- Step 3: Σ σ^B f w = Σ_S ĉ_S numR(B△S)
  let numR : Finset ι → ℝ := fun X => ∑ σ, spinProduct X σ * boltzmannWeight G p σ
  -- Each Fourier term contributes non-negatively:
  -- ĉ_S · [(Σ σ^{B△S} w)(Σ w) - (Σ σ^B w)(Σ σ^S w)] ≥ 0
  have hterm : ∀ S : Finset ι,
      0 ≤ ĉ S * ((∑ σ, spinProduct (symmDiff B S) σ * boltzmannWeight G p σ) *
        (∑ σ, boltzmannWeight G p σ) -
        (∑ σ, spinProduct B σ * boltzmannWeight G p σ) *
        (∑ σ, spinProduct S σ * boltzmannWeight G p σ)) := by
    intro S; apply mul_nonneg (hĉ_nonneg S)
    -- bracket = Z²(corr(B△S) - corr(B)·corr(S)) ≥ 0 by gks_second
    have hZ := partitionFunction_pos G p
    have hgks := gks_second G p hferm B S
    -- gks_second : corr B * corr S ≤ corr (B △ S)
    -- Unfold to get the numerator form
    unfold correlation gibbsExpectation partitionFunction at hgks
    -- corr(X) = Z⁻¹ num(X), so corr(B)·corr(S) ≤ corr(B△S)
    -- → Z⁻¹ num(B) · Z⁻¹ num(S) ≤ Z⁻¹ num(B△S)
    -- → num(B) num(S) ≤ Z num(B△S)
    -- → Z num(B△S) - num(B) num(S) ≥ 0
    -- → (Σ σ^{B△S} w)(Σ w) - (Σ σ^B w)(Σ σ^S w) ≥ 0
        -- Clear Z⁻¹ from hgks: corr(B)*corr(S) ≤ corr(B△S)
    -- → (Z⁻¹ nB)(Z⁻¹ nS) ≤ Z⁻¹ nBS → nB*nS ≤ nBS*Z
    -- hgks : Z⁻¹ * nB * (Z⁻¹ * nS) ≤ Z⁻¹ * nBS
    -- Multiply both sides by Z (positive), twice:
    have h1 := mul_le_mul_of_nonneg_left hgks hZ.le
    simp at h1
    have h2 := mul_le_mul_of_nonneg_right h1 hZ.le
    -- h2 has partitionFunction and Z⁻¹ mixed. Use field_simp to clear.
    unfold partitionFunction at h2
    field_simp [ne_of_gt hZ] at h2
    -- h2 : (Z * nB * nS) / Z ≤ Z * nBS
    -- Goal: 0 ≤ nBS * Z - nB * nS
    have h3 := (div_le_iff₀ hZ).mp h2
    -- h3 : Z * nB * nS ≤ Z * nBS * Z
    -- h3 : Z * nB * nS ≤ Z * nBS * Z (or similar after div_le_iff)
    -- Goal: 0 ≤ nBS * Z - nB * nS
    -- From h3: nB * nS ≤ nBS * Z (divide by Z > 0)
    -- nlinarith can handle this with Z > 0
    unfold partitionFunction at h3
    -- h3 : Z * nB * nS ≤ Z * nBS * Z, goal: 0 ≤ nBS * Z - nB * nS
    -- Both with Z = ∑ boltzmannWeight. nlinarith should close with Z > 0.
    -- h3: (∑ w) * nB * nS ≤ (∑ w) * nBS * (∑ w)
    -- → (∑ w) * (nB * nS) ≤ (∑ w) * (nBS * (∑ w))  [by ring at h3]
    -- → nB * nS ≤ nBS * (∑ w)  [by le_of_mul_le_mul_left h3 hZ]
    have h3a : (∑ σ : Config ι, boltzmannWeight G p σ) *
        ((∑ x, spinProduct B x * boltzmannWeight G p x) *
          (∑ x, spinProduct S x * boltzmannWeight G p x)) ≤
        (∑ σ : Config ι, boltzmannWeight G p σ) *
        ((∑ x, spinProduct (symmDiff B S) x * boltzmannWeight G p x) *
          (∑ σ : Config ι, boltzmannWeight G p σ)) := by nlinarith
    linarith [le_of_mul_le_mul_left h3a hZ]
  -- LHS = Σ_S ĉ_S · bracket = Σ (non-negative) ≥ 0
  -- The algebraic identity LHS = Σ_S hterm(S) uses:
  -- walsh_fourier_inversion (f = Σ ĉ σ^S) + spinProduct_mul + sum_comm
  sorry

-- Note: The general statement "for arbitrary HNC f, g: covariance ≥ 0"
-- is FALSE. Counterexample: Fourier coefficients with d̂_{B△S}d̂_∅ < d̂_B d̂_S.
-- The correct approach uses duplicateSum_nonneg for the SPECIFIC
-- boltzmannWeight (not arbitrary HNC), via Fourier expansion of f.

/-! ## Monotonicity in coupling constant (Proposition 4.2.1)

The correlation function `⟨σ^B⟩` is monotone increasing in the coupling
constant `J`. This follows from GKS-II:
`∂⟨σ^B⟩/∂J_A = ⟨σ^A σ^B⟩ - ⟨σ^A⟩⟨σ^B⟩ ≥ 0`.

In the discrete setting, we show that for `J₁ ≤ J₂` (with all other
parameters fixed), `⟨σ^B⟩_{J₁} ≤ ⟨σ^B⟩_{J₂}`.

The full proof requires showing that the derivative of ⟨σ^B⟩ w.r.t. J
equals the GKS-II expression. This is a calculus identity for the
Gibbs expectation, and its formalization is deferred to a subsequent step.

Reference: Glimm–Jaffe, Proposition 4.2.1, p. 58. -/

/-- The correlation function as a function of J (coupling constant),
with h and β fixed. -/
noncomputable def correlationJ (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (B : Finset ι) : ℝ → ℝ :=
  fun J => correlation G ⟨J, h, β⟩ B

/-- The reweighting inequality for correlation functions.
For `0 ≤ J₁ ≤ J₂`, `num J₂ * den J₁ - num J₁ * den J₂ ≥ 0`.

Proof: `exp(E J₂ σ) = R(σ) · exp(E J₁ σ)` where
`R(σ) = exp(β(J₂-J₁) Σ edgeSpin)`. Fourier expand R = Σ_S ĉ_S σ^S
(ĉ_S ≥ 0 by HNC of R). Then the difference equals
`Σ_S ĉ_S · Z₁² (corr₁(B△S) - corr₁(B)·corr₁(S)) ≥ 0`
by `gks_second` for each term. -/
private theorem correlation_reweighting_nonneg
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (B : Finset ι) (J₁ J₂ : ℝ) (hJ : J₁ ≤ J₂)
    (hJ₁ : 0 ≤ J₁) (hh : 0 ≤ h) (hβ : 0 < β) :
    0 ≤ (∑ σ : Config ι, spinProduct B σ * Real.exp
          (-β * hamiltonian G ⟨J₂, h, β⟩ σ)) *
        (∑ σ, Real.exp (-β * hamiltonian G ⟨J₁, h, β⟩ σ)) -
      (∑ σ, spinProduct B σ * Real.exp
          (-β * hamiltonian G ⟨J₁, h, β⟩ σ)) *
        (∑ σ, Real.exp (-β * hamiltonian G ⟨J₂, h, β⟩ σ)) := by
  -- exp(E J₂ σ) = exp(E J₁ σ) · R(σ) where R = exp(β(J₂-J₁) Σ edgeSpin)
  -- Fourier expand R = Σ_S ĉ_S σ^S (ĉ_S ≥ 0 by HNC)
  -- LHS = Σ_S ĉ_S · Z₁² · (corr₁(B△S) - corr₁(B)·corr₁(S)) ≥ 0
  -- Each factor: ĉ_S ≥ 0, Z₁² ≥ 0, corr₁(B△S) - corr₁(B)·corr₁(S) ≥ 0 by gks_second.
  -- exp(E J₂ σ) = exp(E J₁ σ) · R(σ) where R = exp(β(J₂-J₁) Σ edgeSpin)
  -- LHS = Σ_S ĉ_R(S) · [Z₁ · num₁(B△S) - num₁(B) · num₁(S)] ≥ 0
  -- Each bracket = Z₁² (corr₁(B△S) - corr₁(B)·corr₁(S)) ≥ 0 by gks_second.
  -- ĉ_R(S) = card⁻¹ Σ_σ σ^S R(σ) ≥ 0 by HNC of R.
  -- Show exp(E J₂ σ) = R(σ) · exp(E J₁ σ), then apply cov_hnc_boltzmann_nonneg.
  -- R(σ) = exp(β(J₂-J₁) Σ edgeSpin) has HNC by hasNonnegCorrelations_edge_site_product.
  -- The exp splitting + algebraic connection to cov_hnc_boltzmann_nonneg is deferred.
  sorry

/-- **Proposition 4.2.1** (Glimm–Jaffe, p. 58):
The correlation function is monotone increasing in J on `[0, ∞)`.

Proof: For `0 ≤ J₁ ≤ J₂`, use Fourier expansion of the reweighting factor
`R = exp(β(J₂-J₁) Σ edgeSpin)` and `gks_second` for each Fourier term. -/
theorem correlation_monotone_J (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (B : Finset ι) :
    MonotoneOn (correlationJ G h β B) (Set.Ici 0) := by
  -- f(J) = num(J) / den(J) where
  -- num(J) = Σ_σ spinProduct B σ * exp(-β * H_J(σ))
  -- den(J) = Σ_σ exp(-β * H_J(σ)) = partitionFunction
  -- H_J(σ) = -J * Σ edgeSpin - h * Σ sign
  -- So exp(-β H_J) = exp(βJ Σ edgeSpin + βh Σ sign)
  -- Both num and den are finite sums of exp(affine in J), hence differentiable.
  -- deriv f = (num' den - num den') / den²
  -- = β/den² Σ_σ Σ_τ σ^B (S(σ) - S(τ)) w(σ) w(τ)
  -- = β/den² Σ_e duplicateSum(B, e) ≥ 0
  -- by duplicateSum_nonneg.
  -- Hence Monotone by monotone_of_deriv_nonneg.
  -- Define the exponent as a function of J and σ
  let E : ℝ → Config ι → ℝ := fun J σ =>
    -β * hamiltonian G ⟨J, h, β⟩ σ
  -- den(J) = Σ exp(E J σ), positive
  let den : ℝ → ℝ := fun J => ∑ σ : Config ι, Real.exp (E J σ)
  have hden_pos : ∀ J, 0 < den J := fun J =>
    Finset.sum_pos (fun σ _ => Real.exp_pos _) Finset.univ_nonempty
  have hden_ne : ∀ J, den J ≠ 0 := fun J => ne_of_gt (hden_pos J)
  -- num(J) = Σ σ^B exp(E J σ) is differentiable
  let num : ℝ → ℝ := fun J =>
    ∑ σ : Config ι, spinProduct B σ * Real.exp (E J σ)
  -- f = num / den is differentiable
  have hf_eq : correlationJ G h β B = num / den := by
    ext J; simp only [correlationJ, correlation, gibbsExpectation,
      partitionFunction, boltzmannWeight, Pi.div_apply, div_eq_mul_inv]
    ring
  -- Direct algebraic proof: for J₁ ≤ J₂, show corr(J₂) ≥ corr(J₁)
  -- by rewriting corr(J₂) - corr(J₁) = [num₂ den₁ - num₁ den₂] / (den₁ den₂)
  -- and showing the numerator ≥ 0 using GKS-II.
  intro J₁ hJ₁_mem J₂ _hJ₂_mem hJ
  simp only [hf_eq, Pi.div_apply]
  rw [div_le_div_iff₀ (hden_pos J₁) (hden_pos J₂)]
  -- Goal: num J₁ * den J₂ ≤ num J₂ * den J₁
  -- Use the reweighting R(σ) = exp(β(J₂-J₁) Σ edgeSpin) which has HNC,
  -- and the Walsh/Fourier expansion R = Σ_S ĉ_S σ^S (ĉ_S ≥ 0 by HNC).
  -- Then num J₂ * den J₁ - num J₁ * den J₂
  --   = Σ_S ĉ_S · duplicateSum(⟨J₁,h,β⟩, B, S) ≥ 0
  -- by duplicateSum_nonneg.
  -- Walsh orthogonality (walsh_orthogonality, walsh_normalization) proved.
  -- The Fourier inversion identity and the algebraic connection
  -- to duplicateSum are the remaining formalization work.
  -- Apply hnc_correlation_nonneg via reweighting identity:
  -- exp(E J₂ σ) = R(σ) · exp(E J₁ σ) where R(σ) = exp(β(J₂-J₁) Σ edgeSpin)
  -- R has HNC, w₁ has HNC → hnc_correlation_nonneg gives the bound.
  -- The exp splitting + sum rearrangement is algebraic bookkeeping.
  exact le_of_sub_nonneg (correlation_reweighting_nonneg G h β B J₁ J₂ hJ
    (Set.mem_Ici.mp hJ₁_mem) hh hβ)

/-! ## Infinite volume convergence (Theorem 4.2.3)

For ferromagnetic Ising model with h ≥ 0, the correlation function
`⟨σ^B⟩_Λ` converges as Λ ↑ ℤ^d.

The proof combines:
- Monotonicity: `⟨σ^B⟩` increases with J (Proposition 4.2.1)
- Boundedness: `|⟨σ^B⟩| ≤ 1` (Proposition 4.2.2)
- Monotone bounded sequences converge

In the finite lattice setting, "Λ grows" means "J increases from 0 to J_max",
and the correlation function is a monotone bounded function of J.

The formalization of the lattice growth sequence and the convergence
theorem requires defining the sequence of finite volumes and relating
the correlation functions across different lattice sizes.
This is deferred to a subsequent step. -/

-- Future work: formalize lattice growth sequence and convergence theorem
-- (requires lattice embedding + tendsto_of_monotone + bddAbove from abs_correlation_le_one)

end IsingModel
