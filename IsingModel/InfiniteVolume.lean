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
    simp (config := { decide := true }) only [] at h1
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
  -- LHS = Σ_S ĉ_S bracket by Fourier substitution + sum rearrangement
  have eq2 : ∑ σ : Config ι, f σ * boltzmannWeight G p σ =
    ∑ S : Finset ι, ĉ S * ∑ σ : Config ι,
      spinProduct S σ * boltzmannWeight G p σ := by
    simp_rw [hfourier, Finset.sum_mul]
    exact (Finset.sum_comm).trans (Finset.sum_congr rfl (fun S _ => by
      simp_rw [show ∀ x, ĉ S * spinProduct S x * boltzmannWeight G p x =
        ĉ S * (spinProduct S x * boltzmannWeight G p x) from fun _ => by ring]
      rw [← Finset.mul_sum]))
  -- Rewrite the first sum: Σ σ^B f w = Σ_S ĉ_S numR(B△S)
  have hnum1 : ∑ σ : Config ι,
      (∑ S : Finset ι, ĉ S * spinProduct (symmDiff B S) σ) *
      boltzmannWeight G p σ =
    ∑ S : Finset ι, ĉ S * ∑ σ : Config ι,
      spinProduct (symmDiff B S) σ * boltzmannWeight G p σ := by
    simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]
    congr 1; ext S; simp_rw [mul_assoc]; rw [← Finset.mul_sum]
  simp_rw [hprod]
  rw [hnum1, eq2]
  -- Now: 0 ≤ (Σ_S ĉ_S numR(B△S))(Σ w) - numR(B)(Σ_S ĉ_S numR(S))
  -- Distribute the products into sums and combine
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  -- = Σ_S (ĉ_S numR(B△S)(Σ w) - numR(B)(ĉ_S numR(S)))
  exact Finset.sum_nonneg (fun S _ => by convert hterm S using 1; ring)

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

The proof uses the reweighting factor `R(σ) = ∏ exp(β(J₂-J₁) edgeSpin)`,
which has HNC. The Hamiltonian splitting `exp(-β H_{J₂}) = R · exp(-β H_{J₁})`
reduces to a covariance bound via `cov_hnc_boltzmann_nonneg`.

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
  -- Step 1: Hamiltonian splitting: exp(-β H_{J₂}) = R · exp(-β H_{J₁})
  -- where R(σ) = ∏_e exp(β(J₂-J₁) edgeSpin(σ,e))
  have hexp : ∀ σ, Real.exp (-β * hamiltonian G ⟨J₂, h, β⟩ σ) =
      (∏ e ∈ G.edgeFinset, Real.exp (β * (J₂ - J₁) * edgeSpin (K := ℝ) σ e)) *
      Real.exp (-β * hamiltonian G ⟨J₁, h, β⟩ σ) := by
    intro σ
    rw [← Real.exp_sum, ← Real.exp_add]
    congr 1
    unfold hamiltonian interactionEnergy externalFieldEnergy
    simp only [← Finset.mul_sum]; ring
  -- Step 2: R has non-negative correlations (HNC)
  -- by hasNonnegCorrelations_edge_site_product with edgeK = β(J₂-J₁), siteK = 0
  have hR : HasNonnegCorrelations (fun σ =>
      ∏ e ∈ G.edgeFinset, Real.exp (β * (J₂ - J₁) * edgeSpin (K := ℝ) σ e)) := by
    intro S
    have hhnc := hasNonnegCorrelations_edge_site_product G
      (fun _ => β * (J₂ - J₁)) (fun _ => 0)
      (fun _ _ => mul_nonneg hβ.le (sub_nonneg.mpr hJ))
      (fun _ => le_refl 0) S
    simp only [zero_mul, Real.exp_zero, Finset.prod_const_one, mul_one] at hhnc
    exact hhnc
  -- Step 3: ⟨J₁, h, β⟩ is ferromagnetic
  have hferm : Ferromagnetic (⟨J₁, h, β⟩ : IsingParams ℝ) := ⟨hJ₁, hh, hβ⟩
  -- Step 4: Rewrite exp(-β H_{J₂}) → R · exp(-β H_{J₁}) and apply cov_hnc_boltzmann_nonneg
  simp_rw [hexp]
  -- Goal: 0 ≤ (Σ σ^B · (R · w₁))(Σ w₁) - (Σ σ^B · w₁)(Σ R · w₁)
  -- Reassociate multiplication and unfold boltzmannWeight
  simp only [← mul_assoc]
  exact cov_hnc_boltzmann_nonneg G ⟨J₁, h, β⟩ hferm _ hR B

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
  -- R has HNC → cov_hnc_boltzmann_nonneg gives the bound.
  exact le_of_sub_nonneg (correlation_reweighting_nonneg G h β B J₁ J₂ hJ
    (Set.mem_Ici.mp hJ₁_mem) hh hβ)

/-! ## Convergence of correlation functions (Theorem 4.2.3)

For the ferromagnetic Ising model with h ≥ 0, the correlation function
`⟨σ^B⟩` converges as the coupling constant J → ∞. The proof combines:
- Monotonicity: `⟨σ^B⟩` increases with J (Proposition 4.2.1)
- Boundedness: `|⟨σ^B⟩| ≤ 1` (Proposition 4.2.2)
- Monotone bounded sequences converge (`tendsto_atTop_ciSup`)

In the finite lattice setting, "Λ grows" means coupling constants increase
from 0 to their full values, and the correlation function is a monotone
bounded function of J.

Reference: Glimm–Jaffe, Theorem 4.2.3, p. 59. -/

/-- The correlation function is non-negative for ferromagnetic parameters.
For `J ≥ 0`, `h ≥ 0`, `β > 0`: `⟨σ^B⟩ ≥ 0` by GKS-I. -/
theorem correlationJ_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (B : Finset ι)
    (J : ℝ) (hJ : 0 ≤ J) :
    0 ≤ correlationJ G h β B J :=
  gks_first G ⟨J, h, β⟩ ⟨hJ, hh, hβ⟩ B

/-- The correlation function is bounded above by 1.
From `|⟨σ^B⟩| ≤ 1` we get `⟨σ^B⟩ ≤ 1`. -/
theorem correlationJ_le_one (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (B : Finset ι) (J : ℝ) :
    correlationJ G h β B J ≤ 1 :=
  le_trans (le_abs_self _) (abs_correlation_le_one G ⟨J, h, β⟩ B)

/-- **Theorem 4.2.3** (Glimm–Jaffe, p. 59):
The correlation function converges as J → ∞ along natural numbers.

For ferromagnetic parameters (`h ≥ 0`, `β > 0`), the sequence
`n ↦ ⟨σ^B⟩_{(G, n, h, β)}` is monotone increasing (by Prop 4.2.1)
and bounded above by 1 (by Prop 4.2.2), hence convergent by
the monotone convergence theorem. The limit equals the supremum
`⨆ n, ⟨σ^B⟩_{(G, n, h, β)}`. -/
theorem correlation_convergent (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (B : Finset ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => correlationJ G h β B n)
      Filter.atTop (nhds L) := by
  -- Step 1: The sequence is monotone (Proposition 4.2.1)
  have hmono : Monotone (fun n : ℕ => correlationJ G h β B n) := by
    intro a b hab
    exact correlation_monotone_J G h hh β hβ B
      (Set.mem_Ici.mpr (Nat.cast_nonneg a))
      (Set.mem_Ici.mpr (Nat.cast_nonneg b))
      (Nat.cast_le.mpr hab)
  -- Step 2: The sequence is bounded above by 1 (Proposition 4.2.2)
  have hbdd : BddAbove (Set.range (fun n : ℕ => correlationJ G h β B n)) :=
    ⟨1, fun _ ⟨n, hn⟩ => hn ▸ correlationJ_le_one G h β B n⟩
  -- Step 3: Monotone + bounded above → convergent (to the supremum)
  exact ⟨_, tendsto_atTop_ciSup hmono hbdd⟩

/-! ## Monotonicity in external field (Proposition 4.2.4)

The correlation function `⟨σ^B⟩` is monotone increasing in the external
field `h`. This follows from GKS-II via the reweighting factor
`R(σ) = ∏_i exp(β(h₂-h₁) · sign(σ_i))`, which has HNC.

Reference: Glimm–Jaffe, Proposition 4.2.4 (Exercise), p. 58. -/

/-- The correlation function as a function of h (external field),
with J and β fixed. -/
noncomputable def correlationH (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (B : Finset ι) : ℝ → ℝ :=
  fun h => correlation G ⟨J, h, β⟩ B

/-- The reweighting inequality for correlation functions in h.
For `0 ≤ h₁ ≤ h₂`, the numerator cross-difference is non-negative. -/
private theorem correlation_reweighting_h_nonneg
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (B : Finset ι) (h₁ h₂ : ℝ) (hh : h₁ ≤ h₂)
    (hJ : 0 ≤ J) (hh₁ : 0 ≤ h₁) (hβ : 0 < β) :
    0 ≤ (∑ σ : Config ι, spinProduct B σ * Real.exp
          (-β * hamiltonian G ⟨J, h₂, β⟩ σ)) *
        (∑ σ, Real.exp (-β * hamiltonian G ⟨J, h₁, β⟩ σ)) -
      (∑ σ, spinProduct B σ * Real.exp
          (-β * hamiltonian G ⟨J, h₁, β⟩ σ)) *
        (∑ σ, Real.exp (-β * hamiltonian G ⟨J, h₂, β⟩ σ)) := by
  -- Step 1: Hamiltonian splitting: exp(-β H_{h₂}) = R · exp(-β H_{h₁})
  -- where R(σ) = ∏_i exp(β(h₂-h₁) · sign(σ_i))
  have hexp : ∀ σ, Real.exp (-β * hamiltonian G ⟨J, h₂, β⟩ σ) =
      (∏ i : ι, Real.exp (β * (h₂ - h₁) * Spin.sign ℝ (σ i))) *
      Real.exp (-β * hamiltonian G ⟨J, h₁, β⟩ σ) := by
    intro σ
    rw [← Real.exp_sum, ← Real.exp_add]
    congr 1
    unfold hamiltonian interactionEnergy externalFieldEnergy
    simp only [Spin.sign, ← Finset.mul_sum]; ring
  -- Step 2: R has non-negative correlations (HNC)
  have hR : HasNonnegCorrelations (fun σ =>
      ∏ i : ι, Real.exp (β * (h₂ - h₁) * Spin.sign ℝ (σ i))) := by
    intro S
    have hhnc := hasNonnegCorrelations_edge_site_product G
      (fun _ => 0) (fun _ => β * (h₂ - h₁))
      (fun _ _ => le_refl 0)
      (fun _ => mul_nonneg hβ.le (sub_nonneg.mpr hh)) S
    simp only [zero_mul, Real.exp_zero, Finset.prod_const_one, one_mul] at hhnc
    convert hhnc using 1
  -- Step 3: ⟨J, h₁, β⟩ is ferromagnetic
  have hferm : Ferromagnetic (⟨J, h₁, β⟩ : IsingParams ℝ) := ⟨hJ, hh₁, hβ⟩
  -- Step 4: Apply cov_hnc_boltzmann_nonneg
  simp_rw [hexp]
  simp only [← mul_assoc]
  exact cov_hnc_boltzmann_nonneg G ⟨J, h₁, β⟩ hferm _ hR B

/-- **Proposition 4.2.4** (Glimm–Jaffe, p. 58, exercise):
The correlation function is monotone increasing in h on `[0, ∞)`.

Proof: For `0 ≤ h₁ ≤ h₂`, use the reweighting factor
`R = ∏_i exp(β(h₂-h₁) · sign(σ_i))` (which has HNC) and `gks_second`. -/
theorem correlation_monotone_h (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) (B : Finset ι) :
    MonotoneOn (correlationH G J β B) (Set.Ici 0) := by
  let E : ℝ → Config ι → ℝ := fun h σ =>
    -β * hamiltonian G ⟨J, h, β⟩ σ
  let den : ℝ → ℝ := fun h => ∑ σ : Config ι, Real.exp (E h σ)
  have hden_pos : ∀ h, 0 < den h := fun h =>
    Finset.sum_pos (fun σ _ => Real.exp_pos _) Finset.univ_nonempty
  let num : ℝ → ℝ := fun h =>
    ∑ σ : Config ι, spinProduct B σ * Real.exp (E h σ)
  have hf_eq : correlationH G J β B = num / den := by
    ext h; simp only [correlationH, correlation, gibbsExpectation,
      partitionFunction, boltzmannWeight, Pi.div_apply, div_eq_mul_inv]
    ring
  intro h₁ hh₁_mem h₂ _hh₂_mem hh
  simp only [hf_eq, Pi.div_apply]
  rw [div_le_div_iff₀ (hden_pos h₁) (hden_pos h₂)]
  exact le_of_sub_nonneg (correlation_reweighting_h_nonneg G J β B h₁ h₂ hh
    hJ (Set.mem_Ici.mp hh₁_mem) hβ)

/-! ## Upper bound on the correlation (without absolute value) -/

/-- The correlation function is bounded above by `1`.
Extracted from `abs_correlation_le_one` via `a ≤ |a|`. -/
theorem correlation_le_one (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A : Finset ι) :
    correlation G p A ≤ 1 :=
  le_trans (le_abs_self _) (abs_correlation_le_one G p A)

/-- The correlation function is bounded below by `-1`.
Extracted from `abs_correlation_le_one` via the `abs_le` characterization. -/
theorem neg_one_le_correlation (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A : Finset ι) :
    -1 ≤ correlation G p A :=
  (abs_le.mp (abs_correlation_le_one G p A)).1

/-! ## Monotonicity in the lattice (Theorem 4.2.3, lattice version)

For a fixed ambient finite lattice `ι` and ferromagnetic parameters `p`,
if `G₁ ≤ G₂` (subgraph of the interaction graph), then the correlation
function is monotone: `⟨σ^A⟩_{G₁} ≤ ⟨σ^A⟩_{G₂}`.

This is the *discretized* formalization of GJ §4.2 Thm 4.2.3's statement
"`Λ ↑ ℝᵈ`": increasing the lattice corresponds to turning on couplings
`J_A : 0 → βJ` for new edges. The original GJ statement is over an
infinite ambient lattice with finite-volume exhaustions; our version
uses a fixed finite ambient lattice with growing subgraphs, preserving
the proof mechanism (GKS-I + monotonicity + boundedness).

Reference: Glimm–Jaffe, Theorem 4.2.3, p. 59. -/

/-- HNC of a product `∏_{e ∈ E} exp(K e · edgeSpin σ e)` over an arbitrary
non-diagonal Finset `E` of `Sym2 ι`, with non-negative `K`.
A graph-free variant of `hasNonnegCorrelations_edge_site_product`. -/
private theorem hasNonnegCorrelations_edge_prod_of_finset
    (E : Finset (Sym2 ι)) (hE : ∀ e ∈ E, ¬ e.IsDiag)
    (K : Sym2 ι → ℝ) (hK : ∀ e ∈ E, 0 ≤ K e) :
    HasNonnegCorrelations
      (fun σ => ∏ e ∈ E, Real.exp (K e * edgeSpin (K := ℝ) σ e)) := by
  apply hasNonnegCorrelations_finset_prod
  intro e he
  obtain ⟨⟨i, j⟩, rfl⟩ := Quot.exists_rep e
  have hne : i ≠ j := fun hij => hE _ he (Sym2.mk_isDiag_iff.mpr hij)
  refine ⟨Real.cosh (K (Quot.mk _ (i, j))),
    Real.sinh (K (Quot.mk _ (i, j))), {i, j},
    (Real.cosh_pos _).le,
    Real.sinh_nonneg_iff.mpr (hK _ he), fun σ => ?_⟩
  simp only [spinProduct, Finset.prod_pair hne]
  exact exp_edgeSpin_decomp _ σ _

/-- The Boltzmann weight on a larger graph factors through a reweighting
`R(σ) = ∏_{e ∈ E(G₂)\E(G₁)} exp(βJ · edgeSpin σ e)`:
`w_{G₂}(σ) = R(σ) · w_{G₁}(σ)`. -/
theorem boltzmannWeight_subgraph_factor
    {G₁ G₂ : SimpleGraph ι} [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
    (h₁₂ : G₁ ≤ G₂) (p : IsingParams ℝ) (σ : Config ι) :
    boltzmannWeight G₂ p σ =
    (∏ e ∈ G₂.edgeFinset \ G₁.edgeFinset,
      Real.exp (p.β * p.J * edgeSpin (K := ℝ) σ e)) *
    boltzmannWeight G₁ p σ := by
  have hsub : G₁.edgeFinset ⊆ G₂.edgeFinset := SimpleGraph.edgeFinset_mono h₁₂
  rw [← Real.exp_sum]
  unfold boltzmannWeight
  rw [← Real.exp_add]
  congr 1
  unfold hamiltonian interactionEnergy externalFieldEnergy
  have hdis : ∑ e ∈ G₂.edgeFinset, edgeSpin (K := ℝ) σ e =
      ∑ e ∈ G₂.edgeFinset \ G₁.edgeFinset, edgeSpin (K := ℝ) σ e +
      ∑ e ∈ G₁.edgeFinset, edgeSpin (K := ℝ) σ e := by
    rw [← Finset.sum_sdiff hsub, add_comm]
  rw [show ∑ e ∈ G₂.edgeFinset \ G₁.edgeFinset, p.β * p.J * edgeSpin (K := ℝ) σ e =
      p.β * p.J * ∑ e ∈ G₂.edgeFinset \ G₁.edgeFinset, edgeSpin (K := ℝ) σ e from by
      rw [Finset.mul_sum]]
  rw [hdis]
  ring

/-- **Theorem 4.2.3** (Glimm–Jaffe, p. 59; lattice version):
For a ferromagnetic Ising model, the correlation function is monotone
under the subgraph ordering: if `G₁ ≤ G₂` (as `SimpleGraph` on the
ambient lattice `ι`), then `⟨σ^A⟩_{G₁} ≤ ⟨σ^A⟩_{G₂}`.

Proof: Factor `w_{G₂} = R · w_{G₁}` where `R` has HNC (since it is a
product of non-negative-coefficient exponentials of edge spins), then
apply `cov_hnc_boltzmann_nonneg` on the base graph `G₁`. -/
theorem correlation_monotone_subgraph
    {G₁ G₂ : SimpleGraph ι} [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
    (h₁₂ : G₁ ≤ G₂) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset ι) :
    correlation G₁ p A ≤ correlation G₂ p A := by
  set R : Config ι → ℝ := fun σ =>
    ∏ e ∈ G₂.edgeFinset \ G₁.edgeFinset,
      Real.exp (p.β * p.J * edgeSpin (K := ℝ) σ e) with hR_def
  have hR : HasNonnegCorrelations R :=
    hasNonnegCorrelations_edge_prod_of_finset
      (G₂.edgeFinset \ G₁.edgeFinset)
      (fun e he =>
        G₂.not_isDiag_of_mem_edgeFinset (Finset.mem_sdiff.mp he).1)
      (fun _ => p.β * p.J)
      (fun _ _ => mul_nonneg hf.hβ.le hf.hJ)
  have hfact : ∀ σ, boltzmannWeight G₂ p σ = R σ * boltzmannWeight G₁ p σ :=
    fun σ => boltzmannWeight_subgraph_factor h₁₂ p σ
  have hcov := cov_hnc_boltzmann_nonneg G₁ p hf R hR A
  have hnum : ∑ σ : Config ι, spinProduct A σ * R σ * boltzmannWeight G₁ p σ =
      ∑ σ, spinProduct A σ * boltzmannWeight G₂ p σ := by
    apply Finset.sum_congr rfl; intro σ _
    rw [hfact σ]; ring
  have hden : ∑ σ : Config ι, R σ * boltzmannWeight G₁ p σ =
      ∑ σ, boltzmannWeight G₂ p σ := by
    apply Finset.sum_congr rfl; intro σ _
    exact (hfact σ).symm
  rw [hnum, hden] at hcov
  have hZ₁ := partitionFunction_pos G₁ p
  have hZ₂ := partitionFunction_pos G₂ p
  unfold correlation gibbsExpectation partitionFunction
  unfold partitionFunction at hZ₁ hZ₂
  rw [mul_comm ((∑ σ : Config ι, boltzmannWeight G₁ p σ)⁻¹)
      (∑ σ, spinProduct A σ * boltzmannWeight G₁ p σ),
      mul_comm ((∑ σ : Config ι, boltzmannWeight G₂ p σ)⁻¹)
      (∑ σ, spinProduct A σ * boltzmannWeight G₂ p σ)]
  rw [← div_eq_mul_inv, ← div_eq_mul_inv]
  rw [div_le_div_iff₀ hZ₁ hZ₂]
  linarith

/-! ## Convergence along an increasing chain of subgraphs

For an increasing sequence of subgraphs `Gn : ℕ → SimpleGraph ι` with
ferromagnetic parameters, the correlation function `n ↦ ⟨σ^A⟩_{Gn n}`
is monotone (by `correlation_monotone_subgraph`) and bounded above by
`1` (by `correlation_le_one`), hence convergent by monotone-bounded. -/

/-- **Theorem 4.2.3** (Glimm–Jaffe, p. 59; lattice version, convergence):
For any increasing sequence of subgraphs `Gₙ ↑` on a fixed ambient finite
lattice, with ferromagnetic parameters, the correlation function
`n ↦ ⟨σ^A⟩_{Gₙ}` converges as `n → ∞`. -/
theorem correlation_convergent_subgraph
    (Gn : ℕ → SimpleGraph ι) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => correlation (Gn n) p A)
      Filter.atTop (nhds L) := by
  have hcorr_mono : Monotone (fun n : ℕ => correlation (Gn n) p A) :=
    fun a b hab => correlation_monotone_subgraph (hmono hab) p hf A
  have hbdd : BddAbove (Set.range (fun n : ℕ => correlation (Gn n) p A)) :=
    ⟨1, fun _ ⟨n, hn⟩ => hn ▸ correlation_le_one (Gn n) p A⟩
  exact ⟨_, tendsto_atTop_ciSup hcorr_mono hbdd⟩

/-! ## Named corollaries of the lattice-growth convergence

Direct specializations of `correlation_convergent_subgraph` at the most
physically relevant subsets: single-site magnetization `⟨σᵢ⟩` and
two-point correlation `⟨σᵢσⱼ⟩`.  Both are used downstream in §5
(symmetry breaking, phase transitions). -/

/-- **Magnetization convergence** (Glimm–Jaffe, §5.3 context):
the single-site magnetization `⟨σᵢ⟩_{Gₙ}` converges along any increasing
subgraph sequence. Direct specialization of `correlation_convergent_subgraph`
to `A = {i}`. -/
theorem magnetization_convergent_subgraph
    (Gn : ℕ → SimpleGraph ι) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => correlation (Gn n) p {i})
      Filter.atTop (nhds L) :=
  correlation_convergent_subgraph Gn hmono p hf {i}

/-- **Two-point correlation convergence** (Glimm–Jaffe, §5.1 context):
the two-point correlation `⟨σᵢσⱼ⟩_{Gₙ}` converges along any increasing
subgraph sequence. Direct specialization of `correlation_convergent_subgraph`
to `A = {i, j}`. -/
theorem twoPoint_convergent_subgraph
    (Gn : ℕ → SimpleGraph ι) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => correlation (Gn n) p {i, j})
      Filter.atTop (nhds L) :=
  correlation_convergent_subgraph Gn hmono p hf {i, j}

/-! ## Monotonicity in β (inverse temperature)

The correlation function is monotone increasing in β for ferromagnetic
parameters. Proof uses the rescaling identity
`⟨σ^A⟩_{(J,h,β)} = ⟨σ^A⟩_{(βJ, βh, 1)}`
(analogous to `partitionFunction_beta_rescale` in `Conditioning.lean`)
to reduce to the already-established `correlation_monotone_J`
(Prop 4.2.1) and `correlation_monotone_h` (Prop 4.2.4).

Reference: Glimm–Jaffe, Propositions 4.2.1 and 4.2.4 (the J- and h-
monotonicity of correlation); Cor. 10.2.3 is the corresponding statement
for the partition function `Z`. -/

/-- The rescaling identity for the correlation function:
`⟨σ^A⟩_{(J, h, β)} = ⟨σ^A⟩_{(βJ, βh, 1)}`. Follows from the fact that
the Boltzmann weights `exp(-β H_{J,h}(σ))` and `exp(-1 · H_{βJ,βh}(σ))`
are pointwise equal. -/
private theorem correlation_rescale_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (A : Finset ι) :
    correlation G ⟨J, h, β⟩ A = correlation G ⟨β * J, β * h, 1⟩ A := by
  have hw : ∀ σ : Config ι,
      boltzmannWeight G ⟨J, h, β⟩ σ = boltzmannWeight G ⟨β * J, β * h, 1⟩ σ := by
    intro σ
    unfold boltzmannWeight hamiltonian interactionEnergy externalFieldEnergy
    congr 1; ring
  unfold correlation gibbsExpectation partitionFunction
  simp_rw [hw]

/-- **Correlation β-monotonicity**: for ferromagnetic parameters
(`J ≥ 0`, `h ≥ 0`), the correlation function is monotone increasing in
the inverse temperature `β` on `(0, ∞)`.

Proof: Apply the rescaling identity `correlation_rescale_beta` to
reduce to `correlation_monotone_J` and `correlation_monotone_h`:
increasing β from β₁ to β₂ moves `(β₁J, β₁h)` to `(β₂J, β₂h)` with
both components non-decreasing. -/
theorem correlation_monotone_beta (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) (A : Finset ι) :
    MonotoneOn (fun β : ℝ => correlation G ⟨J, h, β⟩ A) (Set.Ioi 0) := by
  intro β₁ hβ₁ β₂ _ hβ
  change correlation G ⟨J, h, β₁⟩ A ≤ correlation G ⟨J, h, β₂⟩ A
  rw [correlation_rescale_beta G J h β₁ A,
      correlation_rescale_beta G J h β₂ A]
  have hβ₁' : 0 < β₁ := hβ₁
  have hβ₂' : 0 < β₂ := lt_of_lt_of_le hβ₁' hβ
  have hβ₁J : 0 ≤ β₁ * J := mul_nonneg hβ₁'.le hJ
  have hβ₂J : 0 ≤ β₂ * J := mul_nonneg hβ₂'.le hJ
  have hβ₁h : 0 ≤ β₁ * h := mul_nonneg hβ₁'.le hh
  have hβ₂h : 0 ≤ β₂ * h := mul_nonneg hβ₂'.le hh
  calc correlation G ⟨β₁ * J, β₁ * h, 1⟩ A
      ≤ correlation G ⟨β₂ * J, β₁ * h, 1⟩ A :=
        correlation_monotone_J G (β₁ * h) hβ₁h 1 one_pos A
          (Set.mem_Ici.mpr hβ₁J) (Set.mem_Ici.mpr hβ₂J)
          (mul_le_mul_of_nonneg_right hβ hJ)
    _ ≤ correlation G ⟨β₂ * J, β₂ * h, 1⟩ A :=
        correlation_monotone_h G (β₂ * J) hβ₂J 1 one_pos A
          (Set.mem_Ici.mpr hβ₁h) (Set.mem_Ici.mpr hβ₂h)
          (mul_le_mul_of_nonneg_right hβ hh)

/-- **Correlation β-convergence**: for ferromagnetic parameters
(`J ≥ 0`, `h ≥ 0`), the sequence `⟨σ^A⟩_{(J, h, n+1)}` converges as
`n → ∞`. Uses `β = n + 1` to keep `β > 0`.

Proof: Monotone increasing by `correlation_monotone_beta`, bounded above
by `1` via `correlation_le_one`, hence converges by `tendsto_atTop_ciSup`. -/
theorem correlation_convergent_beta (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) (A : Finset ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => correlation G ⟨J, h, (n + 1 : ℝ)⟩ A)
      Filter.atTop (nhds L) := by
  have h_mono : Monotone (fun n : ℕ => correlation G ⟨J, h, (n + 1 : ℝ)⟩ A) := by
    intro a b hab
    have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
    have hb : (0 : ℝ) < (b : ℝ) + 1 := by positivity
    have hab' : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by
      have : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr hab
      linarith
    exact correlation_monotone_beta G J hJ h hh A
      (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr hb) hab'
  have h_bdd : BddAbove (Set.range
      (fun n : ℕ => correlation G ⟨J, h, (n + 1 : ℝ)⟩ A)) :=
    ⟨1, fun _ ⟨n, hn⟩ => hn ▸ correlation_le_one G ⟨J, h, (n + 1 : ℝ)⟩ A⟩
  exact ⟨_, tendsto_atTop_ciSup h_mono h_bdd⟩

/-! ## Convergence as h → ∞

Filling the monotonicity/convergence matrix: we had `J → ∞`
(`correlation_convergent`) and `β → ∞` (`correlation_convergent_beta`);
this section adds `h → ∞` by the same monotone-bounded argument using
`correlation_monotone_h` (Prop 4.2.4). -/

/-- **Correlation h → ∞ convergence**: for ferromagnetic parameters
(`J ≥ 0`, `β > 0`), the sequence `n ↦ ⟨σ^A⟩_{(J, n, β)}` converges as
`n → ∞`.

Proof: Monotone increasing by `correlation_monotone_h` (Prop 4.2.4),
bounded above by `1` via `correlation_le_one`, hence converges by
`tendsto_atTop_ciSup`. -/
theorem correlation_convergent_h (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) (A : Finset ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => correlation G ⟨J, (n : ℝ), β⟩ A)
      Filter.atTop (nhds L) := by
  have h_mono : Monotone (fun n : ℕ => correlation G ⟨J, (n : ℝ), β⟩ A) := by
    intro a b hab
    have ha : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    have hb : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
    exact correlation_monotone_h G J hJ β hβ A
      (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr hb) (by exact_mod_cast hab)
  have h_bdd : BddAbove (Set.range
      (fun n : ℕ => correlation G ⟨J, (n : ℝ), β⟩ A)) :=
    ⟨1, fun _ ⟨n, hn⟩ => hn ▸ correlation_le_one G ⟨J, (n : ℝ), β⟩ A⟩
  exact ⟨_, tendsto_atTop_ciSup h_mono h_bdd⟩

end IsingModel
