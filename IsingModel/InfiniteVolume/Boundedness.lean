import IsingModel.Inequalities.GKS

/-!
# Infinite-volume correlations split — spin-product boundedness and Walsh orthogonality

Part of the split infinite-volume correlation layer (Issue #1850).
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


end IsingModel
