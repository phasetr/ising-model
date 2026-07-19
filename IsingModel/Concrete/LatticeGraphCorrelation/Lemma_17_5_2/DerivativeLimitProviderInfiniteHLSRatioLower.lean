import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProviderInfiniteHLSComparison

/-!
# GJ §17.5 Lemma 17.5.2 — provider-based infinite-HLS bridges (ratio-lower layer)

Child module of `DerivativeLimitProviderInfiniteHLS`.  It assembles the
high-temperature ratio-lower infinite-HLS comparison, upper-bound and sandwich
bridges from the comparison core.  Split out purely for build speed; the
declarations are relocated verbatim.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and
  Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

set_option maxHeartbeats 1200000 in
-- The proof chooses one enlarged HLS constant and normalizes both finite
-- ratio-lower and endpoint path-rate inequalities for the concrete profile.
/-- **GJ §17.5 Lemma 17.5.2 concrete infinite-HLS comparison from a
high-temperature ratio lower bound**: under a finite-stage ratio lower bound
for `correlationAlongExhaustion / (m⁻)^(2α)`, choose one enlarged HLS constant
that carries the convolution inequality, the interval infinite-HLS denominator
comparison for the concrete pseudo-mass profile, and the endpoint Step 115
path-rate comparison. -/
theorem
    lemma_17_5_2_concrete_infinite_hls_path_rate_inputs_of_high_temp_ratio_lower_provider
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    {s : Set ℝ} (hs_open : IsOpen s)
    (hs_sub : s ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (hIcc : Set.Icc β₁ β₂ ⊆ s)
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProviderOn s Λ J x z)
    {L : ℝ} (hL_pos : 0 < L)
    (hratio :
      ∀ᶠ n in Filter.atTop,
        ∀ β ∈ Set.Icc β₁ β₂,
          L ≤
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
            (lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z β) ^
              (2 * α)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      (∀ β ∈ Set.Icc β₁ β₂,
        Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β α K
          (lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z)) ∧
      ENNReal.ofReal (-Real.log (Real.tanh (β₂ * J))) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) := by
  obtain ⟨K₀, hK₀, hK₀_conv⟩ := lemma_17_5_2_hls_convolution_constant α d hαd
  let N : ℝ := ((2 * α + 1 : ℕ) : ℝ)
  let m : ℝ :=
    pseudoMassFromParamsAtPair hα hrho d Λ
      (⟨J, 0, β₂⟩ : IsingParams ℝ) x z
  let path : ℝ := -Real.log (Real.tanh (β₂ * J))
  let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
  let B : ℝ := J * M ^ 2 + J * (4 * ↑d)
  let K : ℝ := max K₀ (max (path * rho / (N * m)) (B / L))
  have hβ₂_mem : β₂ ∈ Set.Icc β₁ β₂ := ⟨hβ₁₂, le_rfl⟩
  have hcorrβ₂ :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2 :=
    lemma_17_5_2_active_range_on_Icc_of_high_temp_pair Λ hJ_pos hxz
      (hIcc.trans hs_sub) β₂ hβ₂_mem
  have hN_pos : 0 < N := by
    dsimp [N]
    exact_mod_cast Nat.succ_pos (2 * α)
  have hm_pos : 0 < m := by
    dsimp [m]
    exact pseudoMassFromParamsAtPair_pos_of_corr_mem hα hrho d Λ
      (⟨J, 0, β₂⟩ : IsingParams ℝ) x z hcorrβ₂
  have hK_pos : 0 < K := hK₀.trans_le (le_max_left _ _)
  have hK_conv : ∀ x' y' : Fin d → ℤ,
      ∑' w : Fin d → ℤ,
          (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
          (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K := by
    intro x' y'
    exact (hK₀_conv x' y').trans (le_max_left _ _)
  have hpath_scale : path * rho / (N * m) ≤ K :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hpath_real : path ≤ (N * K / rho) * m := by
    have hNm_pos : 0 < N * m := mul_pos hN_pos hm_pos
    have hmul_le : path * rho ≤ K * (N * m) := by
      have h := mul_le_mul_of_nonneg_right hpath_scale hNm_pos.le
      rwa [div_mul_cancel₀ (path * rho) hNm_pos.ne'] at h
    have hdiv_le : path ≤ K * (N * m) / rho := by
      have h := div_le_div_of_nonneg_right hmul_le hrho.le
      rwa [mul_div_cancel_right₀ path hrho.ne'] at h
    calc
      path ≤ K * (N * m) / rho := hdiv_le
      _ = (N * K / rho) * m := by ring
  have hpath_enn :
      ENNReal.ofReal path ≤ ENNReal.ofReal (N * K / rho) * ENNReal.ofReal m := by
    have hcoeff_nonneg : 0 ≤ N * K / rho :=
      div_nonneg (mul_nonneg hN_pos.le hK_pos.le) hrho.le
    have h := ENNReal.ofReal_le_ofReal hpath_real
    rw [ENNReal.ofReal_mul hcoeff_nonneg] at h
    exact h
  have hB_le_KL : B ≤ K * L := by
    have hscale : B / L ≤ K :=
      (le_max_right _ _).trans (le_max_right _ _)
    have h := mul_le_mul_of_nonneg_right hscale hL_pos.le
    rwa [div_mul_cancel₀ B hL_pos.ne'] at h
  have habs :=
    lemma_17_5_2_finite_deriv_abs_le_high_temp_on_Icc
      (d := d) Λ J hJ_pos.le ha hab hlt hβ_mem hxz
  have hscalar :
      ∀ᶠ n in Filter.atTop,
        ∀ β ∈ Set.Icc β₁ β₂,
          let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
          J * M ^ 2 + J * (4 * ↑d) ≤
            K *
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
              (lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z β) ^
                (2 * α) := by
    filter_upwards [hratio] with n hratio_n β hβ
    calc
      J * (b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))) ^ 2 + J * (4 * ↑d)
          = B := by rfl
      _ ≤ K * L := hB_le_KL
      _ ≤ K *
          (Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
            (lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z β) ^
              (2 * α)) :=
          mul_le_mul_of_nonneg_left (hratio_n β hβ) hK_pos.le
      _ = K *
          Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
          (lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z β) ^
            (2 * α) := by ring
  have hfinite :
      ∀ᶠ n in Filter.atTop,
        ∀ β ∈ Set.Icc β₁ β₂,
          |deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
            K *
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
              (lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z β) ^
                (2 * α) := by
    filter_upwards [habs, hscalar] with n habs_n hscalar_n β hβ
    exact (habs_n β hβ).trans (by simpa using hscalar_n β hβ)
  have hcomp :
      ∀ β ∈ Set.Icc β₁ β₂,
        Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β α K
          (lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z) :=
    lemma_17_5_2_infinite_hls_comparison_on_Icc_of_uniform_finite_deriv_bounds_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (K := K)
      (h := lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z)
      hd hJ_pos hxz hs_open hs_sub hIcc hderiv_provider hfinite
  exact ⟨K, hK_pos, hK_conv, hcomp, by simpa [N, m, path] using hpath_enn⟩

set_option maxHeartbeats 1200000 in
-- This combines the ratio-lower comparison package with the fixed-constant
-- concrete upper-bound bridge.
/-- **GJ §17.5 Lemma 17.5.2 concrete upper bound from a high-temperature ratio
lower bound**: the finite-stage ratio lower bound supplies the concrete
interval denominator comparisons and endpoint path-rate comparison; the
fixed-constant concrete bridge then closes the named upper-bound predicate. -/
theorem lemma_17_5_2_upper_bound_of_concrete_infinite_hls_ratio_lower_provider
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    {s : Set ℝ} (hs_open : IsOpen s)
    (hs_sub : s ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (hIcc : Set.Icc β₁ β₂ ⊆ s)
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProviderOn s Λ J x z)
    {L : ℝ} (hL_pos : 0 < L)
    (hratio :
      ∀ᶠ n in Filter.atTop,
        ∀ β ∈ Set.Icc β₁ β₂,
          L ≤
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
            (lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z β) ^
              (2 * α)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) := by
  obtain ⟨K, hK, hK_conv, _hcomp, hpath⟩ :=
    lemma_17_5_2_concrete_infinite_hls_path_rate_inputs_of_high_temp_ratio_lower_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho)
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hs_open hs_sub hIcc ha hab hlt hβ_mem
      hderiv_provider hL_pos hratio
  refine ⟨K, hK, hK_conv, ?_⟩
  exact
    lemma_17_5_2_upper_bound_of_concrete_infinite_hls_inputs_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (K := K) (rho := rho)
      hα hd hrho hJ_pos hxz hβ₁₂ hs_open hs_sub hIcc hderiv_provider hpath

set_option maxHeartbeats 1200000 in
-- This is the two-sided form of the preceding ratio-lower upper-bound bridge.
/-- **GJ §17.5 Lemma 17.5.2 concrete sandwich from a high-temperature ratio
lower bound**: the ratio-lower package supplies the concrete infinite-HLS
upper-bound side, and the validating pseudo-mass decay input supplies the lower
side for the same constant. -/
theorem lemma_17_5_2_sandwich_of_concrete_infinite_hls_ratio_lower_provider
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z))
    {L : ℝ} (hL_pos : 0 < L)
    (hratio :
      ∀ᶠ n in Filter.atTop,
        ∀ β ∈ Set.Icc β₁ β₂,
          L ≤
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
            (lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z β) ^
              (2 * α)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) := by
  obtain ⟨K, hK, hK_conv, hupper⟩ :=
    lemma_17_5_2_upper_bound_of_concrete_infinite_hls_ratio_lower_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho)
      hα hαd hd hrho hJ_pos hxz hβ₁₂ isOpen_Ioo (subset_refl _) hIcc ha hab hlt hβ_mem
      hderiv_provider hL_pos hratio
  refine ⟨K, hK, hK_conv, ?_⟩
  exact lemma_17_5_2_sandwich_of_decay_and_upper hα hrho hdecay hupper

set_option maxHeartbeats 1200000 in
-- Uniform infinite-correlation and denominator bounds imply the ratio-lower
-- premise consumed by the preceding concrete infinite-HLS bridge.
/-- **GJ §17.5 Lemma 17.5.2 concrete upper bound from a uniform infinite
correlation lower bound**: a positive uniform lower bound for the infinite
two-point function and a concrete pseudo-mass denominator upper bound supply the
ratio-lower input for the concrete infinite-HLS upper-bound bridge. -/
theorem
    lemma_17_5_2_upper_bound_of_concrete_infinite_hls_uniform_correlation_lower_provider
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    {s : Set ℝ} (hs_open : IsOpen s)
    (hs_sub : s ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (hIcc : Set.Icc β₁ β₂ ⊆ s)
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProviderOn s Λ J x z)
    {C H : ℝ} (hC_pos : 0 < C) (hH_pos : 0 < H)
    (hcInf_lower : ∀ β ∈ Set.Icc β₁ β₂,
      C ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z})
    (hdenom_bound : ∀ β ∈ Set.Icc β₁ β₂,
      (lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z β) ^
        (2 * α) ≤ H) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) := by
  have hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2 :=
    lemma_17_5_2_active_range_on_Icc_of_high_temp_pair Λ hJ_pos hxz (hIcc.trans hs_sub)
  have hh_pos : ∀ β ∈ Set.Icc β₁ β₂,
      0 < lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z β := by
    intro β hβ
    exact pseudoMassFromParamsAtPair_pos_of_corr_mem hα hrho d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z (hcorr β hβ)
  obtain ⟨L, hL_pos, hratio⟩ :=
    lemma_17_5_2_ratio_lower_of_uniform_correlation_on_beta_interval
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b)
      (h := lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z)
      hJ_pos.le hxz ha hab hlt hβ_mem hC_pos hH_pos hcInf_lower
      (fun β hβ => pow_pos (hh_pos β hβ) (2 * α)) hdenom_bound
  exact
    lemma_17_5_2_upper_bound_of_concrete_infinite_hls_ratio_lower_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho)
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hs_open hs_sub hIcc ha hab hlt hβ_mem
      hderiv_provider hL_pos hratio

set_option maxHeartbeats 1200000 in
-- Add the validating pseudo-mass decay lower side to the preceding upper-bound
-- package.
/-- **GJ §17.5 Lemma 17.5.2 concrete sandwich from a uniform infinite
correlation lower bound**: the uniform lower/denominator bounds supply the
concrete infinite-HLS upper-bound side, while the validating pseudo-mass decay
input supplies the lower side. -/
theorem
    lemma_17_5_2_sandwich_of_concrete_infinite_hls_uniform_correlation_lower_provider
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z))
    {C H : ℝ} (hC_pos : 0 < C) (hH_pos : 0 < H)
    (hcInf_lower : ∀ β ∈ Set.Icc β₁ β₂,
      C ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z})
    (hdenom_bound : ∀ β ∈ Set.Icc β₁ β₂,
      (lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z β) ^
        (2 * α) ≤ H) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) := by
  obtain ⟨K, hK, hK_conv, hupper⟩ :=
    lemma_17_5_2_upper_bound_of_concrete_infinite_hls_uniform_correlation_lower_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho)
      hα hαd hd hrho hJ_pos hxz hβ₁₂ isOpen_Ioo (subset_refl _) hIcc ha hab hlt hβ_mem
      hderiv_provider hC_pos hH_pos hcInf_lower hdenom_bound
  refine ⟨K, hK, hK_conv, ?_⟩
  exact lemma_17_5_2_sandwich_of_decay_and_upper hα hrho hdecay hupper

set_option maxHeartbeats 1200000 in
-- Specializes the auxiliary compact interval in the uniform-correlation
-- lower bridge to the beta interval itself.
/-- **GJ §17.5 Lemma 17.5.2 self-interval concrete infinite-HLS upper bound
from a uniform infinite-correlation lower bound**: the closed beta interval
itself supplies the compact high-temperature interval for the ratio-lower
input. -/
theorem
    lemma_17_5_2_upper_bound_of_concrete_infinite_hls_uniform_correlation_lower_provider_on_self_Icc
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
    {C H : ℝ} (hC_pos : 0 < C) (hH_pos : 0 < H)
    (hcInf_lower : ∀ β ∈ Set.Icc β₁ β₂,
      C ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z})
    (hdenom_bound : ∀ β ∈ Set.Icc β₁ β₂,
      (lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z β) ^
        (2 * α) ≤ H) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) := by
  obtain ⟨hβ₁_pos, _hβ₂_pos, hβ₂_lt⟩ :=
    lemma_17_5_2_interval_endpoints_of_Icc_subset_high_temp
      hd hJ_pos hβ₁₂ hIcc
  exact
    lemma_17_5_2_upper_bound_of_concrete_infinite_hls_uniform_correlation_lower_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := β₁) (b := β₂) (rho := rho)
      hα hαd hd hrho hJ_pos hxz hβ₁₂ isOpen_Ioo (subset_refl _) hIcc hβ₁_pos hβ₁₂ hβ₂_lt
      (fun β hβ => hβ) hderiv_provider hC_pos hH_pos hcInf_lower
      hdenom_bound

set_option maxHeartbeats 1200000 in
-- Adds the validating pseudo-mass decay lower side to the self-interval
-- uniform-correlation lower upper-bound package.
/-- **GJ §17.5 Lemma 17.5.2 self-interval concrete infinite-HLS sandwich from
a uniform infinite-correlation lower bound**: combines the self-interval
uniform-correlation upper-bound bridge with the validating pseudo-mass decay
lower side. -/
theorem
    lemma_17_5_2_sandwich_of_concrete_infinite_hls_uniform_correlation_lower_provider_on_self_Icc
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z))
    {C H : ℝ} (hC_pos : 0 < C) (hH_pos : 0 < H)
    (hcInf_lower : ∀ β ∈ Set.Icc β₁ β₂,
      C ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z})
    (hdenom_bound : ∀ β ∈ Set.Icc β₁ β₂,
      (lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z β) ^
        (2 * α) ≤ H) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) := by
  obtain ⟨K, hK, hK_conv, hupper⟩ :=
    lemma_17_5_2_upper_bound_of_concrete_infinite_hls_uniform_correlation_lower_provider_on_self_Icc
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho)
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc hderiv_provider
      hC_pos hH_pos hcInf_lower hdenom_bound
  refine ⟨K, hK, hK_conv, ?_⟩
  exact lemma_17_5_2_sandwich_of_decay_and_upper hα hrho hdecay hupper

/-- **GJ §17.5 Lemma 17.5.2 concrete infinite-HLS capstone from a uniform
infinite-correlation lower bound**: returns the HLS convolution witness, the
named upper-bound predicate, and the displayed two-sided endpoint sandwich for
one constant. -/
theorem
    lemma_17_5_2_capstone_of_concrete_infinite_hls_uniform_correlation_lower_provider
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z))
    {C H : ℝ} (hC_pos : 0 < C) (hH_pos : 0 < H)
    (hcInf_lower : ∀ β ∈ Set.Icc β₁ β₂,
      C ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z})
    (hdenom_bound : ∀ β ∈ Set.Icc β₁ β₂,
      (lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z β) ^
        (2 * α) ≤ H) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) := by
  obtain ⟨K, hK_pos, hconv, hlower, hupper_ineq⟩ :=
    lemma_17_5_2_sandwich_of_concrete_infinite_hls_uniform_correlation_lower_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho)
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem
      hderiv_provider hdecay hC_pos hH_pos hcInf_lower hdenom_bound
  have hupper :
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) := by
    simpa [Lemma_17_5_2_UpperBound] using hupper_ineq
  exact ⟨K, hK_pos, hconv, hupper, hlower, hupper_ineq⟩

/-- **GJ §17.5 Lemma 17.5.2 self-interval concrete infinite-HLS capstone from
a uniform infinite-correlation lower bound**: specializes the auxiliary compact
interval to the beta interval itself. -/
theorem
    lemma_17_5_2_capstone_of_concrete_infinite_hls_uniform_correlation_lower_provider_on_self_Icc
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z))
    {C H : ℝ} (hC_pos : 0 < C) (hH_pos : 0 < H)
    (hcInf_lower : ∀ β ∈ Set.Icc β₁ β₂,
      C ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z})
    (hdenom_bound : ∀ β ∈ Set.Icc β₁ β₂,
      (lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z β) ^
        (2 * α) ≤ H) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) := by
  obtain ⟨K, hK_pos, hconv, hlower, hupper_ineq⟩ :=
    lemma_17_5_2_sandwich_of_concrete_infinite_hls_uniform_correlation_lower_provider_on_self_Icc
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho)
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc hderiv_provider hdecay
      hC_pos hH_pos hcInf_lower hdenom_bound
  have hupper :
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) := by
    simpa [Lemma_17_5_2_UpperBound] using hupper_ineq
  exact ⟨K, hK_pos, hconv, hupper, hlower, hupper_ineq⟩

end Ambient
end IsingModel
