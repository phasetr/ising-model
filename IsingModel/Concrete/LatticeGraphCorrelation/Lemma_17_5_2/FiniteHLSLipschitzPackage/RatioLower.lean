import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.FiniteHLSLipschitzPackage.Enlarged

/-!
# GJ §17.5 Lemma 17.5.2 finite-HLS Lipschitz package -- ratio lower wrappers

Part of the split `FiniteHLSLipschitzPackage` layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

/-- **GJ §17.5 Lemma 17.5.2 ratio lower from uniform finite-volume
convergence**: if finite correlations converge uniformly to the infinite
correlation on an interval, the infinite correlation has a positive uniform
lower bound `C`, and the pseudo-mass denominator is uniformly bounded above by
`H`, then the finite ratio `corr_n / h^(2α)` has an eventual positive uniform
lower bound on the same interval. -/
theorem lemma_17_5_2_ratio_lower_of_uniform_correlation_limit
    {α : ℕ} {s : Set ℝ} {cN : ℕ → ℝ → ℝ} {cInf h : ℝ → ℝ}
    {C H : ℝ} (hC_pos : 0 < C) (hH_pos : 0 < H)
    (hconv : TendstoUniformlyOn cN cInf Filter.atTop s)
    (hcInf_lower : ∀ β ∈ s, C ≤ cInf β)
    (hdenom_pos : ∀ β ∈ s, 0 < (h β) ^ (2 * α))
    (hdenom_bound : ∀ β ∈ s, (h β) ^ (2 * α) ≤ H) :
    ∃ L : ℝ, 0 < L ∧
      ∀ᶠ n in Filter.atTop,
        ∀ β ∈ s, L ≤ cN n β / (h β) ^ (2 * α) := by
  let L : ℝ := (C / 2) / H
  have hC_half_pos : 0 < C / 2 := half_pos hC_pos
  have hL_pos : 0 < L := div_pos hC_half_pos hH_pos
  have hconv_half :
      ∀ᶠ n in Filter.atTop,
        ∀ β ∈ s, dist (cInf β) (cN n β) < C / 2 :=
    (Metric.tendstoUniformlyOn_iff.mp hconv) (C / 2) hC_half_pos
  refine ⟨L, hL_pos, ?_⟩
  filter_upwards [hconv_half] with n hn β hβ
  have hdist : |cInf β - cN n β| < C / 2 := by
    simpa [Real.dist_eq] using hn β hβ
  have hdiff_lt : cInf β - cN n β < C / 2 :=
    (le_abs_self (cInf β - cN n β)).trans_lt hdist
  have hcN_lower : C / 2 ≤ cN n β := by
    have hc := hcInf_lower β hβ
    linarith
  have hleft :
      L ≤ (C / 2) / (h β) ^ (2 * α) := by
    dsimp [L]
    exact div_le_div_of_nonneg_left hC_half_pos.le (hdenom_pos β hβ)
      (hdenom_bound β hβ)
  have hright :
      (C / 2) / (h β) ^ (2 * α) ≤ cN n β / (h β) ^ (2 * α) :=
    div_le_div_of_nonneg_right hcN_lower (hdenom_pos β hβ).le
  exact hleft.trans hright

/-- **GJ §17.5 Lemma 17.5.2 concrete beta-interval ratio lower**:
specialize the abstract uniform-limit ratio lower to lattice correlations on a
closed beta interval inside a high-temperature interval. -/
theorem lemma_17_5_2_ratio_lower_of_uniform_correlation_on_beta_interval
    {d α : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ : 0 ≤ J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    {h : ℝ → ℝ} {C H : ℝ} (hC_pos : 0 < C) (hH_pos : 0 < H)
    (hcInf_lower : ∀ β ∈ Set.Icc β₁ β₂,
      C ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z})
    (hdenom_pos : ∀ β ∈ Set.Icc β₁ β₂, 0 < (h β) ^ (2 * α))
    (hdenom_bound : ∀ β ∈ Set.Icc β₁ β₂, (h β) ^ (2 * α) ≤ H) :
    ∃ L : ℝ, 0 < L ∧
      ∀ᶠ n in Filter.atTop,
        ∀ β ∈ Set.Icc β₁ β₂,
          L ≤
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
            (h β) ^ (2 * α) := by
  have hconv_ab :=
    correlationAlongExhaustion_tendstoUniformlyOn_beta
      Λ x z hxz J hJ a b ha hab hlt
  have hconv :
      TendstoUniformlyOn
        (fun n β =>
          Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n)
        (fun β =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z})
        Filter.atTop (Set.Icc β₁ β₂) :=
    hconv_ab.mono hβ_mem
  exact
    lemma_17_5_2_ratio_lower_of_uniform_correlation_limit
      (α := α)
      (cN := fun n β =>
        Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n)
      (cInf := fun β =>
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z})
      (h := h) hC_pos hH_pos hconv hcInf_lower hdenom_pos hdenom_bound

/-- **GJ §17.5 Lemma 17.5.2 self-interval concrete ratio lower from a
uniform infinite-correlation lower bound**: the beta interval itself supplies
the compact high-temperature interval used to turn uniform convergence into
the eventual finite ratio lower bound. -/
theorem lemma_17_5_2_ratio_lower_of_uniform_correlation_on_self_Icc
    {d α : ℕ} (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {h : ℝ → ℝ} {C H : ℝ} (hC_pos : 0 < C) (hH_pos : 0 < H)
    (hcInf_lower : ∀ β ∈ Set.Icc β₁ β₂,
      C ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z})
    (hdenom_pos : ∀ β ∈ Set.Icc β₁ β₂, 0 < (h β) ^ (2 * α))
    (hdenom_bound : ∀ β ∈ Set.Icc β₁ β₂, (h β) ^ (2 * α) ≤ H) :
    ∃ L : ℝ, 0 < L ∧
      ∀ᶠ n in Filter.atTop,
        ∀ β ∈ Set.Icc β₁ β₂,
          L ≤
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
            (h β) ^ (2 * α) := by
  obtain ⟨hβ₁_pos, _hβ₂_pos, hβ₂_lt⟩ :=
    lemma_17_5_2_interval_endpoints_of_Icc_subset_high_temp
      hd hJ_pos hβ₁₂ hIcc
  exact
    lemma_17_5_2_ratio_lower_of_uniform_correlation_on_beta_interval
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := β₁) (b := β₂) (h := h)
      hJ_pos.le hxz hβ₁_pos hβ₁₂ hβ₂_lt (fun β hβ => hβ)
      hC_pos hH_pos hcInf_lower hdenom_pos hdenom_bound

/-- **GJ §17.5 Lemma 17.5.2 compact positive lower bound**: a continuous
positive real-valued function on a nonempty closed interval has a positive
uniform lower bound. -/
theorem lemma_17_5_2_compact_pos_lower_bound_on_Icc
    {f : ℝ → ℝ} {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hf_cont : ContinuousOn f (Set.Icc β₁ β₂))
    (hf_pos : ∀ β ∈ Set.Icc β₁ β₂, 0 < f β) :
    ∃ C : ℝ, 0 < C ∧ ∀ β ∈ Set.Icc β₁ β₂, C ≤ f β := by
  obtain ⟨β₀, hβ₀, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hβ₁₂) hf_cont
  refine ⟨f β₀, hf_pos β₀ hβ₀, ?_⟩
  exact isMinOn_iff.mp hmin

/-- **GJ §17.5 Lemma 17.5.2 compact denominator upper bound**: a continuous
nonnegative pseudo-mass profile on a nonempty closed interval has a positive
uniform upper bound for `h^(2α)`. -/
theorem lemma_17_5_2_compact_pow_upper_bound_on_Icc
    {α : ℕ} {h : ℝ → ℝ} {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hh_cont : ContinuousOn h (Set.Icc β₁ β₂))
    (hh_nonneg : ∀ β ∈ Set.Icc β₁ β₂, 0 ≤ h β) :
    ∃ H : ℝ, 0 < H ∧ ∀ β ∈ Set.Icc β₁ β₂, (h β) ^ (2 * α) ≤ H := by
  have hpow_cont : ContinuousOn (fun β => (h β) ^ (2 * α)) (Set.Icc β₁ β₂) :=
    hh_cont.pow (2 * α)
  obtain ⟨β₀, hβ₀, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hβ₁₂) hpow_cont
  let H : ℝ := (h β₀) ^ (2 * α) + 1
  have hpow_nonneg : 0 ≤ (h β₀) ^ (2 * α) := pow_nonneg (hh_nonneg β₀ hβ₀) _
  refine ⟨H, by linarith, ?_⟩
  intro β hβ
  have hle : (h β) ^ (2 * α) ≤ (h β₀) ^ (2 * α) := isMaxOn_iff.mp hmax β hβ
  dsimp [H]
  linarith

/-- **GJ §17.5 Lemma 17.5.2 compact interval bounds for the ratio lower**:
on a closed beta interval inside the high-temperature region, continuity and
pointwise positivity of `corr_infty` provide the positive lower bound `C`, while
continuity and nonnegativity of the denominator profile provide the positive
upper bound `H` for `h^(2α)`. -/
theorem lemma_17_5_2_compact_ratio_bounds_on_beta_interval
    {d α : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ : 0 ≤ J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    {h : ℝ → ℝ}
    (hh_cont : ContinuousOn h (Set.Icc β₁ β₂))
    (hh_nonneg : ∀ β ∈ Set.Icc β₁ β₂, 0 ≤ h β)
    (hc_pos : ∀ β ∈ Set.Icc β₁ β₂,
      0 <
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    ∃ C H : ℝ, 0 < C ∧ 0 < H ∧
      (∀ β ∈ Set.Icc β₁ β₂,
        C ≤
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) ∧
      (∀ β ∈ Set.Icc β₁ β₂, (h β) ^ (2 * α) ≤ H) := by
  have hc_cont_ab :=
    correlationInfinite_continuousOn_beta_of_high_temp
      Λ x z hxz J hJ a b ha hab hlt
  have hc_cont :
      ContinuousOn
        (fun β =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z})
        (Set.Icc β₁ β₂) :=
    hc_cont_ab.mono hβ_mem
  obtain ⟨C, hC_pos, hc_lower⟩ :=
    lemma_17_5_2_compact_pos_lower_bound_on_Icc hβ₁₂ hc_cont hc_pos
  obtain ⟨H, hH_pos, hdenom_bound⟩ :=
    lemma_17_5_2_compact_pow_upper_bound_on_Icc (α := α) hβ₁₂ hh_cont hh_nonneg
  exact ⟨C, H, hC_pos, hH_pos, hc_lower, hdenom_bound⟩

set_option maxHeartbeats 2000000 in
-- The package selects one enlarged constant and normalizes several large
-- interval-uniform derivative and all-rate premises at once.
/-- **GJ §17.5 Lemma 17.5.2 upper bound from a high-temperature ratio lower
bound**: choose a single HLS constant large enough to carry the convolution
bound, dominate the Step 115 path rate, and dominate the high-temperature
Lebowitz/susceptibility scalar bound through an eventual lower bound on
`correlationAlongExhaustion / h^(2α)`. -/
theorem lemma_17_5_2_upper_bound_of_high_temp_ratio_lower
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    {rho : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ} (g' : ℝ → ℝ)
    (hh_diff : ∀ β' ∈ Set.Icc β₁ β₂, HasDerivAt h (deriv h β') β')
    (hh_nonneg : ∀ β' ∈ Set.Icc β₁ β₂, 0 ≤ h β')
    (hg_eq : ∀ β' ∈ Set.Icc β₁ β₂,
      (fun γ => pseudoMassG α rho (h γ)) =ᶠ[nhds β']
        (fun γ =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, γ⟩ : IsingParams ℝ) {x, z}))
    (hh_pos : ∀ β' ∈ Set.Icc β₁ β₂, 0 < h β')
    (hc_pos : ∀ β' ∈ Set.Icc β₁ β₂,
      0 <
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (hm_pos :
      0 <
        pseudoMassFromParamsAtPair hα hrho d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    {L : ℝ} (hL_pos : 0 < L)
    (hratio :
      ∀ᶠ n in Filter.atTop,
        ∀ β ∈ Set.Icc β₁ β₂,
          L ≤
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
            (h β) ^ (2 * α)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) := by
  let cInf : ℝ → ℝ := fun β' =>
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}
  have hc_diff : ∀ β' ∈ Set.Icc β₁ β₂,
      HasDerivAt cInf (deriv cInf β') β' := by
    intro β hβ
    have hcdiff_g :=
      correlationInfinite_hasDerivAt_beta_of_tendstoLocallyUniformlyOn_deriv
        (d := d) (Λ := Λ) (r_val := x) (s_val := z) (J := J) (g' := g')
        hd hxz hJ_pos hderiv_lim β (hIcc hβ)
    have hderiv_eq : deriv cInf β = g' β := hcdiff_g.deriv
    simpa [cInf, hderiv_eq] using hcdiff_g
  obtain ⟨K₀, hK₀, hK₀_conv⟩ := lemma_17_5_2_hls_convolution_constant α d hαd
  let N : ℝ := ((2 * α + 1 : ℕ) : ℝ)
  let m : ℝ :=
    pseudoMassFromParamsAtPair hα hrho d Λ
      (⟨J, 0, β₂⟩ : IsingParams ℝ) x z
  let path : ℝ := -Real.log (Real.tanh (β₂ * J))
  let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
  let B : ℝ := J * M ^ 2 + J * (4 * ↑d)
  let K : ℝ := max K₀ (max (path * rho / (N * m)) (B / L))
  have hN_pos : 0 < N := by
    dsimp [N]
    exact_mod_cast Nat.succ_pos (2 * α)
  have hm_pos' : 0 < m := by
    dsimp [m]
    exact hm_pos
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
    have hNm_pos : 0 < N * m := mul_pos hN_pos hm_pos'
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
  have hscalar :
      ∀ᶠ n in Filter.atTop,
        ∀ β ∈ Set.Icc β₁ β₂,
          let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
          J * M ^ 2 + J * (4 * ↑d) ≤
            K *
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
              (h β) ^ (2 * α) := by
    filter_upwards [hratio] with n hratio_n β hβ
    calc
      J * (b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))) ^ 2 + J * (4 * ↑d)
          = B := by rfl
      _ ≤ K * L := hB_le_KL
      _ ≤ K *
          (Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
            (h β) ^ (2 * α)) :=
          mul_le_mul_of_nonneg_left (hratio_n β hβ) hK_pos.le
      _ = K *
          Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
          (h β) ^ (2 * α) := by ring
  have hfinite :
      ∀ᶠ n in Filter.atTop,
        ∀ β ∈ Set.Icc β₁ β₂,
          |deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
            K *
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
              (h β) ^ (2 * α) :=
    lemma_17_5_2_finite_deriv_bound_of_high_temp_scalar_bound
      (d := d) (α := α) (Λ := Λ) (J := J) (a := a) (b := b)
      (β₁ := β₁) (β₂ := β₂) (x := x) (z := z) (h := h) (K := K)
      hJ_pos.le ha hab hlt hβ_mem hxz hscalar
  have hlip :
      (∀ᶠ n in Filter.atTop,
          ∀ β ∈ Set.Icc β₁ β₂,
            |deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
              K *
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
                (h β) ^ (2 * α)) →
        |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
          ↑(2 * α + 1) * K / rho * (β₂ - β₁) := by
    intro hfinite'
    exact pseudoMass_pow_succ_lipschitz α hrho hβ₁₂ hh_diff hc_diff hh_nonneg
      hg_eq hh_pos hc_pos
      (lemma_17_5_2_infinite_hls_denominator_comparison_on_Icc_of_uniform_finite_deriv_bounds
        hd Λ J hJ_pos x z hxz β₁ β₂ K hIcc h g' hderiv_lim hfinite')
  have hβ₂_pos : 0 < β₂ := (hIcc (Set.right_mem_Icc.mpr hβ₁₂)).1
  have hd_pos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  have hbridge :
      Lemma_17_5_2_InfiniteHLSLipschitzAllRateBridge
        hα hrho Λ J x z β₁ β₂ K h :=
    lemma_17_5_2_infinite_hls_lipschitz_all_rate_bridge_of_path_rate_le_hls
      hα hrho hd_pos Λ hJ_pos hβ₂_pos x z h
      (by simpa [N, m, path] using hpath_enn)
  exact ⟨K, hK_pos, hK_conv,
    lemma_17_5_2_upper_bound_of_infinite_hls_lipschitz_all_rate_bridge
      hα hrho Λ J x z β₁ β₂ K h (fun _ => hlip hfinite) hbridge⟩

set_option maxHeartbeats 2000000 in
-- This wrapper reuses the large upper-bound package and preserves the same
-- ratio-lower hypotheses while adding the lower validating-decay side.
/-- **GJ §17.5 Lemma 17.5.2 sandwich from a high-temperature ratio lower
bound**: combine the high-temperature ratio-lower upper-bound package with the
validating pseudo-mass decay lower side. -/
theorem lemma_17_5_2_sandwich_of_high_temp_ratio_lower
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    {rho : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ} (g' : ℝ → ℝ)
    (hh_diff : ∀ β' ∈ Set.Icc β₁ β₂, HasDerivAt h (deriv h β') β')
    (hh_nonneg : ∀ β' ∈ Set.Icc β₁ β₂, 0 ≤ h β')
    (hg_eq : ∀ β' ∈ Set.Icc β₁ β₂,
      (fun γ => pseudoMassG α rho (h γ)) =ᶠ[nhds β']
        (fun γ =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, γ⟩ : IsingParams ℝ) {x, z}))
    (hh_pos : ∀ β' ∈ Set.Icc β₁ β₂, 0 < h β')
    (hc_pos : ∀ β' ∈ Set.Icc β₁ β₂,
      0 <
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (hm_pos :
      0 <
        pseudoMassFromParamsAtPair hα hrho d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
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
            (h β) ^ (2 * α)) :
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
    lemma_17_5_2_upper_bound_of_high_temp_ratio_lower
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem hrho g'
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hm_pos hderiv_lim hL_pos hratio
  exact ⟨K, hK, hK_conv,
    lemma_17_5_2_sandwich_of_decay_and_upper hα hrho hdecay hupper⟩

set_option maxHeartbeats 2000000 in
-- This wrapper composes the uniform-limit ratio package with the existing
-- enlarged high-temperature upper-bound assembly.
/-- **GJ §17.5 Lemma 17.5.2 upper bound from a uniform infinite-correlation
lower bound**: derive the interval-uniform finite ratio lower bound from
uniform convergence `corr_n -> corr_infty`, a positive lower bound on
`corr_infty`, and a uniform upper bound on `h^(2α)`, then feed it into the
high-temperature ratio-lower upper-bound package. -/
theorem lemma_17_5_2_upper_bound_of_high_temp_uniform_correlation_lower
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    {rho : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ} (g' : ℝ → ℝ)
    (hh_diff : ∀ β' ∈ Set.Icc β₁ β₂, HasDerivAt h (deriv h β') β')
    (hh_nonneg : ∀ β' ∈ Set.Icc β₁ β₂, 0 ≤ h β')
    (hg_eq : ∀ β' ∈ Set.Icc β₁ β₂,
      (fun γ => pseudoMassG α rho (h γ)) =ᶠ[nhds β']
        (fun γ =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, γ⟩ : IsingParams ℝ) {x, z}))
    (hh_pos : ∀ β' ∈ Set.Icc β₁ β₂, 0 < h β')
    (hc_pos : ∀ β' ∈ Set.Icc β₁ β₂,
      0 <
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (hm_pos :
      0 <
        pseudoMassFromParamsAtPair hα hrho d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    {C H : ℝ} (hC_pos : 0 < C) (hH_pos : 0 < H)
    (hcInf_lower : ∀ β ∈ Set.Icc β₁ β₂,
      C ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z})
    (hdenom_bound : ∀ β ∈ Set.Icc β₁ β₂, (h β) ^ (2 * α) ≤ H) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) := by
  obtain ⟨L, hL_pos, hratio⟩ :=
    lemma_17_5_2_ratio_lower_of_uniform_correlation_on_beta_interval
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (h := h)
      hJ_pos.le hxz ha hab hlt hβ_mem hC_pos hH_pos hcInf_lower
      (fun β hβ => pow_pos (hh_pos β hβ) (2 * α)) hdenom_bound
  exact
    lemma_17_5_2_upper_bound_of_high_temp_ratio_lower
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem hrho g'
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hm_pos hderiv_lim hL_pos hratio

set_option maxHeartbeats 2000000 in
-- This wrapper reuses the preceding large upper-bound package and adds the
-- validating pseudo-mass decay lower side.
/-- **GJ §17.5 Lemma 17.5.2 sandwich from a uniform infinite-correlation lower
bound**: add the validating pseudo-mass decay lower side to
`lemma_17_5_2_upper_bound_of_high_temp_uniform_correlation_lower`. -/
theorem lemma_17_5_2_sandwich_of_high_temp_uniform_correlation_lower
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    {rho : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ} (g' : ℝ → ℝ)
    (hh_diff : ∀ β' ∈ Set.Icc β₁ β₂, HasDerivAt h (deriv h β') β')
    (hh_nonneg : ∀ β' ∈ Set.Icc β₁ β₂, 0 ≤ h β')
    (hg_eq : ∀ β' ∈ Set.Icc β₁ β₂,
      (fun γ => pseudoMassG α rho (h γ)) =ᶠ[nhds β']
        (fun γ =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, γ⟩ : IsingParams ℝ) {x, z}))
    (hh_pos : ∀ β' ∈ Set.Icc β₁ β₂, 0 < h β')
    (hc_pos : ∀ β' ∈ Set.Icc β₁ β₂,
      0 <
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (hm_pos :
      0 <
        pseudoMassFromParamsAtPair hα hrho d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z))
    {C H : ℝ} (hC_pos : 0 < C) (hH_pos : 0 < H)
    (hcInf_lower : ∀ β ∈ Set.Icc β₁ β₂,
      C ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z})
    (hdenom_bound : ∀ β ∈ Set.Icc β₁ β₂, (h β) ^ (2 * α) ≤ H) :
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
    lemma_17_5_2_upper_bound_of_high_temp_uniform_correlation_lower
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem hrho g'
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hm_pos hderiv_lim hC_pos hH_pos
      hcInf_lower hdenom_bound
  exact ⟨K, hK, hK_conv,
    lemma_17_5_2_sandwich_of_decay_and_upper hα hrho hdecay hupper⟩

set_option maxHeartbeats 2000000 in
-- Self-interval form of the uniform-correlation-lower upper-bound package.
/-- **GJ §17.5 Lemma 17.5.2 self-interval upper bound from a uniform
infinite-correlation lower bound**: specializes the auxiliary compact
high-temperature interval in
`lemma_17_5_2_upper_bound_of_high_temp_uniform_correlation_lower` to the beta
interval itself. -/
theorem lemma_17_5_2_upper_bound_of_uniform_correlation_lower_on_self_Icc
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {rho : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ} (g' : ℝ → ℝ)
    (hh_diff : ∀ β' ∈ Set.Icc β₁ β₂, HasDerivAt h (deriv h β') β')
    (hh_nonneg : ∀ β' ∈ Set.Icc β₁ β₂, 0 ≤ h β')
    (hg_eq : ∀ β' ∈ Set.Icc β₁ β₂,
      (fun γ => pseudoMassG α rho (h γ)) =ᶠ[nhds β']
        (fun γ =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, γ⟩ : IsingParams ℝ) {x, z}))
    (hh_pos : ∀ β' ∈ Set.Icc β₁ β₂, 0 < h β')
    (hc_pos : ∀ β' ∈ Set.Icc β₁ β₂,
      0 <
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (hm_pos :
      0 <
        pseudoMassFromParamsAtPair hα hrho d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    {C H : ℝ} (hC_pos : 0 < C) (hH_pos : 0 < H)
    (hcInf_lower : ∀ β ∈ Set.Icc β₁ β₂,
      C ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z})
    (hdenom_bound : ∀ β ∈ Set.Icc β₁ β₂, (h β) ^ (2 * α) ≤ H) :
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
    lemma_17_5_2_upper_bound_of_high_temp_uniform_correlation_lower
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := β₁) (b := β₂) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hβ₁_pos hβ₁₂ hβ₂_lt
      (fun β hβ => hβ) hrho g' hh_diff hh_nonneg hg_eq hh_pos hc_pos
      hm_pos hderiv_lim hC_pos hH_pos hcInf_lower hdenom_bound

set_option maxHeartbeats 2000000 in
-- Self-interval form of the uniform-correlation-lower sandwich package.
/-- **GJ §17.5 Lemma 17.5.2 self-interval sandwich from a uniform
infinite-correlation lower bound**: adds the validating pseudo-mass decay
lower side to
`lemma_17_5_2_upper_bound_of_uniform_correlation_lower_on_self_Icc`. -/
theorem lemma_17_5_2_sandwich_of_uniform_correlation_lower_on_self_Icc
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {rho : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ} (g' : ℝ → ℝ)
    (hh_diff : ∀ β' ∈ Set.Icc β₁ β₂, HasDerivAt h (deriv h β') β')
    (hh_nonneg : ∀ β' ∈ Set.Icc β₁ β₂, 0 ≤ h β')
    (hg_eq : ∀ β' ∈ Set.Icc β₁ β₂,
      (fun γ => pseudoMassG α rho (h γ)) =ᶠ[nhds β']
        (fun γ =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, γ⟩ : IsingParams ℝ) {x, z}))
    (hh_pos : ∀ β' ∈ Set.Icc β₁ β₂, 0 < h β')
    (hc_pos : ∀ β' ∈ Set.Icc β₁ β₂,
      0 <
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
    (hm_pos :
      0 <
        pseudoMassFromParamsAtPair hα hrho d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z))
    {C H : ℝ} (hC_pos : 0 < C) (hH_pos : 0 < H)
    (hcInf_lower : ∀ β ∈ Set.Icc β₁ β₂,
      C ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z})
    (hdenom_bound : ∀ β ∈ Set.Icc β₁ β₂, (h β) ^ (2 * α) ≤ H) :
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
    lemma_17_5_2_upper_bound_of_uniform_correlation_lower_on_self_Icc
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hrho g' hh_diff hh_nonneg hg_eq
      hh_pos hc_pos hm_pos hderiv_lim hC_pos hH_pos hcInf_lower hdenom_bound
  exact ⟨K, hK, hK_conv,
    lemma_17_5_2_sandwich_of_decay_and_upper hα hrho hdecay hupper⟩

end Ambient
end IsingModel
