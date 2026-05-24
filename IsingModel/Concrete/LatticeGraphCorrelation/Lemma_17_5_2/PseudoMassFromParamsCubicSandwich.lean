import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsHighTempSandwich
import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassNamedRate
import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassTanhProfile

/-!
# Cubic pseudo-mass self-interval sandwich package for GJ Lemma 17.5.2

This module specializes the concrete self-interval sandwich wrappers to the
anchored cubic exhaustion.  It connects the general concrete beta-interval API
to the existing lightweight cubic named-rate and tanh-profile inputs.
-/

namespace IsingModel

open Set

namespace Ambient

/-- **Pointwise high-temperature scalar bounds from an interval inclusion**:
any beta in a closed interval contained in the high-temperature interval is
positive and satisfies `β * J * 2d < 1`. -/
theorem lemma_17_5_2_high_temp_scalar_of_mem_Icc_subset_high_temp
    {d : ℕ} (hd : 1 ≤ d) {J β₁ β₂ β : ℝ} (hJ_pos : 0 < J)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (hβ_mem : β ∈ Set.Icc β₁ β₂) :
    0 < β ∧ β * J * ↑(2 * d) < 1 := by
  have hβ_open : β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) :=
    hIcc hβ_mem
  refine ⟨hβ_open.1, ?_⟩
  have h2d_pos : 0 < (↑(2 * d) : ℝ) := by
    have h2d_nat : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
    exact_mod_cast h2d_nat
  have hJ2d_pos : 0 < J * ↑(2 * d) := mul_pos hJ_pos h2d_pos
  have hlt : β * (J * ↑(2 * d)) < 1 := by
    exact (lt_div_iff₀ hJ2d_pos).mp hβ_open.2
  simpa [mul_assoc] using hlt

/-- **Interval active range from interval cubic tanh-profile bounds**:
pointwise `cubicTanhProfileBound` on the beta interval supplies the active-range
hypothesis consumed by the concrete pseudo-mass compact/sandwich packages. -/
theorem lemma_17_5_2_cubic_origin_active_range_of_cubicTanhProfileBound_on_Icc
    {d α : ℕ} (hd : 1 ≤ d)
    {J : ℝ} (hJ_pos : 0 < J)
    {z : Fin d → ℤ} (hz : z ≠ 0)
    {β₁ β₂ : ℝ}
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {rho : ℝ} (hrho : 0 < rho)
    (hprofile_tanh : ∀ β ∈ Set.Icc β₁ β₂,
      cubicTanhProfileBound α d rho β J z) :
    ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2 := by
  intro β hβ_mem
  obtain ⟨hβ_pos, hβ_lt⟩ :=
    lemma_17_5_2_high_temp_scalar_of_mem_Icc_subset_high_temp
      hd hJ_pos hIcc hβ_mem
  exact
    correlationInfinite_cubic_pair_mem_Ioo_zero_two_of_cubicTanhProfileBound
      hrho hJ_pos.le hβ_pos hβ_lt hz (hprofile_tanh β hβ_mem)

set_option maxHeartbeats 2000000 in
-- Specializes the self-interval rate-comparison wrapper to the anchored cubic
-- named-rate proposition.
/-- **GJ §17.5 Lemma 17.5.2 anchored cubic self-interval sandwich from the
named high-temperature rate proposition**: the lightweight
`cubicOriginNamedRateLeHighTemp` proposition supplies the endpoint comparison
for the concrete self-interval high-temperature sandwich wrapper. -/
theorem
    lemma_17_5_2_cubic_origin_sandwich_of_named_rate_on_self_Icc
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {J : ℝ} (hJ_pos : 0 < J)
    {z : Fin d → ℤ} (hz : z ≠ 0)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {rho : ℝ} (hrho : 0 < rho) (g' : ℝ → ℝ)
    (hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d)
              (Ambient.cubicExhaustion d)
              (⟨J, 0, β'⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hnamed : cubicOriginNamedRateLeHighTemp hα hrho β₂ J z) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d (Ambient.cubicExhaustion d)
            (⟨J, 0, β₂⟩ : IsingParams ℝ) (0 : Fin d → ℤ) z)
        ≤ latticeMass d (Ambient.cubicExhaustion d)
            (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d (Ambient.cubicExhaustion d)
          (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d (Ambient.cubicExhaustion d)
              (⟨J, 0, β₂⟩ : IsingParams ℝ) (0 : Fin d → ℤ) z) := by
  have hxz : (0 : Fin d → ℤ) ≠ z := fun h => hz h.symm
  have hle_cubic :=
    cubicOriginPseudoMassFromParamsAtPair_le_high_temp_rate_of_cubicOriginNamedRateLeHighTemp
      hα hrho hnamed
  have hle :
      pseudoMassFromParamsAtPair hα hrho d (Ambient.cubicExhaustion d)
          (⟨J, 0, β₂⟩ : IsingParams ℝ) (0 : Fin d → ℤ) z
        ≤ -Real.log (β₂ * J * ↑(2 * d)) := by
    simpa [cubicOriginPseudoMassFromParamsAtPair_eq] using hle_cubic
  exact
    lemma_17_5_2_sandwich_of_concrete_pseudoMass_compact_bounds_and_le_high_temp_rate_on_self_Icc
      (d := d) (α := α) (Λ := Ambient.cubicExhaustion d) (J := J)
      (x := (0 : Fin d → ℤ)) (z := z) (β₁ := β₁) (β₂ := β₂)
      (rho := rho) hα hαd hd hJ_pos hxz hβ₁₂ hIcc hrho g' hcorr
      hderiv_lim hle

set_option maxHeartbeats 2000000 in
-- Specializes the self-interval profile-lower wrapper to the anchored cubic
-- endpoint profile input.
/-- **GJ §17.5 Lemma 17.5.2 anchored cubic self-interval sandwich from an
endpoint cubic profile lower bound**: the endpoint profile inequality supplies
the validating lower decay input for the concrete self-interval sandwich on the
cubic exhaustion. -/
theorem
    lemma_17_5_2_cubic_origin_sandwich_of_profile_lower_on_self_Icc
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {J : ℝ} (hJ_pos : 0 < J)
    {z : Fin d → ℤ} (hz : z ≠ 0)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {rho : ℝ} (hrho : 0 < rho) (g' : ℝ → ℝ)
    (hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d)
              (Ambient.cubicExhaustion d)
              (⟨J, 0, β'⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hprofile :
      pseudoMassG α rho (-Real.log (β₂ * J * ↑(2 * d))) ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β₂⟩ : IsingParams ℝ)
            {(0 : Fin d → ℤ), z}) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d (Ambient.cubicExhaustion d)
            (⟨J, 0, β₂⟩ : IsingParams ℝ) (0 : Fin d → ℤ) z)
        ≤ latticeMass d (Ambient.cubicExhaustion d)
            (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d (Ambient.cubicExhaustion d)
          (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d (Ambient.cubicExhaustion d)
              (⟨J, 0, β₂⟩ : IsingParams ℝ) (0 : Fin d → ℤ) z) := by
  have hxz : (0 : Fin d → ℤ) ≠ z := fun h => hz h.symm
  exact
    lemma_17_5_2_sandwich_of_concrete_pseudoMass_compact_bounds_and_profile_lower_on_self_Icc
      (d := d) (α := α) (Λ := Ambient.cubicExhaustion d) (J := J)
      (x := (0 : Fin d → ℤ)) (z := z) (β₁ := β₁) (β₂ := β₂)
      (rho := rho) hα hαd hd hJ_pos hxz hβ₁₂ hIcc hrho g' hcorr
      hderiv_lim hprofile

set_option maxHeartbeats 2000000 in
-- Uses the named tanh-profile predicate to supply the endpoint cubic profile
-- lower bound.
/-- **GJ §17.5 Lemma 17.5.2 anchored cubic self-interval sandwich from the
named tanh-profile predicate**: `cubicTanhProfileBound` supplies the endpoint
cubic profile lower bound, which then feeds the concrete self-interval sandwich
on the cubic exhaustion. -/
theorem
    lemma_17_5_2_cubic_origin_sandwich_of_cubicTanhProfileBound_on_self_Icc
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {J : ℝ} (hJ_pos : 0 < J)
    {z : Fin d → ℤ} (hz : z ≠ 0)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {rho : ℝ} (hrho : 0 < rho) (g' : ℝ → ℝ)
    (hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
          {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d)
              (Ambient.cubicExhaustion d)
              (⟨J, 0, β'⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hprofile_tanh : cubicTanhProfileBound α d rho β₂ J z) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d (Ambient.cubicExhaustion d)
            (⟨J, 0, β₂⟩ : IsingParams ℝ) (0 : Fin d → ℤ) z)
        ≤ latticeMass d (Ambient.cubicExhaustion d)
            (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d (Ambient.cubicExhaustion d)
          (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d (Ambient.cubicExhaustion d)
              (⟨J, 0, β₂⟩ : IsingParams ℝ) (0 : Fin d → ℤ) z) := by
  obtain ⟨_hβ₁_pos, hβ₂_pos, _hβ₂_lt⟩ :=
    lemma_17_5_2_interval_endpoints_of_Icc_subset_high_temp
      hd hJ_pos hβ₁₂ hIcc
  have hprofile :
      pseudoMassG α rho (-Real.log (β₂ * J * ↑(2 * d))) ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β₂⟩ : IsingParams ℝ)
            {(0 : Fin d → ℤ), z} :=
    cubicTanhProfileBound_le_cubic_correlation hJ_pos.le hβ₂_pos hz
      hprofile_tanh
  exact
    lemma_17_5_2_cubic_origin_sandwich_of_profile_lower_on_self_Icc
      (d := d) (α := α) (J := J) (z := z) (β₁ := β₁) (β₂ := β₂)
      (rho := rho) hα hαd hd hJ_pos hz hβ₁₂ hIcc hrho g' hcorr
      hderiv_lim hprofile

set_option maxHeartbeats 2000000 in
-- Uses interval-wide named tanh-profile bounds to supply both the active-range
-- hypothesis and the endpoint profile lower bound.
/-- **GJ §17.5 Lemma 17.5.2 anchored cubic self-interval sandwich from
interval tanh-profile bounds**: pointwise `cubicTanhProfileBound` on the beta
interval supplies the interval active-range hypothesis and the endpoint profile
lower bound, leaving only the derivative-limit input explicit. -/
theorem
    lemma_17_5_2_cubic_origin_sandwich_of_cubicTanhProfileBound_on_Icc
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {J : ℝ} (hJ_pos : 0 < J)
    {z : Fin d → ℤ} (hz : z ≠ 0)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {rho : ℝ} (hrho : 0 < rho) (g' : ℝ → ℝ)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d)
              (Ambient.cubicExhaustion d)
              (⟨J, 0, β'⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hprofile_tanh : ∀ β ∈ Set.Icc β₁ β₂,
      cubicTanhProfileBound α d rho β J z) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d (Ambient.cubicExhaustion d)
            (⟨J, 0, β₂⟩ : IsingParams ℝ) (0 : Fin d → ℤ) z)
        ≤ latticeMass d (Ambient.cubicExhaustion d)
            (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d (Ambient.cubicExhaustion d)
          (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d (Ambient.cubicExhaustion d)
              (⟨J, 0, β₂⟩ : IsingParams ℝ) (0 : Fin d → ℤ) z) := by
  have hcorr :=
    lemma_17_5_2_cubic_origin_active_range_of_cubicTanhProfileBound_on_Icc
      hd hJ_pos hz hIcc hrho hprofile_tanh
  exact
    lemma_17_5_2_cubic_origin_sandwich_of_cubicTanhProfileBound_on_self_Icc
      (d := d) (α := α) (J := J) (z := z) (β₁ := β₁) (β₂ := β₂)
      (rho := rho) hα hαd hd hJ_pos hz hβ₁₂ hIcc hrho g' hcorr
      hderiv_lim (hprofile_tanh β₂ (Set.right_mem_Icc.mpr hβ₁₂))

end Ambient

end IsingModel
