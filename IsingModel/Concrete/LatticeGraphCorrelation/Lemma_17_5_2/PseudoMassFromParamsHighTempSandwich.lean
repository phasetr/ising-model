import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsCompactPackage
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferBasic

/-!
# Concrete pseudo-mass high-temperature sandwich package for GJ Lemma 17.5.2

This module combines the concrete `pseudoMassFromParamsAtPair` compact
upper-bound package with the existing high-temperature decay-transfer bridge.
The result removes the lower-side `HasExponentialDecay` premise whenever the
endpoint concrete pseudo-mass is bounded by the transferred high-temperature
rate, or by the equivalent `pseudoMassG` profile comparison.
-/

namespace IsingModel

open Set

namespace Ambient

/-- **Endpoint high-temperature scalar bounds from an interval inclusion**:
if the closed interval lies in the high-temperature open interval, then the
right endpoint is positive and satisfies `β₂ * J * 2d < 1`. -/
theorem lemma_17_5_2_endpoint_high_temp_of_Icc_subset_high_temp
    {d : ℕ} (hd : 1 ≤ d) {J β₁ β₂ : ℝ} (hJ_pos : 0 < J)
    (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) :
    0 < β₂ ∧ β₂ * J * ↑(2 * d) < 1 := by
  obtain ⟨_hβ₁_pos, hβ₂_pos, hβ₂_lt⟩ :=
    lemma_17_5_2_interval_endpoints_of_Icc_subset_high_temp
      hd hJ_pos hβ₁₂ hIcc
  exact ⟨hβ₂_pos, hβ₂_lt⟩

set_option maxHeartbeats 2000000 in
-- The statement composes the concrete upper package with the lower
-- high-temperature transfer bridge.
/-- **GJ §17.5 Lemma 17.5.2 concrete high-temperature sandwich from a rate
comparison**: if the endpoint concrete pseudo-mass is below the transferred
high-temperature rate `-log (β₂ J 2d)`, then the high-temperature decay
transfer supplies the lower validating decay premise for the concrete compact
sandwich package. -/
theorem lemma_17_5_2_sandwich_of_concrete_pseudoMass_compact_bounds_and_le_high_temp_rate
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    {rho : ℝ} (hrho : 0 < rho) (g' : ℝ → ℝ)
    (hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hβ₂_pos : 0 < β₂)
    (hβ₂_lt : β₂ * J * ↑(2 * d) < 1)
    (hle :
      pseudoMassFromParamsAtPair hα hrho d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z
        ≤ -Real.log (β₂ * J * ↑(2 * d))) :
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
  have hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
    HasExponentialDecay_pseudoMassFromParamsAtPair_of_le_high_temp_rate
      hα hrho Λ hJ_pos.le hβ₂_pos hβ₂_lt hle
  exact
    lemma_17_5_2_sandwich_of_concrete_pseudoMass_compact_ratio_bounds
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem hrho g'
      hcorr hderiv_lim hdecay

set_option maxHeartbeats 2000000 in
-- This wrapper derives the endpoint scalar hypotheses from the interval
-- inclusion before applying the comparison form above.
/-- **GJ §17.5 Lemma 17.5.2 concrete high-temperature sandwich from an interval
high-temperature inclusion and endpoint rate comparison**: the interval
inclusion supplies `0 < β₂` and `β₂ * J * 2d < 1`, so the only lower-side
comparison premise is `pseudoMassFromParamsAtPair ≤ -log (β₂ J 2d)`. -/
theorem lemma_17_5_2_sandwich_of_concrete_pseudoMass_compact_bounds_and_le_high_temp_rate_on_Icc
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    {rho : ℝ} (hrho : 0 < rho) (g' : ℝ → ℝ)
    (hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hle :
      pseudoMassFromParamsAtPair hα hrho d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z
        ≤ -Real.log (β₂ * J * ↑(2 * d))) :
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
  obtain ⟨hβ₂_pos, hβ₂_lt⟩ :=
    lemma_17_5_2_endpoint_high_temp_of_Icc_subset_high_temp
      hd hJ_pos hβ₁₂ hIcc
  exact
    lemma_17_5_2_sandwich_of_concrete_pseudoMass_compact_bounds_and_le_high_temp_rate
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem hrho g'
      hcorr hderiv_lim hβ₂_pos hβ₂_lt hle

set_option maxHeartbeats 2000000 in
-- Specializes the auxiliary compact interval to the beta interval itself.
/-- **GJ §17.5 Lemma 17.5.2 concrete high-temperature sandwich on its own
beta interval from a rate comparison**: the interval inclusion supplies both
the endpoint high-temperature scalar hypotheses and the auxiliary interval
package with `a = β₁` and `b = β₂`. -/
theorem
    lemma_17_5_2_sandwich_of_concrete_pseudoMass_compact_bounds_and_le_high_temp_rate_on_self_Icc
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {rho : ℝ} (hrho : 0 < rho) (g' : ℝ → ℝ)
    (hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hle :
      pseudoMassFromParamsAtPair hα hrho d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z
        ≤ -Real.log (β₂ * J * ↑(2 * d))) :
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
  obtain ⟨hβ₁_pos, _hβ₂_pos, hβ₂_lt⟩ :=
    lemma_17_5_2_interval_endpoints_of_Icc_subset_high_temp
      hd hJ_pos hβ₁₂ hIcc
  exact
    lemma_17_5_2_sandwich_of_concrete_pseudoMass_compact_bounds_and_le_high_temp_rate_on_Icc
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := β₁) (b := β₂) (rho := rho)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hβ₁_pos hβ₁₂ hβ₂_lt
      (fun β hβ => hβ) hrho g' hcorr hderiv_lim hle

set_option maxHeartbeats 2000000 in
-- The profile comparison form derives the endpoint rate comparison internally.
/-- **GJ §17.5 Lemma 17.5.2 concrete high-temperature sandwich from a
`pseudoMassG` profile lower bound**: an endpoint lower bound for the infinite
correlation by the pseudo-mass profile at `-log (β₂ J 2d)` validates the
endpoint concrete pseudo-mass as a decay rate, then the concrete compact
upper-bound package gives the two-sided sandwich. -/
theorem lemma_17_5_2_sandwich_of_concrete_pseudoMass_compact_bounds_and_profile_lower
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    {rho : ℝ} (hrho : 0 < rho) (g' : ℝ → ℝ)
    (hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hβ₂_pos : 0 < β₂)
    (hβ₂_lt : β₂ * J * ↑(2 * d) < 1)
    (hprofile :
      pseudoMassG α rho (-Real.log (β₂ * J * ↑(2 * d))) ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) {x, z}) :
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
  have hβ₂_mem : β₂ ∈ Set.Icc β₁ β₂ := Set.right_mem_Icc.mpr hβ₁₂
  have hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
    HasExponentialDecay_pseudoMassFromParamsAtPair_of_pseudoMassG_le_corr
      hα hrho Λ hJ_pos.le hβ₂_pos hβ₂_lt (hcorr β₂ hβ₂_mem) hprofile
  exact
    lemma_17_5_2_sandwich_of_concrete_pseudoMass_compact_ratio_bounds
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem hrho g'
      hcorr hderiv_lim hdecay

set_option maxHeartbeats 2000000 in
-- This wrapper derives the endpoint scalar hypotheses from the interval
-- inclusion before applying the profile-lower-bound form above.
/-- **GJ §17.5 Lemma 17.5.2 concrete high-temperature sandwich from an interval
high-temperature inclusion and endpoint profile lower bound**: the interval
inclusion supplies the endpoint high-temperature scalar hypotheses, and the
profile lower bound supplies the validating lower decay rate. -/
theorem lemma_17_5_2_sandwich_of_concrete_pseudoMass_compact_bounds_and_profile_lower_on_Icc
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    {rho : ℝ} (hrho : 0 < rho) (g' : ℝ → ℝ)
    (hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hprofile :
      pseudoMassG α rho (-Real.log (β₂ * J * ↑(2 * d))) ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) {x, z}) :
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
  obtain ⟨hβ₂_pos, hβ₂_lt⟩ :=
    lemma_17_5_2_endpoint_high_temp_of_Icc_subset_high_temp
      hd hJ_pos hβ₁₂ hIcc
  exact
    lemma_17_5_2_sandwich_of_concrete_pseudoMass_compact_bounds_and_profile_lower
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem hrho g'
      hcorr hderiv_lim hβ₂_pos hβ₂_lt hprofile

set_option maxHeartbeats 2000000 in
-- Specializes the auxiliary compact interval to the beta interval itself.
/-- **GJ §17.5 Lemma 17.5.2 concrete high-temperature sandwich on its own
beta interval from a profile lower bound**: the interval inclusion supplies the
endpoint high-temperature scalar hypotheses and the auxiliary interval package
with `a = β₁` and `b = β₂`. -/
theorem
    lemma_17_5_2_sandwich_of_concrete_pseudoMass_compact_bounds_and_profile_lower_on_self_Icc
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {rho : ℝ} (hrho : 0 < rho) (g' : ℝ → ℝ)
    (hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hprofile :
      pseudoMassG α rho (-Real.log (β₂ * J * ↑(2 * d))) ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) {x, z}) :
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
  obtain ⟨hβ₁_pos, _hβ₂_pos, hβ₂_lt⟩ :=
    lemma_17_5_2_interval_endpoints_of_Icc_subset_high_temp
      hd hJ_pos hβ₁₂ hIcc
  exact
    lemma_17_5_2_sandwich_of_concrete_pseudoMass_compact_bounds_and_profile_lower_on_Icc
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := β₁) (b := β₂) (rho := rho)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hβ₁_pos hβ₁₂ hβ₂_lt
      (fun β hβ => hβ) hrho g' hcorr hderiv_lim hprofile

set_option maxHeartbeats 2000000 in
-- Repackages the rate-comparison sandwich with the matching named upper-bound
-- predicate for the same HLS constant.
/-- **GJ §17.5 Lemma 17.5.2 concrete high-temperature capstone from a rate
comparison**: the rate-comparison sandwich wrapper also supplies the matching
named upper-bound predicate for the same HLS constant `K`. -/
theorem lemma_17_5_2_capstone_of_concrete_pseudoMass_compact_bounds_and_le_high_temp_rate
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    {rho : ℝ} (hrho : 0 < rho) (g' : ℝ → ℝ)
    (hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hβ₂_pos : 0 < β₂)
    (hβ₂_lt : β₂ * J * ↑(2 * d) < 1)
    (hle :
      pseudoMassFromParamsAtPair hα hrho d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z
        ≤ -Real.log (β₂ * J * ↑(2 * d))) :
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
    lemma_17_5_2_sandwich_of_concrete_pseudoMass_compact_bounds_and_le_high_temp_rate
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem hrho g'
      hcorr hderiv_lim hβ₂_pos hβ₂_lt hle
  have hupper :
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) := by
    simpa [Lemma_17_5_2_UpperBound] using hupper_ineq
  exact ⟨K, hK_pos, hconv, hupper, hlower, hupper_ineq⟩

set_option maxHeartbeats 2000000 in
-- The interval form derives the endpoint high-temperature scalar hypotheses.
/-- **GJ §17.5 Lemma 17.5.2 interval concrete high-temperature capstone from
a rate comparison**: the interval inclusion supplies the endpoint scalar
hypotheses, and the rate-comparison capstone returns the matching upper
predicate and sandwich for one HLS constant. -/
theorem
    lemma_17_5_2_capstone_of_concrete_pseudoMass_compact_bounds_and_le_high_temp_rate_on_Icc
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    {rho : ℝ} (hrho : 0 < rho) (g' : ℝ → ℝ)
    (hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hle :
      pseudoMassFromParamsAtPair hα hrho d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z
        ≤ -Real.log (β₂ * J * ↑(2 * d))) :
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
  obtain ⟨hβ₂_pos, hβ₂_lt⟩ :=
    lemma_17_5_2_endpoint_high_temp_of_Icc_subset_high_temp
      hd hJ_pos hβ₁₂ hIcc
  exact
    lemma_17_5_2_capstone_of_concrete_pseudoMass_compact_bounds_and_le_high_temp_rate
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem hrho g'
      hcorr hderiv_lim hβ₂_pos hβ₂_lt hle

set_option maxHeartbeats 2000000 in
-- Specializes the auxiliary compact interval to the beta interval itself.
/-- **GJ §17.5 Lemma 17.5.2 concrete high-temperature capstone on its own
beta interval from a rate comparison**: the interval inclusion supplies the
endpoint and auxiliary interval scalar hypotheses. -/
theorem
    lemma_17_5_2_capstone_of_concrete_pseudoMass_compact_bounds_and_le_high_temp_rate_on_self_Icc
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {rho : ℝ} (hrho : 0 < rho) (g' : ℝ → ℝ)
    (hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hle :
      pseudoMassFromParamsAtPair hα hrho d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z
        ≤ -Real.log (β₂ * J * ↑(2 * d))) :
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
  obtain ⟨hβ₁_pos, _hβ₂_pos, hβ₂_lt⟩ :=
    lemma_17_5_2_interval_endpoints_of_Icc_subset_high_temp
      hd hJ_pos hβ₁₂ hIcc
  exact
    lemma_17_5_2_capstone_of_concrete_pseudoMass_compact_bounds_and_le_high_temp_rate_on_Icc
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := β₁) (b := β₂) (rho := rho)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hβ₁_pos hβ₁₂ hβ₂_lt
      (fun β hβ => hβ) hrho g' hcorr hderiv_lim hle

set_option maxHeartbeats 2000000 in
-- Repackages the profile-lower sandwich with the matching named upper-bound
-- predicate for the same HLS constant.
/-- **GJ §17.5 Lemma 17.5.2 concrete high-temperature capstone from a
`pseudoMassG` profile lower bound**: the profile-lower sandwich wrapper also
supplies the matching named upper-bound predicate for the same HLS constant
`K`. -/
theorem lemma_17_5_2_capstone_of_concrete_pseudoMass_compact_bounds_and_profile_lower
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    {rho : ℝ} (hrho : 0 < rho) (g' : ℝ → ℝ)
    (hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hβ₂_pos : 0 < β₂)
    (hβ₂_lt : β₂ * J * ↑(2 * d) < 1)
    (hprofile :
      pseudoMassG α rho (-Real.log (β₂ * J * ↑(2 * d))) ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) {x, z}) :
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
    lemma_17_5_2_sandwich_of_concrete_pseudoMass_compact_bounds_and_profile_lower
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem hrho g'
      hcorr hderiv_lim hβ₂_pos hβ₂_lt hprofile
  have hupper :
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) := by
    simpa [Lemma_17_5_2_UpperBound] using hupper_ineq
  exact ⟨K, hK_pos, hconv, hupper, hlower, hupper_ineq⟩

set_option maxHeartbeats 2000000 in
-- The interval form derives the endpoint high-temperature scalar hypotheses.
/-- **GJ §17.5 Lemma 17.5.2 interval concrete high-temperature capstone from
a profile lower bound**: the interval inclusion supplies the endpoint scalar
hypotheses, and the profile-lower capstone returns the matching upper predicate
and sandwich for one HLS constant. -/
theorem
    lemma_17_5_2_capstone_of_concrete_pseudoMass_compact_bounds_and_profile_lower_on_Icc
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    {rho : ℝ} (hrho : 0 < rho) (g' : ℝ → ℝ)
    (hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hprofile :
      pseudoMassG α rho (-Real.log (β₂ * J * ↑(2 * d))) ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) {x, z}) :
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
  obtain ⟨hβ₂_pos, hβ₂_lt⟩ :=
    lemma_17_5_2_endpoint_high_temp_of_Icc_subset_high_temp
      hd hJ_pos hβ₁₂ hIcc
  exact
    lemma_17_5_2_capstone_of_concrete_pseudoMass_compact_bounds_and_profile_lower
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem hrho g'
      hcorr hderiv_lim hβ₂_pos hβ₂_lt hprofile

set_option maxHeartbeats 2000000 in
-- Specializes the auxiliary compact interval to the beta interval itself.
/-- **GJ §17.5 Lemma 17.5.2 concrete high-temperature capstone on its own
beta interval from a profile lower bound**: the interval inclusion supplies the
endpoint and auxiliary interval scalar hypotheses. -/
theorem
    lemma_17_5_2_capstone_of_concrete_pseudoMass_compact_bounds_and_profile_lower_on_self_Icc
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {rho : ℝ} (hrho : 0 < rho) (g' : ℝ → ℝ)
    (hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hprofile :
      pseudoMassG α rho (-Real.log (β₂ * J * ↑(2 * d))) ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) {x, z}) :
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
  obtain ⟨hβ₁_pos, _hβ₂_pos, hβ₂_lt⟩ :=
    lemma_17_5_2_interval_endpoints_of_Icc_subset_high_temp
      hd hJ_pos hβ₁₂ hIcc
  exact
    lemma_17_5_2_capstone_of_concrete_pseudoMass_compact_bounds_and_profile_lower_on_Icc
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := β₁) (b := β₂) (rho := rho)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hβ₁_pos hβ₁₂ hβ₂_lt
      (fun β hβ => hβ) hrho g' hcorr hderiv_lim hprofile

end Ambient

end IsingModel
