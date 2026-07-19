import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsCompactPackage
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferBasic

/-!
# Concrete pseudo-mass high-temperature sandwich: active-range foundation (GJ Lemma 17.5.2)

This module holds the foundational active-range lemmas of the concrete
`pseudoMassFromParamsAtPair` high-temperature sandwich package: the endpoint
high-temperature scalar bounds and the active-range facts
(`lemma_17_5_2_active_range_of_high_temp_pair`,
`lemma_17_5_2_active_range_on_Icc_of_high_temp_pair`).  The interval
active-range lemma is the shared hub reused by the ratio-bound, compact-bound,
and capstone children.

The umbrella module `PseudoMassFromParamsHighTempSandwich` re-exports this file
together with the ratio-bound, compact-bound, and capstone children, so
downstream consumers keep importing the original path unchanged.
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

/-- **GJ §17.5 Lemma 17.5.2 active range from the high-temperature path lower
bound**: for distinct lattice sites and `J, β > 0`, the infinite-volume
two-point function lies in `(0,2)`.  Positivity comes from the translated
cubic path lower bound `tanh(βJ)^dist ≤ corr_∞`; the upper side is the
unconditional `corr_∞ < 2`. -/
theorem lemma_17_5_2_active_range_of_high_temp_pair
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J β : ℝ} (hJ_pos : 0 < J) (hβ_pos : 0 < β)
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2 := by
  let p : IsingParams ℝ := ⟨J, 0, β⟩
  have hf : Ferromagnetic p := ⟨hJ_pos.le, le_refl 0, hβ_pos⟩
  have hsep : z - x ≠ 0 := by
    intro hzero
    exact hxz (sub_eq_zero.mp hzero).symm
  have htanh_pos : 0 < Real.tanh (β * J) :=
    by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hβ_pos hJ_pos))
        (Real.cosh_pos _)
  have hpow_pos :
      0 < Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 (z - x) :=
    pow_pos htanh_pos _
  have hpath :
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 (z - x) ≤
        Ambient.twoPointFunction d p (z - x) :=
    twoPointFunction_ge_tanh_betaJ_pow_dist hJ_pos.le hβ_pos hsep
  have htwo_pos : 0 < Ambient.twoPointFunction d p (z - x) :=
    hpow_pos.trans_le hpath
  have hcubic :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p {x, z}
        = Ambient.twoPointFunction d p (z - x) :=
    correlationInfinite_latticeGraph_pair_eq_twoPointFunction d p hf x z
  have hpos_cubic :
      0 <
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p {x, z} := by
    rwa [hcubic]
  have hindep :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} =
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p {x, z} :=
    correlationInfinite_indep_exhaustion (IsingModel.latticeGraph d)
      Λ (Ambient.cubicExhaustion d) p hf {x, z}
  have hpos :
      0 < Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} := by
    rwa [hindep]
  exact correlationInfinite_mem_Ioo_zero_two_of_pos
    (IsingModel.latticeGraph d) Λ p hf {x, z} hpos

/-- **GJ §17.5 Lemma 17.5.2 interval active range from a high-temperature
inclusion**: if `Icc β₁ β₂` lies in the open high-temperature interval, then
the infinite two-point correlation for every `β ∈ Icc β₁ β₂` lies in `(0,2)`.
-/
theorem lemma_17_5_2_active_range_on_Icc_of_high_temp_pair
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ}
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) :
    ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2 := by
  intro β hβ
  exact lemma_17_5_2_active_range_of_high_temp_pair
    Λ hJ_pos (hIcc hβ).1 hxz

end Ambient

end IsingModel
