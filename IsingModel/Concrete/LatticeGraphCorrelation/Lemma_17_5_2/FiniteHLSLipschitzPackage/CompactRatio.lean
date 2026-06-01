import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.FiniteHLSLipschitzPackage.RatioLower

/-!
# GJ §17.5 Lemma 17.5.2 finite-HLS Lipschitz package -- compact ratio wrappers

Part of the split `FiniteHLSLipschitzPackage` layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

set_option maxHeartbeats 2000000 in
-- This wrapper obtains the `C` and `H` ratio-lower witnesses by compactness,
-- then delegates to the uniform-correlation lower package.
/-- **GJ §17.5 Lemma 17.5.2 upper bound from compact ratio bounds**:
continuity on the closed beta interval turns pointwise positivity of the
infinite correlation into the uniform `C` lower bound, and turns denominator
continuity/nonnegativity into the uniform `H` upper bound.  These witnesses are
then fed into `lemma_17_5_2_upper_bound_of_high_temp_uniform_correlation_lower`.
-/
theorem lemma_17_5_2_upper_bound_of_high_temp_compact_ratio_bounds
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
    (hh_cont : ContinuousOn h (Set.Icc β₁ β₂))
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
        g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) := by
  obtain ⟨C, H, hC_pos, hH_pos, hc_lower, hdenom_bound⟩ :=
    lemma_17_5_2_compact_ratio_bounds_on_beta_interval
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (h := h)
      hJ_pos.le hxz hβ₁₂ ha hab hlt hβ_mem hh_cont hh_nonneg hc_pos
  exact
    lemma_17_5_2_upper_bound_of_high_temp_uniform_correlation_lower
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem hrho g'
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hm_pos hderiv_lim hC_pos hH_pos
      hc_lower hdenom_bound

set_option maxHeartbeats 2000000 in
-- Compactness supplies the ratio-lower witnesses; the lower side is the
-- existing validating pseudo-mass decay hypothesis.
/-- **GJ §17.5 Lemma 17.5.2 sandwich from compact ratio bounds**: add the
validating pseudo-mass decay lower side to
`lemma_17_5_2_upper_bound_of_high_temp_compact_ratio_bounds`. -/
theorem lemma_17_5_2_sandwich_of_high_temp_compact_ratio_bounds
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
    (hh_cont : ContinuousOn h (Set.Icc β₁ β₂))
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
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
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
    lemma_17_5_2_upper_bound_of_high_temp_compact_ratio_bounds
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem hrho g'
      hh_diff hh_cont hh_nonneg hg_eq hh_pos hc_pos hm_pos hderiv_lim
  exact ⟨K, hK, hK_conv,
    lemma_17_5_2_sandwich_of_decay_and_upper hα hrho hdecay hupper⟩


end Ambient
end IsingModel
