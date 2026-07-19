import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProvider

/-!
# GJ §17.5 Lemma 17.5.2 finite-HLS — ratio-lower and uniform-correlation route

Child module split off from `DerivativeLimitProviderFiniteHLS` for build speed.
Collects the high-temperature ratio-lower entry points and the uniform
infinite-correlation-lower entry points (upper bound, sandwich, self-interval
variants, and capstones) built on `Lemma_17_5_2_DerivativeLimitProvider`.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and
  Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

/-- **GJ §17.5 Lemma 17.5.2 upper bound from a high-temperature ratio lower
and a derivative-limit provider**. -/
theorem lemma_17_5_2_upper_bound_of_high_temp_ratio_lower_of_derivative_limit_provider
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
    {h : ℝ → ℝ}
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
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
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
  obtain ⟨g', hderiv_lim⟩ := hderiv_provider
  exact
    lemma_17_5_2_upper_bound_of_high_temp_ratio_lower
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem hrho g'
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hm_pos hderiv_lim hL_pos hratio

/-- **GJ §17.5 Lemma 17.5.2 sandwich from a high-temperature ratio lower and
a derivative-limit provider**. -/
theorem lemma_17_5_2_sandwich_of_high_temp_ratio_lower_of_derivative_limit_provider
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
    {h : ℝ → ℝ}
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
  obtain ⟨g', hderiv_lim⟩ := hderiv_provider
  exact
    lemma_17_5_2_sandwich_of_high_temp_ratio_lower
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem hrho g'
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hm_pos hderiv_lim hdecay
      hL_pos hratio

/-- **GJ §17.5 Lemma 17.5.2 upper bound from a uniform infinite-correlation
lower bound and a derivative-limit provider**. -/
theorem
    lemma_17_5_2_upper_bound_of_high_temp_uniform_correlation_lower_of_derivative_limit_provider
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
    {h : ℝ → ℝ}
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
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
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
  obtain ⟨g', hderiv_lim⟩ := hderiv_provider
  exact
    lemma_17_5_2_upper_bound_of_high_temp_uniform_correlation_lower
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem hrho g'
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hm_pos hderiv_lim hC_pos hH_pos
      hcInf_lower hdenom_bound

/-- **GJ §17.5 Lemma 17.5.2 sandwich from a uniform infinite-correlation lower
bound and a derivative-limit provider**. -/
theorem
    lemma_17_5_2_sandwich_of_high_temp_uniform_correlation_lower_of_derivative_limit_provider
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
    {h : ℝ → ℝ}
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
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
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
  obtain ⟨g', hderiv_lim⟩ := hderiv_provider
  exact
    lemma_17_5_2_sandwich_of_high_temp_uniform_correlation_lower
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem hrho g'
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hm_pos hderiv_lim hdecay
      hC_pos hH_pos hcInf_lower hdenom_bound

/-- **GJ §17.5 Lemma 17.5.2 self-interval upper bound from a uniform
infinite-correlation lower bound and a derivative-limit provider**. -/
theorem
    lemma_17_5_2_upper_bound_of_uniform_correlation_lower_on_self_Icc_of_derivative_limit_provider
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {rho : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ}
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
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
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
  obtain ⟨g', hderiv_lim⟩ := hderiv_provider
  exact
    lemma_17_5_2_upper_bound_of_uniform_correlation_lower_on_self_Icc
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hrho g' hh_diff hh_nonneg hg_eq
      hh_pos hc_pos hm_pos hderiv_lim hC_pos hH_pos hcInf_lower hdenom_bound

/-- **GJ §17.5 Lemma 17.5.2 self-interval sandwich from a uniform
infinite-correlation lower bound and a derivative-limit provider**. -/
theorem
    lemma_17_5_2_sandwich_of_uniform_correlation_lower_on_self_Icc_of_derivative_limit_provider
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {rho : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ}
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
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
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
  obtain ⟨g', hderiv_lim⟩ := hderiv_provider
  exact
    lemma_17_5_2_sandwich_of_uniform_correlation_lower_on_self_Icc
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hrho g' hh_diff hh_nonneg hg_eq
      hh_pos hc_pos hm_pos hderiv_lim hdecay hC_pos hH_pos hcInf_lower
      hdenom_bound

/-- **GJ §17.5 Lemma 17.5.2 capstone from a uniform infinite-correlation lower
bound and a derivative-limit provider**: returns the HLS witness, the named
upper-bound predicate, and the two-sided sandwich for the same constant. -/
theorem
    lemma_17_5_2_capstone_of_high_temp_uniform_correlation_lower_of_deriv_provider
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
    {h : ℝ → ℝ}
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
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
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
    lemma_17_5_2_sandwich_of_high_temp_uniform_correlation_lower_of_derivative_limit_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem hrho
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hm_pos hderiv_provider hdecay
      hC_pos hH_pos hcInf_lower hdenom_bound
  have hupper :
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) := by
    simpa [Lemma_17_5_2_UpperBound] using hupper_ineq
  exact ⟨K, hK_pos, hconv, hupper, hlower, hupper_ineq⟩

/-- **GJ §17.5 Lemma 17.5.2 self-interval capstone from a uniform
infinite-correlation lower bound and a derivative-limit provider**: the beta
interval itself supplies the auxiliary compact interval. -/
theorem
    lemma_17_5_2_capstone_of_uniform_correlation_lower_self_Icc_of_deriv_provider
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {rho : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ}
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
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
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
    lemma_17_5_2_sandwich_of_uniform_correlation_lower_on_self_Icc_of_derivative_limit_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hrho hh_diff hh_nonneg hg_eq
      hh_pos hc_pos hm_pos hderiv_provider hdecay hC_pos hH_pos hcInf_lower
      hdenom_bound
  have hupper :
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) := by
    simpa [Lemma_17_5_2_UpperBound] using hupper_ineq
  exact ⟨K, hK_pos, hconv, hupper, hlower, hupper_ineq⟩

end Ambient
end IsingModel
