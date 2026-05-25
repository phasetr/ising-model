import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProvider

/-!
# GJ §17.5 Lemma 17.5.2 capstone — provider-based infinite-HLS bridges

This module connects the derivative-limit provider to the infinite derivative
and infinite-HLS bridge layer below the larger finite-HLS assemblies.  The
substantive analytic theorem remains the proof of
`Lemma_17_5_2_DerivativeLimitProvider`; these entry points keep downstream
callers from naming the limiting derivative profile `g'`.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and
  Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

/-- **GJ §17.5 Lemma 17.5.2 infinite beta derivative from a derivative-limit
provider**: the provider supplies the limiting derivative profile used to
differentiate the thermodynamic-limit two-point function. -/
theorem correlationInfinite_hasDerivAt_beta_of_derivative_limit_provider
    {d : ℕ} (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J)
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J r_val s_val) :
    ∃ g' : ℝ → ℝ,
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        HasDerivAt
          (fun β' =>
            Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {r_val, s_val})
          (g' β) β := by
  obtain ⟨g', hderiv_lim⟩ := hderiv_provider
  exact ⟨g',
    correlationInfinite_hasDerivAt_beta_of_tendstoLocallyUniformlyOn_deriv
      hd Λ r_val s_val hrs J hJ_pos g' hderiv_lim⟩

/-- **GJ §17.5 Lemma 17.5.2 infinite HLS denominator comparison from a
derivative-limit provider and a bound on the limiting derivative**. -/
theorem
    lemma_17_5_2_infinite_hls_comparison_of_deriv_bound_provider
    {d α : ℕ} (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    (β K : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (h : ℝ → ℝ)
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
    (hbound :
      ∀ g' : ℝ → ℝ,
        TendstoLocallyUniformlyOn
          (fun n β =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          g' Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) →
        |g' β| ≤
          K *
            Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} /
            (h β) ^ (2 * α)) :
    Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β α K h := by
  obtain ⟨g', hderiv_lim⟩ := hderiv_provider
  exact
    lemma_17_5_2_infinite_hls_denominator_comparison_of_deriv_limit_bound
      hd Λ J hJ_pos x z hxz β K hβ h g' hderiv_lim
      (hbound g' hderiv_lim)

/-- **GJ §17.5 Lemma 17.5.2 infinite HLS denominator comparison from finite
derivative bounds and a derivative-limit provider**. -/
theorem
    lemma_17_5_2_infinite_hls_comparison_of_finite_deriv_bounds_provider
    {d α : ℕ} (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    (β K : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (h : ℝ → ℝ)
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
    (hfinite :
      ∀ᶠ n in Filter.atTop,
        |deriv (fun β' =>
          Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
          K *
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
            (h β) ^ (2 * α)) :
    Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β α K h := by
  obtain ⟨g', hderiv_lim⟩ := hderiv_provider
  exact
    lemma_17_5_2_infinite_hls_denominator_comparison_of_finite_deriv_bounds
      hd Λ J hJ_pos x z hxz β K hβ h g' hderiv_lim hfinite

/-- **GJ §17.5 Lemma 17.5.2 interval infinite HLS denominator comparisons from
pointwise finite derivative bounds and a derivative-limit provider**. -/
theorem
    lemma_17_5_2_infinite_hls_comparison_on_Icc_of_finite_deriv_bounds_provider
    {d α : ℕ} (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    (β₁ β₂ K : ℝ)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (h : ℝ → ℝ)
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
    (hfinite :
      ∀ β ∈ Set.Icc β₁ β₂,
        ∀ᶠ n in Filter.atTop,
          |deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
            K *
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
              (h β) ^ (2 * α)) :
    ∀ β ∈ Set.Icc β₁ β₂,
      Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β α K h := by
  obtain ⟨g', hderiv_lim⟩ := hderiv_provider
  exact
    lemma_17_5_2_infinite_hls_denominator_comparison_on_Icc_of_finite_deriv_bounds
      hd Λ J hJ_pos x z hxz β₁ β₂ K hIcc h g' hderiv_lim hfinite

/-- **GJ §17.5 Lemma 17.5.2 interval infinite HLS denominator comparisons from
a uniform finite derivative bound and a derivative-limit provider**. -/
theorem
    lemma_17_5_2_infinite_hls_comparison_on_Icc_of_uniform_finite_deriv_bounds_provider
    {d α : ℕ} (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    (β₁ β₂ K : ℝ)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (h : ℝ → ℝ)
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
    (hfinite :
      ∀ᶠ n in Filter.atTop,
        ∀ β ∈ Set.Icc β₁ β₂,
          |deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
            K *
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
              (h β) ^ (2 * α)) :
    ∀ β ∈ Set.Icc β₁ β₂,
      Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β α K h := by
  obtain ⟨g', hderiv_lim⟩ := hderiv_provider
  exact
    lemma_17_5_2_infinite_hls_denominator_comparison_on_Icc_of_uniform_finite_deriv_bounds
      hd Λ J hJ_pos x z hxz β₁ β₂ K hIcc h g' hderiv_lim hfinite

/-- **GJ §17.5 Lemma 17.5.2 finite HLS bounds to infinite Lipschitz from a
derivative-limit provider**. -/
theorem
    lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_finite_deriv_bounds_provider
    {d α : ℕ} (hαd : 2 * α > d) (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
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
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ((∀ᶠ n in Filter.atTop,
          ∀ β ∈ Set.Icc β₁ β₂,
            |deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
              K *
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
                (h β) ^ (2 * α)) →
        |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
          ↑(2 * α + 1) * K / rho * (β₂ - β₁)) := by
  obtain ⟨g', hderiv_lim⟩ := hderiv_provider
  exact
    lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_uniform_finite_deriv_bounds
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho) (h := h)
      hαd hd hJ_pos hxz hβ₁₂ hIcc hrho g'
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hderiv_lim

/-- **GJ §17.5 Lemma 17.5.2 infinite-HLS Lipschitz package from a
derivative-limit provider**: the provider supplies the differentiability of the
infinite-volume correlation profile, leaving only the interval HLS denominator
comparison as the analytic input to the Lipschitz step. -/
theorem
    lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_hls_constant_provider
    {d α : ℕ} (hαd : 2 * α > d) (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
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
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ((∀ β' ∈ Set.Icc β₁ β₂,
          Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β' α K h) →
        |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
          ↑(2 * α + 1) * K / rho * (β₂ - β₁)) := by
  obtain ⟨g', hderiv_lim⟩ := hderiv_provider
  let cInf : ℝ → ℝ := fun β' =>
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}
  have hc_diff : ∀ β' ∈ Set.Icc β₁ β₂,
      HasDerivAt cInf (deriv cInf β') β' := by
    intro β hβ
    have hcdiff_g :=
      correlationInfinite_hasDerivAt_beta_of_tendstoLocallyUniformlyOn_deriv
        hd Λ x z hxz J hJ_pos g' hderiv_lim β (hIcc hβ)
    have hderiv_eq : deriv cInf β = g' β := hcdiff_g.deriv
    simpa [cInf, hderiv_eq] using hcdiff_g
  exact
    lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_hls_constant
      hαd Λ J x z hβ₁₂ hrho hh_diff hc_diff hh_nonneg
      hg_eq hh_pos hc_pos

/-- **GJ §17.5 Lemma 17.5.2 concrete infinite-HLS Lipschitz package from a
derivative-limit provider**: specialize the abstract profile `h` in the
provider-shaped infinite-HLS package to the concrete pseudo-mass profile
`pseudoMassFromParamsAtPair`. -/
theorem
    lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_concrete_hls_constant_provider
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {rho : ℝ} (hrho : 0 < rho)
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ((∀ β' ∈ Set.Icc β₁ β₂,
          Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β' α K
            (fun β =>
              pseudoMassFromParamsAtPair hα hrho d Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z)) →
        |(pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) ^ (2 * α + 1) -
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₁⟩ : IsingParams ℝ) x z) ^ (2 * α + 1)| ≤
          ↑(2 * α + 1) * K / rho * (β₂ - β₁)) := by
  obtain ⟨g', hderiv_lim⟩ := hderiv_provider
  let h : ℝ → ℝ := fun β =>
    pseudoMassFromParamsAtPair hα hrho d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z
  have hprovider :
      Lemma_17_5_2_DerivativeLimitProvider Λ J x z := ⟨g', hderiv_lim⟩
  have hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2 :=
    lemma_17_5_2_active_range_on_Icc_of_high_temp_pair Λ hJ_pos hxz hIcc
  have hc_cont : ∀ β ∈ Set.Icc β₁ β₂,
      ContinuousAt
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
        β := by
    intro β hβ
    exact correlationInfinite_continuousAt_beta_of_high_temp
      hd Λ x z hxz J hJ_pos β (hIcc hβ)
  have hc_diff : ∀ β ∈ Set.Icc β₁ β₂,
      DifferentiableAt ℝ
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
        β := by
    intro β hβ
    exact (correlationInfinite_hasDerivAt_beta_of_tendstoLocallyUniformlyOn_deriv
      (d := d) (Λ := Λ) (r_val := x) (s_val := z) (J := J) (g' := g')
      hd hxz hJ_pos hderiv_lim β (hIcc hβ)).differentiableAt
  have hh_diff : ∀ β ∈ Set.Icc β₁ β₂, HasDerivAt h (deriv h β) β := by
    simpa [h] using
      pseudoMassFromParamsAtPair_beta_hasDerivAt_deriv_on_Icc_of_corr_differentiableAt
        hα hrho Λ J x z hc_diff hcorr
  have hh_nonneg : ∀ β ∈ Set.Icc β₁ β₂, 0 ≤ h β := by
    intro β _hβ
    exact pseudoMassFromParamsAtPair_nonneg hα hrho d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z
  have hg_eq : ∀ β ∈ Set.Icc β₁ β₂,
      (fun γ => pseudoMassG α rho (h γ)) =ᶠ[nhds β]
        (fun γ =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, γ⟩ : IsingParams ℝ) {x, z}) := by
    simpa [h] using
      pseudoMassFromParamsAtPair_beta_pseudoMassG_eventuallyEq_on_Icc_of_corr_continuousAt
        hα hrho Λ J x z hc_cont hcorr
  have hh_pos : ∀ β ∈ Set.Icc β₁ β₂, 0 < h β := by
    intro β hβ
    exact pseudoMassFromParamsAtPair_pos_of_corr_mem hα hrho d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z (hcorr β hβ)
  have hc_pos : ∀ β ∈ Set.Icc β₁ β₂,
      0 <
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} := by
    intro β hβ
    exact (hcorr β hβ).1
  simpa [h] using
    lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_hls_constant_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho) (h := h)
      hαd hd hJ_pos hxz hβ₁₂ hIcc hrho
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hprovider

/-- **GJ §17.5 Lemma 17.5.2 enlarged finite-HLS package with path-rate bound
from a derivative-limit provider**. -/
theorem
    lemma_17_5_2_enlarged_finite_hls_lipschitz_package_with_path_rate_of_derivative_limit_provider
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
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
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ((∀ᶠ n in Filter.atTop,
          ∀ β ∈ Set.Icc β₁ β₂,
            |deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
              K *
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
                (h β) ^ (2 * α)) →
        |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
          ↑(2 * α + 1) * K / rho * (β₂ - β₁)) ∧
      ENNReal.ofReal (-Real.log (Real.tanh (β₂ * J))) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) := by
  obtain ⟨g', hderiv_lim⟩ := hderiv_provider
  exact
    lemma_17_5_2_enlarged_finite_hls_lipschitz_package_with_path_rate
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hrho g'
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hm_pos hderiv_lim

/-- **GJ §17.5 Lemma 17.5.2 enlarged finite-HLS upper bound from a
derivative-limit provider**. -/
theorem
    lemma_17_5_2_upper_bound_of_enlarged_finite_hls_lipschitz_package_of_derivative_limit_provider
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
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
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ((∀ᶠ n in Filter.atTop,
          ∀ β ∈ Set.Icc β₁ β₂,
            |deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
              K *
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
                (h β) ^ (2 * α)) →
          Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
            (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho))) := by
  obtain ⟨g', hderiv_lim⟩ := hderiv_provider
  exact
    lemma_17_5_2_upper_bound_of_enlarged_finite_hls_lipschitz_package
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hrho g'
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hm_pos hderiv_lim

/-- **GJ §17.5 Lemma 17.5.2 enlarged finite-HLS sandwich from a
derivative-limit provider**. -/
theorem
    lemma_17_5_2_sandwich_of_enlarged_finite_hls_lipschitz_package_of_derivative_limit_provider
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
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
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ((∀ᶠ n in Filter.atTop,
          ∀ β ∈ Set.Icc β₁ β₂,
            |deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
              K *
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
                (h β) ^ (2 * α)) →
          ENNReal.ofReal
              (pseudoMassFromParamsAtPair hα hrho d Λ
                (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
            ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
          latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
            ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
              ENNReal.ofReal
                (pseudoMassFromParamsAtPair hα hrho d Λ
                  (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) := by
  obtain ⟨g', hderiv_lim⟩ := hderiv_provider
  exact
    lemma_17_5_2_sandwich_of_enlarged_finite_hls_lipschitz_package
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hrho g'
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hm_pos hderiv_lim hdecay

end Ambient
end IsingModel
