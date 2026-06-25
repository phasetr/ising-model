import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProvider
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.BetaDerivBridges
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PathRateBridge
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsCompactPackage

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

/-- Concrete beta profile used by the infinite-HLS bridge wrappers. -/
noncomputable abbrev lemma_17_5_2_concretePseudoMassBetaProfile
    {d α : ℕ} (hα : 1 ≤ α) {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) : ℝ → ℝ :=
  fun β =>
    pseudoMassFromParamsAtPair hα hrho d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z

/-- **GJ §17.5 Lemma 17.5.2 infinite beta derivative from a derivative-limit
provider**: the provider supplies the limiting derivative profile used to
differentiate the thermodynamic-limit two-point function. -/
theorem correlationInfinite_hasDerivAt_beta_of_derivative_limit_provider
    {d : ℕ} (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J)
    {s : Set ℝ} (hs_open : IsOpen s)
    (hs_sub : s ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProviderOn s Λ J r_val s_val) :
    ∃ g' : ℝ → ℝ,
      ∀ β ∈ s,
        HasDerivAt
          (fun β' =>
            Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {r_val, s_val})
          (g' β) β := by
  obtain ⟨g', hderiv_lim⟩ := hderiv_provider
  exact ⟨g',
    correlationInfinite_hasDerivAt_beta_of_tendstoLocallyUniformlyOn_deriv
      hd Λ r_val s_val hrs J hJ_pos g' hs_open hs_sub hderiv_lim⟩

/-- **GJ §17.5 Lemma 17.5.2 infinite HLS denominator comparison from a
derivative-limit provider and a bound on the limiting derivative**. -/
theorem
    lemma_17_5_2_infinite_hls_comparison_of_deriv_bound_provider
    {d α : ℕ} (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    (β K : ℝ)
    {s : Set ℝ} (hs_open : IsOpen s)
    (hs_sub : s ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (hβ : β ∈ s)
    (h : ℝ → ℝ)
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProviderOn s Λ J x z)
    (hbound :
      ∀ g' : ℝ → ℝ,
        TendstoLocallyUniformlyOn
          (fun n β =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          g' Filter.atTop s →
        |g' β| ≤
          K *
            Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} /
            (h β) ^ (2 * α)) :
    Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β α K h := by
  obtain ⟨g', hderiv_lim⟩ := hderiv_provider
  exact
    lemma_17_5_2_infinite_hls_denominator_comparison_of_deriv_limit_bound
      hd Λ J hJ_pos x z hxz β K hs_open hs_sub hβ h g' hderiv_lim
      (hbound g' hderiv_lim)

/-- **GJ §17.5 Lemma 17.5.2 infinite HLS denominator comparison from finite
derivative bounds and a derivative-limit provider**. -/
theorem
    lemma_17_5_2_infinite_hls_comparison_of_finite_deriv_bounds_provider
    {d α : ℕ} (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    (β K : ℝ)
    {s : Set ℝ} (hs_open : IsOpen s)
    (hs_sub : s ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (hβ : β ∈ s)
    (h : ℝ → ℝ)
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProviderOn s Λ J x z)
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
      hd Λ J hJ_pos x z hxz β K hs_open hs_sub hβ h g' hderiv_lim hfinite

/-- **GJ §17.5 Lemma 17.5.2 interval infinite HLS denominator comparisons from
pointwise finite derivative bounds and a derivative-limit provider**. -/
theorem
    lemma_17_5_2_infinite_hls_comparison_on_Icc_of_finite_deriv_bounds_provider
    {d α : ℕ} (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    (β₁ β₂ K : ℝ)
    {s : Set ℝ} (hs_open : IsOpen s)
    (hs_sub : s ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (hIcc : Set.Icc β₁ β₂ ⊆ s)
    (h : ℝ → ℝ)
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProviderOn s Λ J x z)
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
      hd Λ J hJ_pos x z hxz β₁ β₂ K hs_open hs_sub hIcc h g' hderiv_lim hfinite

/-- **GJ §17.5 Lemma 17.5.2 interval infinite HLS denominator comparisons from
a uniform finite derivative bound and a derivative-limit provider**. -/
theorem
    lemma_17_5_2_infinite_hls_comparison_on_Icc_of_uniform_finite_deriv_bounds_provider
    {d α : ℕ} (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    (β₁ β₂ K : ℝ)
    {s : Set ℝ} (hs_open : IsOpen s)
    (hs_sub : s ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (hIcc : Set.Icc β₁ β₂ ⊆ s)
    (h : ℝ → ℝ)
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProviderOn s Λ J x z)
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
      hd Λ J hJ_pos x z hxz β₁ β₂ K hs_open hs_sub hIcc h g' hderiv_lim hfinite

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
      hαd hd hJ_pos hxz hβ₁₂ isOpen_Ioo (subset_refl _) hIcc hrho g'
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
        hd Λ x z hxz J hJ_pos g' isOpen_Ioo (subset_refl _) hderiv_lim β (hIcc hβ)
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
      hd hxz hJ_pos isOpen_Ioo (subset_refl _) hderiv_lim β (hIcc hβ)).differentiableAt
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

set_option maxHeartbeats 1200000 in
-- This fixed-constant form repeats the concrete pseudo-mass regularity
-- normalization from the existential HLS package.
/-- **GJ §17.5 Lemma 17.5.2 fixed-constant concrete infinite-HLS Lipschitz
bridge from a derivative-limit provider**: once the concrete infinite-HLS
denominator comparison is available for a chosen constant `K`, the concrete
pseudo-mass profile satisfies the endpoint Lipschitz estimate for that same
constant. -/
theorem
    lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_concrete_hls_comparison_provider
    {d α : ℕ} (hα : 1 ≤ α) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ K : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
    (hcomp : ∀ β ∈ Set.Icc β₁ β₂,
      Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β α K
        (lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z)) :
    |(pseudoMassFromParamsAtPair hα hrho d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) ^ (2 * α + 1) -
        (pseudoMassFromParamsAtPair hα hrho d Λ
          (⟨J, 0, β₁⟩ : IsingParams ℝ) x z) ^ (2 * α + 1)| ≤
      ↑(2 * α + 1) * K / rho * (β₂ - β₁) := by
  obtain ⟨g', hderiv_lim⟩ := hderiv_provider
  let h : ℝ → ℝ := lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z
  have hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2 :=
    lemma_17_5_2_active_range_on_Icc_of_high_temp_pair Λ hJ_pos hxz hIcc
  have hc_diff : ∀ β ∈ Set.Icc β₁ β₂,
      DifferentiableAt ℝ
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
        β := by
      intro β hβ
      exact (correlationInfinite_hasDerivAt_beta_of_tendstoLocallyUniformlyOn_deriv
        (d := d) (Λ := Λ) (r_val := x) (s_val := z) (J := J) (g' := g')
        hd hxz hJ_pos isOpen_Ioo (subset_refl _) hderiv_lim β (hIcc hβ)).differentiableAt
  have hcomp' : ∀ β ∈ Set.Icc β₁ β₂,
      |deriv
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
        β| ≤
        K *
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} /
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z) ^ (2 * α) := by
    intro β hβ
    simpa [Lemma_17_5_2_InfiniteHLSDenominatorComparison,
      lemma_17_5_2_concretePseudoMassBetaProfile] using hcomp β hβ
  simpa [h, lemma_17_5_2_concretePseudoMassBetaProfile] using
    pseudoMassFromParamsAtPair_beta_pow_succ_lipschitz_on_Icc_of_corr_differentiableAt
      hα hrho Λ J x z hβ₁₂ hc_diff hcorr hcomp'

set_option maxHeartbeats 1200000 in
-- The theorem combines the fixed-constant concrete Lipschitz bridge with the
-- path-rate all-rate bridge for the same HLS constant.
/-- **GJ §17.5 Lemma 17.5.2 upper bound from fixed concrete infinite-HLS and
path-rate inputs**: if one constant carries the concrete interval denominator
comparisons and the endpoint path-rate comparison, the provider-shaped
upper-bound predicate closes for that same constant. -/
theorem lemma_17_5_2_upper_bound_of_concrete_infinite_hls_inputs_provider
    {d α : ℕ} (hα : 1 ≤ α) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ K : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
    (hpath :
      ENNReal.ofReal (-Real.log (Real.tanh (β₂ * J))) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
      (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) := by
  have hβ₂ : 0 < β₂ := (hIcc ⟨hβ₁₂, le_rfl⟩).1
  have hd_pos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  let h : ℝ → ℝ := lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z
  have hlip :
      (∀ β' ∈ Set.Icc β₁ β₂,
          Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β' α K h) →
        |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
          ↑(2 * α + 1) * K / rho * (β₂ - β₁) := by
    intro hcomp'
    simpa [h, lemma_17_5_2_concretePseudoMassBetaProfile] using
      lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_concrete_hls_comparison_provider
        (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
        (β₁ := β₁) (β₂ := β₂) (K := K) (rho := rho)
        hα hd hrho hJ_pos hxz hβ₁₂ hIcc hderiv_provider hcomp'
  have hbridge :
      Lemma_17_5_2_InfiniteHLSLipschitzAllRateBridge
        hα hrho Λ J x z β₁ β₂ K h :=
    lemma_17_5_2_infinite_hls_lipschitz_all_rate_bridge_of_path_rate_le_hls
      hα hrho hd_pos Λ hJ_pos hβ₂ x z h
      (by simpa [h, lemma_17_5_2_concretePseudoMassBetaProfile] using hpath)
  exact
    lemma_17_5_2_upper_bound_of_infinite_hls_lipschitz_all_rate_bridge
      hα hrho Λ J x z β₁ β₂ K h hlip hbridge

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
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
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
    lemma_17_5_2_active_range_on_Icc_of_high_temp_pair Λ hJ_pos hxz hIcc β₂ hβ₂_mem
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
      hd hJ_pos hxz isOpen_Ioo (subset_refl _) hIcc hderiv_provider hfinite
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
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
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
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem
      hderiv_provider hL_pos hratio
  refine ⟨K, hK, hK_conv, ?_⟩
  exact
    lemma_17_5_2_upper_bound_of_concrete_infinite_hls_inputs_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (K := K) (rho := rho)
      hα hd hrho hJ_pos hxz hβ₁₂ hIcc hderiv_provider hpath

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
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem
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
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
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
  have hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2 :=
    lemma_17_5_2_active_range_on_Icc_of_high_temp_pair Λ hJ_pos hxz hIcc
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
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem
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
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem
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
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc hβ₁_pos hβ₁₂ hβ₂_lt
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

set_option maxHeartbeats 1200000 in
-- The concrete compact-ratio package supplies the uniform correlation lower
-- and denominator bounds used by the provider-shaped infinite-HLS bridge.
/-- **GJ §17.5 Lemma 17.5.2 concrete infinite-HLS upper bound from compact
ratio bounds**: high-temperature active-range membership gives the concrete
compact-ratio witnesses, which feed the provider-shaped uniform-correlation
lower bridge to obtain the endpoint upper-bound predicate. -/
theorem
    lemma_17_5_2_upper_bound_of_concrete_infinite_hls_compact_ratio_bounds_provider
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z) :
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
    lemma_17_5_2_active_range_on_Icc_of_high_temp_pair Λ hJ_pos hxz hIcc
  obtain ⟨C, H, hC_pos, hH_pos, hcInf_lower, hdenom_bound⟩ :=
    lemma_17_5_2_concrete_pseudoMass_compact_ratio_bounds_on_beta_interval
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho)
      hα hd hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem hrho hcorr
  exact
    lemma_17_5_2_upper_bound_of_concrete_infinite_hls_uniform_correlation_lower_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho)
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem
      hderiv_provider hC_pos hH_pos hcInf_lower
      (by
        intro β hβ
        simpa [lemma_17_5_2_concretePseudoMassBetaProfile] using
          hdenom_bound β hβ)

set_option maxHeartbeats 1200000 in
-- Adds the validating pseudo-mass decay lower side to the compact-ratio
-- provider-shaped upper-bound package.
/-- **GJ §17.5 Lemma 17.5.2 concrete infinite-HLS sandwich from compact ratio
bounds**: the compact-ratio witnesses close the provider-shaped upper-bound
side, and the validating pseudo-mass decay input supplies the lower side. -/
theorem
    lemma_17_5_2_sandwich_of_concrete_infinite_hls_compact_ratio_bounds_provider
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
    lemma_17_5_2_upper_bound_of_concrete_infinite_hls_compact_ratio_bounds_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho)
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem
      hderiv_provider
  refine ⟨K, hK, hK_conv, ?_⟩
  exact lemma_17_5_2_sandwich_of_decay_and_upper hα hrho hdecay hupper

set_option maxHeartbeats 1200000 in
-- Specializes the auxiliary compact interval to the beta interval itself.
/-- **GJ §17.5 Lemma 17.5.2 concrete infinite-HLS upper bound from compact
ratio bounds on its own beta interval**: the closed high-temperature interval
supplies the auxiliary compact interval hypotheses with `a = β₁` and
`b = β₂`. -/
theorem
    lemma_17_5_2_upper_bound_of_concrete_infinite_hls_compact_ratio_bounds_provider_on_self_Icc
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z) :
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
    lemma_17_5_2_upper_bound_of_concrete_infinite_hls_compact_ratio_bounds_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := β₁) (b := β₂) (rho := rho)
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc hβ₁_pos hβ₁₂ hβ₂_lt
      (fun β hβ => hβ) hderiv_provider

set_option maxHeartbeats 1200000 in
-- Adds the validating-decay lower side to the self-interval compact-ratio
-- provider-shaped upper-bound package.
/-- **GJ §17.5 Lemma 17.5.2 concrete infinite-HLS sandwich from compact ratio
bounds on its own beta interval**: the self-interval compact-ratio upper-bound
wrapper and the validating pseudo-mass decay input give the displayed
two-sided endpoint sandwich. -/
theorem
    lemma_17_5_2_sandwich_of_concrete_infinite_hls_compact_ratio_bounds_provider_on_self_Icc
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
    lemma_17_5_2_upper_bound_of_concrete_infinite_hls_compact_ratio_bounds_provider_on_self_Icc
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho)
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc hderiv_provider
  refine ⟨K, hK, hK_conv, ?_⟩
  exact lemma_17_5_2_sandwich_of_decay_and_upper hα hrho hdecay hupper

/-- **GJ §17.5 Lemma 17.5.2 concrete infinite-HLS capstone from compact
ratio bounds**: returns the HLS convolution witness, the named upper-bound
predicate, and the displayed two-sided endpoint sandwich for one constant. -/
theorem
    lemma_17_5_2_capstone_of_concrete_infinite_hls_compact_ratio_bounds_provider
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
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
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
    lemma_17_5_2_sandwich_of_concrete_infinite_hls_compact_ratio_bounds_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho)
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem
      hderiv_provider hdecay
  have hupper :
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) := by
    simpa [Lemma_17_5_2_UpperBound] using hupper_ineq
  exact ⟨K, hK_pos, hconv, hupper, hlower, hupper_ineq⟩

/-- **GJ §17.5 Lemma 17.5.2 self-interval concrete infinite-HLS capstone from
compact ratio bounds**: specializes the auxiliary compact interval to the beta
interval itself. -/
theorem
    lemma_17_5_2_capstone_of_concrete_infinite_hls_compact_ratio_bounds_provider_on_self_Icc
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
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
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
    lemma_17_5_2_sandwich_of_concrete_infinite_hls_compact_ratio_bounds_provider_on_self_Icc
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho)
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc hderiv_provider hdecay
  have hupper :
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) := by
    simpa [Lemma_17_5_2_UpperBound] using hupper_ineq
  exact ⟨K, hK_pos, hconv, hupper, hlower, hupper_ineq⟩

set_option maxHeartbeats 800000 in
-- The statement combines two existential HLS packages with the concrete
-- pseudo-mass endpoint, which needs extra elaboration budget.
/-- **GJ §17.5 Lemma 17.5.2 upper bound from a concrete infinite-HLS package
and path-rate comparison**: the derivative-limit provider supplies the
concrete infinite-HLS Lipschitz package, and the Step 115 path-rate comparison
closes the all-rate upper-bound assembly. -/
theorem lemma_17_5_2_upper_bound_of_concrete_infinite_hls_path_rate_provider
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ((∀ β' ∈ Set.Icc β₁ β₂,
          Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β' α K
            (lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z)) →
        ENNReal.ofReal (-Real.log (Real.tanh (β₂ * J))) ≤
          ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
            ENNReal.ofReal
              (pseudoMassFromParamsAtPair hα hrho d Λ
                (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) →
        Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
          (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho))) := by
  have hβ₂ : 0 < β₂ := (hIcc ⟨hβ₁₂, le_rfl⟩).1
  have hpkg :=
    lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_concrete_hls_constant_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hrho hderiv_provider
  have hpkg' :
      ∃ K : ℝ, 0 < K ∧
        (∀ x' y' : Fin d → ℤ,
          ∑' w : Fin d → ℤ,
              (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
              (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
        ((∀ β' ∈ Set.Icc β₁ β₂,
            Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β' α K
              (lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z)) →
          |(lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z β₂) ^
              (2 * α + 1) -
              (lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z β₁) ^
                (2 * α + 1)| ≤
            ↑(2 * α + 1) * K / rho * (β₂ - β₁)) := by
    simpa [lemma_17_5_2_concretePseudoMassBetaProfile] using hpkg
  obtain ⟨K, hK, hK_conv, hfinish⟩ :=
    lemma_17_5_2_upper_bound_of_exists_infinite_hls_lipschitz_and_path_rate_le
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (r := rho)
      (h := lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z)
      hα hd hrho hJ_pos hβ₂ hpkg'
  refine ⟨K, hK, hK_conv, fun hcomp hpath_le => ?_⟩
  exact hfinish hcomp hpath_le

set_option maxHeartbeats 800000 in
-- The sandwich statement repeats the same concrete HLS/path-rate package and
-- endpoint pseudo-mass terms, which needs extra elaboration budget.
/-- **GJ §17.5 Lemma 17.5.2 sandwich from a concrete infinite-HLS package and
path-rate comparison**: combines the preceding provider-shaped upper-bound
package with a validating endpoint pseudo-mass decay input. -/
theorem lemma_17_5_2_sandwich_of_concrete_infinite_hls_path_rate_provider
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ((∀ β' ∈ Set.Icc β₁ β₂,
          Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β' α K
            (lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z)) →
        ENNReal.ofReal (-Real.log (Real.tanh (β₂ * J))) ≤
          ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
            ENNReal.ofReal
              (pseudoMassFromParamsAtPair hα hrho d Λ
                (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) →
        ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
          ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
        latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
          ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
            ENNReal.ofReal
              (pseudoMassFromParamsAtPair hα hrho d Λ
                (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) := by
  have hβ₂ : 0 < β₂ := (hIcc ⟨hβ₁₂, le_rfl⟩).1
  have hpkg :=
    lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_concrete_hls_constant_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hrho hderiv_provider
  have hpkg' :
      ∃ K : ℝ, 0 < K ∧
        (∀ x' y' : Fin d → ℤ,
          ∑' w : Fin d → ℤ,
              (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
              (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
        ((∀ β' ∈ Set.Icc β₁ β₂,
            Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β' α K
              (lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z)) →
          |(lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z β₂) ^
              (2 * α + 1) -
              (lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z β₁) ^
                (2 * α + 1)| ≤
            ↑(2 * α + 1) * K / rho * (β₂ - β₁)) := by
    simpa [lemma_17_5_2_concretePseudoMassBetaProfile] using hpkg
  obtain ⟨K, hK, hK_conv, hfinish⟩ :=
    lemma_17_5_2_sandwich_of_exists_infinite_hls_lipschitz_and_path_rate_le
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (r := rho)
      (h := lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z)
      hα hd hrho hJ_pos hβ₂ hpkg' hdecay
  refine ⟨K, hK, hK_conv, fun hcomp hpath_le => ?_⟩
  exact hfinish hcomp hpath_le

/-- **GJ §17.5 Lemma 17.5.2 capstone from a concrete infinite-HLS package and
path-rate comparison**: returns the concrete HLS witness and, under the same
denominator-comparison and path-rate premises, both the named upper-bound
predicate and the displayed two-sided endpoint sandwich for one constant. -/
theorem lemma_17_5_2_capstone_of_concrete_infinite_hls_path_rate_provider
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (hderiv_provider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ((∀ β' ∈ Set.Icc β₁ β₂,
          Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β' α K
            (lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z)) →
        ENNReal.ofReal (-Real.log (Real.tanh (β₂ * J))) ≤
          ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
            ENNReal.ofReal
              (pseudoMassFromParamsAtPair hα hrho d Λ
                (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) →
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
                (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) := by
  have hβ₂ : 0 < β₂ := (hIcc ⟨hβ₁₂, le_rfl⟩).1
  have hpkg :=
    lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_concrete_hls_constant_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hrho hderiv_provider
  have hpkg' :
      ∃ K : ℝ, 0 < K ∧
        (∀ x' y' : Fin d → ℤ,
          ∑' w : Fin d → ℤ,
              (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
              (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
        ((∀ β' ∈ Set.Icc β₁ β₂,
            Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β' α K
              (lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z)) →
          |(lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z β₂) ^
              (2 * α + 1) -
              (lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z β₁) ^
                (2 * α + 1)| ≤
            ↑(2 * α + 1) * K / rho * (β₂ - β₁)) := by
    simpa [lemma_17_5_2_concretePseudoMassBetaProfile] using hpkg
  exact
    lemma_17_5_2_capstone_of_exists_infinite_hls_lipschitz_and_path_rate_le
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (r := rho)
      (h := lemma_17_5_2_concretePseudoMassBetaProfile hα hrho Λ J x z)
      hα hd hrho hJ_pos hβ₂ hpkg' hdecay

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
