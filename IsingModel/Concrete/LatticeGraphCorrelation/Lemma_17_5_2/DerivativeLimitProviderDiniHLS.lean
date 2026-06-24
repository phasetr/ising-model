import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DiniProvider
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProviderInfiniteHLS

/-!
# GJ §17.5 Lemma 17.5.2 capstone — Dini-provider infinite-HLS bridges

This module connects the Dini derivative-provider criteria to the
infinite-HLS bridge layer.  The statements consume the Dini-order and pointwise
derivative-profile inputs directly, then reuse the provider-based infinite-HLS
assembly.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and
  Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

/-- **GJ §17.5 Lemma 17.5.2 infinite HLS comparison from Dini provider
inputs**: Dini-order convergence, pointwise convergence, and limiting-profile
continuity supply the derivative-limit provider, so a uniform finite derivative
bound on the interval yields the infinite HLS denominator comparison at every
beta in the interval. -/
theorem
    lemma_17_5_2_infinite_hls_comparison_on_Icc_of_uniform_finite_deriv_bounds_dini
    {d α : ℕ} (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    (β₁ β₂ K : ℝ)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (h : ℝ → ℝ) (g' : ℝ → ℝ)
    (horder : Lemma_17_5_2_DerivativeProfileDiniOrder Λ J x z)
    (hg_cont : ContinuousOn g' (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β)))
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
  have hprovider :
      Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
    lemma_17_5_2_derivative_limit_provider_of_dini_order_finite_continuous
      Λ J x z g' horder hg_cont hpoint
  exact
    lemma_17_5_2_infinite_hls_comparison_on_Icc_of_uniform_finite_deriv_bounds_provider
      hd Λ J hJ_pos x z hxz β₁ β₂ K isOpen_Ioo (subset_refl _) hIcc h hprovider hfinite

/-- **GJ §17.5 Lemma 17.5.2 infinite pseudo-mass Lipschitz package from
Dini provider inputs**: Dini-order convergence supplies the derivative-limit
provider consumed by the infinite finite-HLS Lipschitz bridge. -/
theorem
    lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_dini_provider_inputs
    {d α : ℕ} (hαd : 2 * α > d) (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
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
    (horder : Lemma_17_5_2_DerivativeProfileDiniOrder Λ J x z)
    (hg_cont : ContinuousOn g' (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β))) :
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
  have hprovider :
      Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
    lemma_17_5_2_derivative_limit_provider_of_dini_order_finite_continuous
      Λ J x z g' horder hg_cont hpoint
  exact
    lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_finite_deriv_bounds_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho) (h := h)
      hαd hd hJ_pos hxz hβ₁₂ hIcc hrho
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hprovider

/-- **GJ §17.5 Lemma 17.5.2 infinite-HLS Lipschitz package from Dini provider
inputs**: Dini-order convergence supplies the provider used to derive the
infinite-volume correlation differentiability input, leaving the interval HLS
denominator comparison as the remaining analytic premise. -/
theorem
    lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_hls_constant_dini
    {d α : ℕ} (hαd : 2 * α > d) (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
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
    (horder : Lemma_17_5_2_DerivativeProfileDiniOrder Λ J x z)
    (hg_cont : ContinuousOn g' (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ((∀ β' ∈ Set.Icc β₁ β₂,
          Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β' α K h) →
        |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
          ↑(2 * α + 1) * K / rho * (β₂ - β₁)) := by
  have hprovider :
      Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
    lemma_17_5_2_derivative_limit_provider_of_dini_order_finite_continuous
      Λ J x z g' horder hg_cont hpoint
  exact
    lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_hls_constant_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho) (h := h)
      hαd hd hJ_pos hxz hβ₁₂ hIcc hrho
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hprovider

/-- **GJ §17.5 Lemma 17.5.2 concrete infinite-HLS Lipschitz package from Dini
provider inputs**: specializes the HLS Lipschitz profile to the concrete
pseudo-mass profile. -/
theorem
    lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_concrete_hls_constant_dini
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    {rho : ℝ} (hrho : 0 < rho)
    (g' : ℝ → ℝ)
    (horder : Lemma_17_5_2_DerivativeProfileDiniOrder Λ J x z)
    (hg_cont : ContinuousOn g' (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β))) :
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
  have hprovider :
      Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
    lemma_17_5_2_derivative_limit_provider_of_dini_order_finite_continuous
      Λ J x z g' horder hg_cont hpoint
  exact
    lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_concrete_hls_constant_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hrho hprovider

set_option maxHeartbeats 1200000 in
-- The Dini provider inputs feed the self-interval uniform-correlation
-- infinite-HLS upper-bound wrapper added at the provider layer.
/-- **GJ §17.5 Lemma 17.5.2 self-interval uniform-correlation infinite-HLS
upper bound from Dini provider inputs**: Dini-order derivative-profile control
supplies the derivative-limit provider, while the uniform infinite-correlation
lower and denominator upper bounds supply the concrete ratio-lower input. -/
theorem
    lemma_17_5_2_upper_bound_of_concrete_infinite_hls_uniform_correlation_lower_on_self_Icc_dini
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (g' : ℝ → ℝ)
    (horder : Lemma_17_5_2_DerivativeProfileDiniOrder Λ J x z)
    (hg_cont : ContinuousOn g' (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β)))
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
  have hprovider :
      Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
    lemma_17_5_2_derivative_limit_provider_of_dini_order_finite_continuous
      Λ J x z g' horder hg_cont hpoint
  exact
    lemma_17_5_2_upper_bound_of_concrete_infinite_hls_uniform_correlation_lower_provider_on_self_Icc
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho)
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc hprovider hC_pos hH_pos
      hcInf_lower hdenom_bound

set_option maxHeartbeats 1200000 in
-- Adds the validating pseudo-mass decay lower side to the Dini self-interval
-- uniform-correlation upper-bound wrapper.
/-- **GJ §17.5 Lemma 17.5.2 self-interval uniform-correlation infinite-HLS
sandwich from Dini provider inputs**: the Dini derivative-profile inputs
provide the derivative-limit provider, while the validating endpoint
pseudo-mass decay input supplies the lower side. -/
theorem
    lemma_17_5_2_sandwich_of_concrete_infinite_hls_uniform_correlation_lower_on_self_Icc_dini
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (g' : ℝ → ℝ)
    (horder : Lemma_17_5_2_DerivativeProfileDiniOrder Λ J x z)
    (hg_cont : ContinuousOn g' (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β)))
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
  have hprovider :
      Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
    lemma_17_5_2_derivative_limit_provider_of_dini_order_finite_continuous
      Λ J x z g' horder hg_cont hpoint
  exact
    lemma_17_5_2_sandwich_of_concrete_infinite_hls_uniform_correlation_lower_provider_on_self_Icc
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho)
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc hprovider hdecay hC_pos
      hH_pos hcInf_lower hdenom_bound

/-- **GJ §17.5 Lemma 17.5.2 self-interval uniform-correlation infinite-HLS
capstone from Dini provider inputs**: returns the named upper-bound predicate
and sandwich for the same HLS constant. -/
theorem
    lemma_17_5_2_capstone_of_concrete_infinite_hls_uniform_correlation_lower_on_self_Icc_dini
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (g' : ℝ → ℝ)
    (horder : Lemma_17_5_2_DerivativeProfileDiniOrder Λ J x z)
    (hg_cont : ContinuousOn g' (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β)))
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
  have hprovider :
      Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
    lemma_17_5_2_derivative_limit_provider_of_dini_order_finite_continuous
      Λ J x z g' horder hg_cont hpoint
  exact
    lemma_17_5_2_capstone_of_concrete_infinite_hls_uniform_correlation_lower_provider_on_self_Icc
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho)
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc hprovider hdecay hC_pos
      hH_pos hcInf_lower hdenom_bound

set_option maxHeartbeats 1200000 in
-- The Dini provider inputs feed the compact-ratio infinite-HLS upper-bound
-- wrapper added at the provider layer.
/-- **GJ §17.5 Lemma 17.5.2 compact-ratio infinite-HLS upper bound from Dini
provider inputs**: Dini-order derivative-profile control supplies the
derivative-limit provider, and the concrete compact-ratio package supplies the
interval ratio witnesses used by the infinite-HLS upper-bound bridge. -/
theorem
    lemma_17_5_2_upper_bound_of_concrete_infinite_hls_compact_ratio_bounds_dini
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    (g' : ℝ → ℝ)
    (horder : Lemma_17_5_2_DerivativeProfileDiniOrder Λ J x z)
    (hg_cont : ContinuousOn g' (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) := by
  have hprovider :
      Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
    lemma_17_5_2_derivative_limit_provider_of_dini_order_finite_continuous
      Λ J x z g' horder hg_cont hpoint
  exact
    lemma_17_5_2_upper_bound_of_concrete_infinite_hls_compact_ratio_bounds_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho)
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem hprovider

set_option maxHeartbeats 1200000 in
-- Adds the lower validating pseudo-mass decay side to the Dini compact-ratio
-- infinite-HLS upper-bound wrapper.
/-- **GJ §17.5 Lemma 17.5.2 compact-ratio infinite-HLS sandwich from Dini
provider inputs**: the Dini derivative-profile inputs provide the
derivative-limit provider, while the validating endpoint pseudo-mass decay
input supplies the lower side of the displayed sandwich. -/
theorem
    lemma_17_5_2_sandwich_of_concrete_infinite_hls_compact_ratio_bounds_dini
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    (g' : ℝ → ℝ)
    (horder : Lemma_17_5_2_DerivativeProfileDiniOrder Λ J x z)
    (hg_cont : ContinuousOn g' (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β)))
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
  have hprovider :
      Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
    lemma_17_5_2_derivative_limit_provider_of_dini_order_finite_continuous
      Λ J x z g' horder hg_cont hpoint
  exact
    lemma_17_5_2_sandwich_of_concrete_infinite_hls_compact_ratio_bounds_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho)
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem hprovider
      hdecay

set_option maxHeartbeats 1200000 in
-- Self-interval Dini wrapper for the compact-ratio infinite-HLS upper bound.
/-- **GJ §17.5 Lemma 17.5.2 self-interval compact-ratio infinite-HLS upper
bound from Dini provider inputs**: specializes the auxiliary compact interval
to the beta interval itself. -/
theorem
    lemma_17_5_2_upper_bound_of_concrete_infinite_hls_compact_ratio_bounds_on_self_Icc_dini
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (g' : ℝ → ℝ)
    (horder : Lemma_17_5_2_DerivativeProfileDiniOrder Λ J x z)
    (hg_cont : ContinuousOn g' (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) := by
  have hprovider :
      Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
    lemma_17_5_2_derivative_limit_provider_of_dini_order_finite_continuous
      Λ J x z g' horder hg_cont hpoint
  exact
    lemma_17_5_2_upper_bound_of_concrete_infinite_hls_compact_ratio_bounds_provider_on_self_Icc
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho)
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc hprovider

set_option maxHeartbeats 1200000 in
-- Self-interval Dini wrapper adding the validating-decay lower side.
/-- **GJ §17.5 Lemma 17.5.2 self-interval compact-ratio infinite-HLS sandwich
from Dini provider inputs**: specializes the compact-ratio sandwich bridge to
the beta interval itself. -/
theorem
    lemma_17_5_2_sandwich_of_concrete_infinite_hls_compact_ratio_bounds_on_self_Icc_dini
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (g' : ℝ → ℝ)
    (horder : Lemma_17_5_2_DerivativeProfileDiniOrder Λ J x z)
    (hg_cont : ContinuousOn g' (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β)))
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
  have hprovider :
      Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
    lemma_17_5_2_derivative_limit_provider_of_dini_order_finite_continuous
      Λ J x z g' horder hg_cont hpoint
  exact
    lemma_17_5_2_sandwich_of_concrete_infinite_hls_compact_ratio_bounds_provider_on_self_Icc
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho)
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc hprovider hdecay

/-- **GJ §17.5 Lemma 17.5.2 compact-ratio infinite-HLS capstone from
Dini-order provider inputs**: returns the HLS convolution witness, named
upper-bound predicate, and endpoint sandwich for one constant. -/
theorem
    lemma_17_5_2_capstone_of_concrete_infinite_hls_compact_ratio_bounds_dini
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    (g' : ℝ → ℝ)
    (horder : Lemma_17_5_2_DerivativeProfileDiniOrder Λ J x z)
    (hg_cont : ContinuousOn g' (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β)))
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
  have hprovider :
      Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
    lemma_17_5_2_derivative_limit_provider_of_dini_order_finite_continuous
      Λ J x z g' horder hg_cont hpoint
  exact
    lemma_17_5_2_capstone_of_concrete_infinite_hls_compact_ratio_bounds_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (a := a) (b := b) (rho := rho)
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem hprovider
      hdecay

/-- **GJ §17.5 Lemma 17.5.2 self-interval compact-ratio infinite-HLS capstone
from Dini-order provider inputs**. -/
theorem
    lemma_17_5_2_capstone_of_concrete_infinite_hls_compact_ratio_bounds_on_self_Icc_dini
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (g' : ℝ → ℝ)
    (horder : Lemma_17_5_2_DerivativeProfileDiniOrder Λ J x z)
    (hg_cont : ContinuousOn g' (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β)))
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
  have hprovider :
      Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
    lemma_17_5_2_derivative_limit_provider_of_dini_order_finite_continuous
      Λ J x z g' horder hg_cont hpoint
  exact
    lemma_17_5_2_capstone_of_concrete_infinite_hls_compact_ratio_bounds_provider_on_self_Icc
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho)
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc hprovider hdecay

set_option maxHeartbeats 800000 in
-- The Dini statement combines the Dini provider input with the concrete
-- HLS/path-rate upper-bound package.
/-- **GJ §17.5 Lemma 17.5.2 upper bound from Dini concrete infinite-HLS and
path-rate inputs**: Dini-order derivative-profile control supplies the
provider, then the concrete infinite-HLS package and Step 115 path-rate
comparison close the upper-bound assembly. -/
theorem lemma_17_5_2_upper_bound_of_concrete_infinite_hls_path_rate_dini
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (g' : ℝ → ℝ)
    (horder : Lemma_17_5_2_DerivativeProfileDiniOrder Λ J x z)
    (hg_cont : ContinuousOn g' (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β)))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet] :
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
  have hprovider :
      Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
    lemma_17_5_2_derivative_limit_provider_of_dini_order_finite_continuous
      Λ J x z g' horder hg_cont hpoint
  exact
    lemma_17_5_2_upper_bound_of_concrete_infinite_hls_path_rate_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho)
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc hprovider

set_option maxHeartbeats 800000 in
-- The sandwich variant repeats the Dini provider inputs and concrete endpoint
-- package, so it needs the same local elaboration budget.
/-- **GJ §17.5 Lemma 17.5.2 sandwich from Dini concrete infinite-HLS and
path-rate inputs**: adds the endpoint validating decay input to the Dini
upper-bound package. -/
theorem lemma_17_5_2_sandwich_of_concrete_infinite_hls_path_rate_dini
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (g' : ℝ → ℝ)
    (horder : Lemma_17_5_2_DerivativeProfileDiniOrder Λ J x z)
    (hg_cont : ContinuousOn g' (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β)))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
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
  have hprovider :
      Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
    lemma_17_5_2_derivative_limit_provider_of_dini_order_finite_continuous
      Λ J x z g' horder hg_cont hpoint
  exact
    lemma_17_5_2_sandwich_of_concrete_infinite_hls_path_rate_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho)
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc hprovider hdecay

/-- **GJ §17.5 Lemma 17.5.2 capstone from Dini concrete infinite-HLS and
path-rate inputs**: returns the concrete HLS witness and, under the same
denominator-comparison and path-rate premises, both the named upper-bound
predicate and endpoint sandwich for one constant. -/
theorem lemma_17_5_2_capstone_of_concrete_infinite_hls_path_rate_dini
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (g' : ℝ → ℝ)
    (horder : Lemma_17_5_2_DerivativeProfileDiniOrder Λ J x z)
    (hg_cont : ContinuousOn g' (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β)))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
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
  have hprovider :
      Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
    lemma_17_5_2_derivative_limit_provider_of_dini_order_finite_continuous
      Λ J x z g' horder hg_cont hpoint
  exact
    lemma_17_5_2_capstone_of_concrete_infinite_hls_path_rate_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho)
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc hprovider hdecay

/-- **GJ §17.5 Lemma 17.5.2 enlarged finite-HLS package from Dini provider
inputs**: Dini-order convergence supplies the provider needed by the
path-rate enlarged finite-HLS package. -/
theorem
    lemma_17_5_2_enlarged_finite_hls_lipschitz_package_with_path_rate_of_dini
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
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
    (horder : Lemma_17_5_2_DerivativeProfileDiniOrder Λ J x z)
    (hg_cont : ContinuousOn g' (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β))) :
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
  have hprovider :
      Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
    lemma_17_5_2_derivative_limit_provider_of_dini_order_finite_continuous
      Λ J x z g' horder hg_cont hpoint
  exact
    lemma_17_5_2_enlarged_finite_hls_lipschitz_package_with_path_rate_of_derivative_limit_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hrho
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hm_pos hprovider

/-- **GJ §17.5 Lemma 17.5.2 enlarged finite-HLS upper bound from Dini
provider inputs**: combines the Dini-order derivative provider criterion
with the provider-based enlarged finite-HLS upper-bound assembly. -/
theorem
    lemma_17_5_2_upper_bound_of_enlarged_finite_hls_lipschitz_package_of_dini
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
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
    (horder : Lemma_17_5_2_DerivativeProfileDiniOrder Λ J x z)
    (hg_cont : ContinuousOn g' (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β))) :
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
  have hprovider :
      Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
    lemma_17_5_2_derivative_limit_provider_of_dini_order_finite_continuous
      Λ J x z g' horder hg_cont hpoint
  exact
    lemma_17_5_2_upper_bound_of_enlarged_finite_hls_lipschitz_package_of_derivative_limit_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hrho
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hm_pos hprovider

/-- **GJ §17.5 Lemma 17.5.2 enlarged finite-HLS sandwich from Dini provider
inputs**: adds the lower validating-decay input to the Dini-provider upper
bound bridge, returning the displayed two-sided sandwich. -/
theorem
    lemma_17_5_2_sandwich_of_enlarged_finite_hls_lipschitz_package_of_dini
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
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
    (horder : Lemma_17_5_2_DerivativeProfileDiniOrder Λ J x z)
    (hg_cont : ContinuousOn g' (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β)))
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
  have hprovider :
      Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
    lemma_17_5_2_derivative_limit_provider_of_dini_order_finite_continuous
      Λ J x z g' horder hg_cont hpoint
  exact
    lemma_17_5_2_sandwich_of_enlarged_finite_hls_lipschitz_package_of_derivative_limit_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hrho
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hm_pos hprovider hdecay

end Ambient
end IsingModel
