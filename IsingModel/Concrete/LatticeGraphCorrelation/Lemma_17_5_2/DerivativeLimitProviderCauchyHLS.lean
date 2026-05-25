import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProviderCriteria
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProviderInfiniteHLS

/-!
# GJ §17.5 Lemma 17.5.2 capstone — Cauchy-provider infinite-HLS bridges

This module connects the compact-Cauchy derivative-provider criteria to the
infinite-HLS bridge layer.  The statements consume the Cauchy and pointwise
derivative-profile inputs directly, then reuse the provider-based infinite-HLS
assembly.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and
  Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

/-- **GJ §17.5 Lemma 17.5.2 infinite HLS comparison from Cauchy provider
inputs**: compact-interval metric Cauchy control and pointwise convergence of
the finite derivative profiles supply the derivative-limit provider, so a
uniform finite derivative bound on the interval yields the infinite HLS
denominator comparison at every beta in the interval. -/
theorem
    lemma_17_5_2_infinite_hls_comparison_on_Icc_of_uniform_finite_deriv_bounds_cauchy
    {d α : ℕ} (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    (β₁ β₂ K : ℝ)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (h : ℝ → ℝ) (g' : ℝ → ℝ)
    (hcauchy :
      ∀ a b : ℝ,
        Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
          ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
            ∀ β ∈ Set.Icc a b,
              dist
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} m) β)
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β) < ε)
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
    lemma_17_5_2_derivative_limit_provider_of_metricCauchy_on_Icc
      Λ J x z g' hcauchy hpoint
  exact
    lemma_17_5_2_infinite_hls_comparison_on_Icc_of_uniform_finite_deriv_bounds_provider
      hd Λ J hJ_pos x z hxz β₁ β₂ K hIcc h hprovider hfinite

/-- **GJ §17.5 Lemma 17.5.2 infinite pseudo-mass Lipschitz package from
Cauchy provider inputs**: the compact-interval Cauchy criterion supplies the
derivative-limit provider consumed by the infinite finite-HLS Lipschitz bridge. -/
theorem
    lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_cauchy_provider_inputs
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
    (hcauchy :
      ∀ a b : ℝ,
        Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
          ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
            ∀ β ∈ Set.Icc a b,
              dist
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} m) β)
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β) < ε)
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
    lemma_17_5_2_derivative_limit_provider_of_metricCauchy_on_Icc
      Λ J x z g' hcauchy hpoint
  exact
    lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_finite_deriv_bounds_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho) (h := h)
      hαd hd hJ_pos hxz hβ₁₂ hIcc hrho
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hprovider

/-- **GJ §17.5 Lemma 17.5.2 enlarged finite-HLS package from Cauchy provider
inputs**: compact-interval Cauchy control supplies the provider needed by the
path-rate enlarged finite-HLS package. -/
theorem
    lemma_17_5_2_enlarged_finite_hls_lipschitz_package_with_path_rate_of_cauchy
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
    (hcauchy :
      ∀ a b : ℝ,
        Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
          ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
            ∀ β ∈ Set.Icc a b,
              dist
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} m) β)
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β) < ε)
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
    lemma_17_5_2_derivative_limit_provider_of_metricCauchy_on_Icc
      Λ J x z g' hcauchy hpoint
  exact
    lemma_17_5_2_enlarged_finite_hls_lipschitz_package_with_path_rate_of_derivative_limit_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hrho
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hm_pos hprovider

/-- **GJ §17.5 Lemma 17.5.2 enlarged finite-HLS upper bound from Cauchy
provider inputs**: combines the compact-Cauchy derivative provider criterion
with the provider-based enlarged finite-HLS upper-bound assembly. -/
theorem
    lemma_17_5_2_upper_bound_of_enlarged_finite_hls_lipschitz_package_of_cauchy
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
    (hcauchy :
      ∀ a b : ℝ,
        Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
          ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
            ∀ β ∈ Set.Icc a b,
              dist
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} m) β)
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β) < ε)
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
    lemma_17_5_2_derivative_limit_provider_of_metricCauchy_on_Icc
      Λ J x z g' hcauchy hpoint
  exact
    lemma_17_5_2_upper_bound_of_enlarged_finite_hls_lipschitz_package_of_derivative_limit_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hrho
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hm_pos hprovider

/-- **GJ §17.5 Lemma 17.5.2 enlarged finite-HLS sandwich from Cauchy provider
inputs**: adds the lower validating-decay input to the Cauchy-provider upper
bound bridge, returning the displayed two-sided sandwich. -/
theorem
    lemma_17_5_2_sandwich_of_enlarged_finite_hls_lipschitz_package_of_cauchy
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
    (hcauchy :
      ∀ a b : ℝ,
        Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
          ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
            ∀ β ∈ Set.Icc a b,
              dist
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} m) β)
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β) < ε)
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
    lemma_17_5_2_derivative_limit_provider_of_metricCauchy_on_Icc
      Λ J x z g' hcauchy hpoint
  exact
    lemma_17_5_2_sandwich_of_enlarged_finite_hls_lipschitz_package_of_derivative_limit_provider
      (d := d) (α := α) (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) (rho := rho) (h := h)
      hα hαd hd hJ_pos hxz hβ₁₂ hIcc hrho
      hh_diff hh_nonneg hg_eq hh_pos hc_pos hm_pos hprovider hdecay

end Ambient
end IsingModel
