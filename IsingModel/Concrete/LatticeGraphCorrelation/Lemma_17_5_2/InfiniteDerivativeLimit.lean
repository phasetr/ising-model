import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSConstants
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempLipschitzTendstoLocallyUniformly
import IsingModel.Concrete.LatticeGraphCorrelation.PointwiseRegularityBetaHZero
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# GJ §17.5 Lemma 17.5.2 capstone — infinite derivative-limit bridge

This module is part of the split
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2` development.  It
isolates the remaining finite-to-infinite differentiability passage needed by
the HLS denominator comparison: if the finite-volume β-derivatives converge
locally uniformly on the high-temperature interval, then the thermodynamic-limit
two-point function has the corresponding β-derivative, and a bound on the
limit derivative gives the named infinite-volume HLS denominator comparison.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and
  Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

/-- **GJ §17.5 Lemma 17.5.2 infinite β-derivative from derivative convergence**:
on the open high-temperature interval, local uniform convergence of the
finite-volume β-derivatives upgrades the already established locally uniform
convergence `corr_n → corr_∞` to a `HasDerivAt` statement for `corr_∞`.

This is the differentiability passage needed before the infinite-volume HLS
denominator comparison can be discharged from finite-volume Lebowitz/HLS
estimates. -/
theorem correlationInfinite_hasDerivAt_beta_of_tendstoLocallyUniformlyOn_deriv
    {d : ℕ} (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J)
    (g' : ℝ → ℝ)
    {t : Set ℝ} (ht_open : IsOpen t)
    (ht_sub : t ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {r_val, s_val} n) β)
        g' Filter.atTop t) :
    ∀ β ∈ t,
      HasDerivAt
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {r_val, s_val})
        (g' β) β := by
  intro β hβ
  let s : Set ℝ := t
  let f : ℕ → ℝ → ℝ := fun n β' =>
    Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β'⟩ : IsingParams ℝ) {r_val, s_val} n
  let g : ℝ → ℝ := fun β' =>
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β'⟩ : IsingParams ℝ) {r_val, s_val}
  have hderiv_lim' : TendstoLocallyUniformlyOn (deriv ∘ f) g' Filter.atTop s := by
    simpa [s, f, Function.comp_def] using hderiv_lim
  have hdiff : ∀ᶠ n in Filter.atTop, DifferentiableOn ℝ (f n) s := by
    filter_upwards [] with n
    simpa [f] using
      (correlationAlongExhaustion_differentiable_beta Λ {r_val, s_val} J n).differentiableOn
  have hfg : ∀ x ∈ s, Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (g x)) := by
    intro x hx
    have hconv :=
      correlationAlongExhaustion_tendstoLocallyUniformlyOn_beta_of_high_temp_open
        hd Λ r_val s_val hrs J hJ_pos
    simpa [s, f, g] using hconv.tendsto_at (ht_sub hx)
  exact hasDerivAt_of_tendsto_locally_uniformly_on'
    (f := f) (g := g) (g' := g') (l := Filter.atTop) (s := s)
    ht_open hderiv_lim' hdiff hfg hβ

/-- **GJ §17.5 Lemma 17.5.2 infinite HLS denominator comparison from an
identified infinite derivative**: once the derivative of the thermodynamic-limit
two-point function is identified with `g' β`, a bound on `|g' β|` gives the
named infinite-volume HLS denominator comparison. -/
theorem lemma_17_5_2_infinite_hls_denominator_comparison_of_deriv_bound
    {d α : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ)
    (β K : ℝ) (h : ℝ → ℝ) {gβ' : ℝ}
    (hdiff :
      HasDerivAt
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
        gβ' β)
    (hbound :
      |gβ'| ≤
        K *
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} /
          (h β) ^ (2 * α)) :
    Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β α K h := by
  have hderiv :
      deriv
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
        β = gβ' :=
    hdiff.deriv
  simpa [Lemma_17_5_2_InfiniteHLSDenominatorComparison, hderiv] using hbound

/-- **GJ §17.5 Lemma 17.5.2 infinite HLS denominator comparison from derivative
convergence**: local uniform convergence of the finite-volume β-derivatives
identifies the derivative of `corr_∞`; a pointwise HLS bound on the limiting
derivative then gives the named infinite-volume denominator comparison. -/
theorem lemma_17_5_2_infinite_hls_denominator_comparison_of_deriv_limit_bound
    {d α : ℕ} (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    (β K : ℝ)
    {t : Set ℝ} (ht_open : IsOpen t)
    (ht_sub : t ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (hβ : β ∈ t)
    (h : ℝ → ℝ) (g' : ℝ → ℝ)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop t)
    (hbound :
      |g' β| ≤
        K *
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} /
          (h β) ^ (2 * α)) :
    Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β α K h := by
  have hdiff :=
    correlationInfinite_hasDerivAt_beta_of_tendstoLocallyUniformlyOn_deriv
      hd Λ x z hxz J hJ_pos g' ht_open ht_sub hderiv_lim β hβ
  exact lemma_17_5_2_infinite_hls_denominator_comparison_of_deriv_bound
    Λ J x z β K h hdiff hbound

/-- **GJ §17.5 Lemma 17.5.2 finite HLS derivative bounds pass to the
infinite derivative limit**: if the finite-volume derivative profiles converge
at `β` to the limiting derivative value, the finite-volume correlations
converge at `β` to `corr_∞`, and the finite HLS derivative bound holds
eventually in the exhaustion, then the same HLS bound holds for the limiting
derivative.

This is the order/topology handoff behind the infinite HLS denominator
comparison.  The substantive analytic inputs are the derivative convergence and
the eventual finite-stage HLS bounds. -/
theorem lemma_17_5_2_infinite_hls_deriv_bound_of_finite_profile_bounds
    {d α : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ)
    (β K : ℝ) (h : ℝ → ℝ) (g' : ℝ → ℝ)
    (hderiv_point :
      Filter.Tendsto
        (fun n =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        Filter.atTop (nhds (g' β)))
    (hcorr_point :
      Filter.Tendsto
        (fun n =>
          Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n)
        Filter.atTop
        (nhds
          (Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z})))
    (hfinite :
      ∀ᶠ n in Filter.atTop,
        |deriv (fun β' =>
          Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤
          K *
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n /
            (h β) ^ (2 * α)) :
      |g' β| ≤
        K *
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} /
          (h β) ^ (2 * α) := by
  refine le_of_tendsto_of_tendsto ?_ ?_ hfinite
  · exact (continuous_abs.tendsto (g' β)).comp hderiv_point
  · exact (tendsto_const_nhds.mul hcorr_point).div_const ((h β) ^ (2 * α))

/-- **GJ §17.5 Lemma 17.5.2 infinite HLS denominator comparison from finite
HLS derivative bounds**: local uniform convergence of finite-volume
β-derivatives identifies the infinite derivative, while eventual finite-stage
HLS derivative bounds pass to the limit and discharge the named infinite
denominator comparison. -/
theorem lemma_17_5_2_infinite_hls_denominator_comparison_of_finite_deriv_bounds
    {d α : ℕ} (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    (β K : ℝ)
    {t : Set ℝ} (ht_open : IsOpen t)
    (ht_sub : t ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (hβ : β ∈ t)
    (h : ℝ → ℝ) (g' : ℝ → ℝ)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop t)
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
  have hcorr_lim :=
    correlationAlongExhaustion_tendstoLocallyUniformlyOn_beta_of_high_temp_open
      hd Λ x z hxz J hJ_pos
  have hbound :=
    lemma_17_5_2_infinite_hls_deriv_bound_of_finite_profile_bounds
      Λ J x z β K h g' (hderiv_lim.tendsto_at hβ) (hcorr_lim.tendsto_at (ht_sub hβ))
      hfinite
  exact lemma_17_5_2_infinite_hls_denominator_comparison_of_deriv_limit_bound
    hd Λ J hJ_pos x z hxz β K ht_open ht_sub hβ h g' hderiv_lim hbound

/-- **GJ §17.5 Lemma 17.5.2 interval finite-HLS limit bridge**: if an interval
lies in the open high-temperature region, the finite-volume β-derivatives
converge locally uniformly there, and the finite-stage HLS derivative bound
holds eventually at each point of the interval, then the infinite HLS
denominator comparison holds at every point of the interval.

This is the interval-shaped input consumed by the infinite HLS Lipschitz
bridge. -/
theorem
    lemma_17_5_2_infinite_hls_denominator_comparison_on_Icc_of_finite_deriv_bounds
    {d α : ℕ} (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    (β₁ β₂ K : ℝ)
    {t : Set ℝ} (ht_open : IsOpen t)
    (ht_sub : t ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (hIcc : Set.Icc β₁ β₂ ⊆ t)
    (h : ℝ → ℝ) (g' : ℝ → ℝ)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop t)
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
  intro β hβ
  exact lemma_17_5_2_infinite_hls_denominator_comparison_of_finite_deriv_bounds
    hd Λ J hJ_pos x z hxz β K ht_open ht_sub (hIcc hβ) h g' hderiv_lim (hfinite β hβ)

/-- **GJ §17.5 Lemma 17.5.2 interval finite-HLS limit bridge, uniform-eventual
form**: a single eventual finite-stage HLS derivative bound, uniform over the
closed interval, is enough to provide the interval family of infinite HLS
denominator comparisons. -/
theorem
    lemma_17_5_2_infinite_hls_denominator_comparison_on_Icc_of_uniform_finite_deriv_bounds
    {d α : ℕ} (hd : 1 ≤ d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    (β₁ β₂ K : ℝ)
    {t : Set ℝ} (ht_open : IsOpen t)
    (ht_sub : t ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (hIcc : Set.Icc β₁ β₂ ⊆ t)
    (h : ℝ → ℝ) (g' : ℝ → ℝ)
    (hderiv_lim :
      TendstoLocallyUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop t)
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
  refine
    lemma_17_5_2_infinite_hls_denominator_comparison_on_Icc_of_finite_deriv_bounds
      hd Λ J hJ_pos x z hxz β₁ β₂ K ht_open ht_sub hIcc h g' hderiv_lim ?_
  intro β hβ
  exact hfinite.mono fun n hn => hn β hβ

end Ambient
end IsingModel
