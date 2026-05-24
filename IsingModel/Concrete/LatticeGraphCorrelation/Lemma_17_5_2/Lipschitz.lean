import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.BetaDerivBridges

/-!
# GJ §17.5 Lemma 17.5.2 capstone — interval Lipschitz bridges

This module is part of the split
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2` development. It
collects the finite-stage and infinite-volume HLS-constant interval Lipschitz
estimates for `β ↦ (h β)^(2α+1)`, plus the infinite-volume HLS-constant
derivative bound for the same target, all carrying the convolution inequality
from `lemma_17_5_2_hls_convolution_constant`.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and
  Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

/-- **GJ §17.5 Lemma 17.5.2 finite-stage pseudo-mass Lipschitz bound**:
on an interval contained in the high-temperature window `[a,b]`, pointwise HLS
denominator comparisons for the finite-stage correlation imply the Lipschitz
estimate for `β ↦ (h β)^(2α+1)`.

This is the finite-volume concrete analogue of `pseudoMass_pow_succ_lipschitz`,
with the correlation derivative input supplied by
`lemma_17_5_2_beta_pseudoMass_power_deriv_le_of_high_temp_bound` at each point.

References: Glimm--Jaffe §17.5, Theorem 17.5.1 proof and Lemma 17.5.2,
pp.~311--312. -/
theorem lemma_17_5_2_beta_pseudoMass_pow_succ_lipschitz_of_high_temp_bound
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ : 0 ≤ J)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (n : ℕ) (r s : ↑(Λ.volume n)) (hrs : r ≠ s)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hβ_mem : ∀ β' ∈ Set.Icc β₁ β₂, β' ∈ Set.Icc a b)
    {α : ℕ} {rho K : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ}
    (hh_diff : ∀ β' ∈ Set.Icc β₁ β₂, HasDerivAt h (deriv h β') β')
    (hh_nonneg : ∀ β' ∈ Set.Icc β₁ β₂, 0 ≤ h β')
    (hg_eq : ∀ β' ∈ Set.Icc β₁ β₂,
      (fun γ => pseudoMassG α rho (h γ)) =ᶠ[nhds β']
        (fun γ =>
          IsingModel.correlation
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
            (⟨J, 0, γ⟩ : IsingParams ℝ) {r, s}))
    (hh_pos : ∀ β' ∈ Set.Icc β₁ β₂, 0 < h β')
    (hc_pos : ∀ β' ∈ Set.Icc β₁ β₂,
      0 <
        IsingModel.correlation
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s})
    (hcomp : ∀ β' ∈ Set.Icc β₁ β₂,
      let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
      J * M ^ 2 + J * (4 * ↑d) ≤
        K *
          IsingModel.correlation
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
            (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s} /
          (h β') ^ (2 * α)) :
    |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
      ↑(2 * α + 1) * K / rho * (β₂ - β₁) := by
  rw [← Real.norm_eq_abs]
  have hMVT := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun β' => (h β') ^ (2 * α + 1))
    (f' := fun β' => ↑(2 * α + 1) * (h β') ^ (2 * α) * deriv h β')
    (a := β₁) (b := β₂) (C := ↑(2 * α + 1) * K / rho)
    (hf := fun β' hβ' => by
      have hβ'_mem : β' ∈ Set.Icc β₁ β₂ := hβ'
      have hderiv := (hh_diff β' hβ'_mem).fun_pow (2 * α + 1)
      have hexp : 2 * α + 1 - 1 = 2 * α := by omega
      rw [hexp] at hderiv
      exact hderiv.hasDerivWithinAt)
    (bound := fun β' hβ' => by
      have hβ'_mem : β' ∈ Set.Icc β₁ β₂ := Set.Ico_subset_Icc_self hβ'
      have h1 :=
        lemma_17_5_2_beta_pseudoMass_power_deriv_le_of_high_temp_bound
          Λ J hJ a b ha hab hlt n r s hrs β' (hβ_mem β' hβ'_mem)
          (α := α) (rho := rho) (K := K) hrho
          (hh_diff β' hβ'_mem) (hh_nonneg β' hβ'_mem) (hg_eq β' hβ'_mem)
          (hh_pos β' hβ'_mem) (hc_pos β' hβ'_mem) (hcomp β' hβ'_mem)
      have hpow_pos : (0 : ℝ) < ↑(2 * α + 1) := by
        exact_mod_cast Nat.succ_pos (2 * α)
      have hm_pow_pos : 0 < (h β') ^ (2 * α) := pow_pos (hh_pos β' hβ'_mem) _
      simp only [Real.norm_eq_abs, abs_mul, abs_of_pos hpow_pos, abs_of_pos hm_pow_pos]
      calc ↑(2 * α + 1) * (h β') ^ (2 * α) * |deriv h β'|
          = ↑(2 * α + 1) * ((h β') ^ (2 * α) * |deriv h β'|) := by ring
        _ ≤ ↑(2 * α + 1) * (K / rho) := mul_le_mul_of_nonneg_left h1 hpow_pos.le
        _ = ↑(2 * α + 1) * K / rho := by ring)
  have hmem : β₂ ∈ Set.Icc β₁ β₂ := Set.right_mem_Icc.mpr hβ₁₂
  simpa using hMVT β₂ hmem

/-- **GJ §17.5 Lemma 17.5.2 HLS-constant interval Lipschitz bridge**:
under the HLS exponent condition `2α > d`, choose a positive HLS convolution
constant `K`.  If the finite-stage HLS denominator comparison holds for this
same `K` at every point of `[β₁, β₂]`, then the concrete interval Lipschitz
estimate for `β ↦ (h β)^(2α+1)` follows.

This packages the HLS constant into the interval version of the finite-volume
pseudo-mass calculus.  It remains conditional on the pointwise denominator
comparison; the final infinite-volume `latticeMass` upper-bound assembly is a
separate downstream step.

References: Glimm--Jaffe §17.5, Theorem 17.5.1 proof and Lemma 17.5.2,
pp.~311--312. -/
theorem lemma_17_5_2_beta_pseudoMass_pow_succ_lipschitz_of_hls_constant
    {d α : ℕ} (hαd : 2 * α > d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ : 0 ≤ J)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (n : ℕ) (r s : ↑(Λ.volume n)) (hrs : r ≠ s)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hβ_mem : ∀ β' ∈ Set.Icc β₁ β₂, β' ∈ Set.Icc a b)
    {rho : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ}
    (hh_diff : ∀ β' ∈ Set.Icc β₁ β₂, HasDerivAt h (deriv h β') β')
    (hh_nonneg : ∀ β' ∈ Set.Icc β₁ β₂, 0 ≤ h β')
    (hg_eq : ∀ β' ∈ Set.Icc β₁ β₂,
      (fun γ => pseudoMassG α rho (h γ)) =ᶠ[nhds β']
        (fun γ =>
          IsingModel.correlation
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
            (⟨J, 0, γ⟩ : IsingParams ℝ) {r, s}))
    (hh_pos : ∀ β' ∈ Set.Icc β₁ β₂, 0 < h β')
    (hc_pos : ∀ β' ∈ Set.Icc β₁ β₂,
      0 <
        IsingModel.correlation
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s}) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x y : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ((∀ β' ∈ Set.Icc β₁ β₂,
          Lemma_17_5_2_HLSDenominatorComparison Λ J b n r s β' α K h) →
        |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
          ↑(2 * α + 1) * K / rho * (β₂ - β₁)) := by
  obtain ⟨K, hK, hK_conv⟩ := lemma_17_5_2_hls_convolution_constant α d hαd
  refine ⟨K, hK, hK_conv, fun hcomp => ?_⟩
  exact lemma_17_5_2_beta_pseudoMass_pow_succ_lipschitz_of_high_temp_bound
    Λ J hJ a b ha hab hlt n r s hrs hβ₁₂ hβ_mem
    (α := α) (rho := rho) (K := K) hrho
    hh_diff hh_nonneg hg_eq hh_pos hc_pos
    (fun β' hβ' => by
      simpa [Lemma_17_5_2_HLSDenominatorComparison] using hcomp β' hβ')

/-- **GJ §17.5 Lemma 17.5.2 infinite-volume HLS-constant derivative bound
for `(m⁻)^(2α+1)`**: under `2α > d`, choose a positive HLS convolution constant
`K` carrying the uniform convolution inequality.  If the infinite-volume HLS
denominator comparison holds for this `K` at `β`, then the abstract pseudo-mass
chain rule gives a derivative bound for `β ↦ (h β)^(2α+1)`.

This is the `correlationInfinite` analogue of
`lemma_17_5_2_beta_pseudoMass_pow_succ_deriv_bound_of_hls_constant`; it is
conditional on differentiability of the infinite-volume correlation profile and
on the named denominator comparison.

References: Glimm--Jaffe §17.5, Theorem 17.5.1 proof and Lemma 17.5.2,
pp.~311--312. -/
theorem lemma_17_5_2_infinite_pseudoMass_pow_succ_deriv_bound_of_hls_constant
    {d α : ℕ} (hαd : 2 * α > d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ)
    (β : ℝ) {rho : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ} {h' : ℝ}
    (hh : HasDerivAt h h' β)
    (hc : HasDerivAt
      (fun β' =>
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z})
      (deriv (fun β' =>
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}) β) β)
    (hh_nonneg : 0 ≤ h β)
    (hg_eq :
      (fun β' => pseudoMassG α rho (h β')) =ᶠ[nhds β]
        (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}))
    (hh_pos : 0 < h β)
    (hc_pos :
      0 <
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      (Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β α K h →
        ∃ dval : ℝ,
          HasDerivAt (fun β' => (h β') ^ (2 * α + 1)) dval β ∧
          |dval| ≤ ↑(2 * α + 1) * K / rho) := by
  obtain ⟨K, hK, hK_conv⟩ := lemma_17_5_2_hls_convolution_constant α d hαd
  refine ⟨K, hK, hK_conv, fun hcomp => ?_⟩
  exact pseudoMass_pow_succ_deriv_bound α hrho hh hc hh_nonneg hg_eq hh_pos hc_pos
    (by simpa [Lemma_17_5_2_InfiniteHLSDenominatorComparison] using hcomp)

/-- **GJ §17.5 Lemma 17.5.2 infinite-volume HLS-constant interval Lipschitz
bridge**: under `2α > d`, choose a positive HLS convolution constant `K`
carrying the uniform convolution inequality.  If the infinite-volume HLS
denominator comparison holds for this same `K` on `[β₁, β₂]`, then the abstract
MVT pseudo-mass argument gives the interval Lipschitz estimate for
`β ↦ (h β)^(2α+1)`.

This is the infinite-volume handoff immediately preceding the future
`latticeMass` upper-bound assembly.  It does not prove the denominator
comparison or the final `latticeMass ≤ C · m⁻` inequality.

References: Glimm--Jaffe §17.5, Theorem 17.5.1 proof and Lemma 17.5.2,
pp.~311--312. -/
theorem lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_hls_constant
    {d α : ℕ} (hαd : 2 * α > d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ)
    {β₁ β₂ : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    {rho : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ}
    (hh_diff : ∀ β' ∈ Set.Icc β₁ β₂, HasDerivAt h (deriv h β') β')
    (hc_diff : ∀ β' ∈ Set.Icc β₁ β₂,
      HasDerivAt
        (fun β'' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β''⟩ : IsingParams ℝ) {x, z})
        (deriv (fun β'' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β''⟩ : IsingParams ℝ) {x, z}) β') β')
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
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ((∀ β' ∈ Set.Icc β₁ β₂,
          Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β' α K h) →
        |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
          ↑(2 * α + 1) * K / rho * (β₂ - β₁)) := by
  obtain ⟨K, hK, hK_conv⟩ := lemma_17_5_2_hls_convolution_constant α d hαd
  refine ⟨K, hK, hK_conv, fun hcomp => ?_⟩
  exact pseudoMass_pow_succ_lipschitz α hrho hβ₁₂ hh_diff hc_diff hh_nonneg
    hg_eq hh_pos hc_pos
    (fun β' hβ' => by
      simpa [Lemma_17_5_2_InfiniteHLSDenominatorComparison] using hcomp β' hβ')

/-- **GJ §17.5 Lemma 17.5.2 upper bound from an infinite-volume HLS Lipschitz
all-rate bridge**: once the HLS/Lipschitz layer has produced the interval
Lipschitz estimate for `β ↦ (h β)^(2α+1)`, the named bridge
`Lemma_17_5_2_InfiniteHLSLipschitzAllRateBridge` converts it into the
all-admissible-rate estimate, and the order-theoretic upper-bound assembly
closes `Lemma_17_5_2_UpperBound`.

This theorem deliberately does not re-prove the interval Lipschitz estimate;
that is supplied by
`lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_hls_constant`.

References: Glimm--Jaffe §17.5, Theorem 17.5.1 proof and Lemma 17.5.2,
pp.~311--312. -/
theorem lemma_17_5_2_upper_bound_of_infinite_hls_lipschitz_all_rate_bridge
    {d α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ) (β₁ β₂ K : ℝ) (h : ℝ → ℝ)
    (hlip :
      (∀ β' ∈ Set.Icc β₁ β₂,
          Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β' α K h) →
        |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
          ↑(2 * α + 1) * K / r * (β₂ - β₁))
    (hbridge :
      Lemma_17_5_2_InfiniteHLSLipschitzAllRateBridge
        hα hr Λ J x z β₁ β₂ K h) :
    Lemma_17_5_2_UpperBound hα hr Λ J β₂ x z
      (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r)) := by
  exact lemma_17_5_2_upper_bound_of_all_decay_rates_le hα hr Λ J β₂ x z
    (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r)) (hbridge hlip)

/-- **GJ §17.5 Lemma 17.5.2 sandwich from an infinite-volume HLS Lipschitz
all-rate bridge**: once the lower pseudo-mass decay side is available at
`β₂`, the preceding upper-bound bridge gives the full conditional sandwich.

The theorem keeps the last analytic step explicit as
`Lemma_17_5_2_InfiniteHLSLipschitzAllRateBridge`, but removes all remaining
order-theoretic assembly from downstream work.

References: Glimm--Jaffe §17.5, Theorem 17.5.1 proof and Lemma 17.5.2,
pp.~311--312. -/
theorem lemma_17_5_2_sandwich_of_infinite_hls_lipschitz_all_rate_bridge
    {d α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J : ℝ} {x z : Fin d → ℤ} {β₁ β₂ K : ℝ} {h : ℝ → ℝ}
    (hlip :
      (∀ β' ∈ Set.Icc β₁ β₂,
          Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β' α K h) →
        |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
          ↑(2 * α + 1) * K / r * (β₂ - β₁))
    (hbridge :
      Lemma_17_5_2_InfiniteHLSLipschitzAllRateBridge
        hα hr Λ J x z β₁ β₂ K h)
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
    latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
      ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
        ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) := by
  have hupper :
      Lemma_17_5_2_UpperBound hα hr Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r)) :=
    lemma_17_5_2_upper_bound_of_infinite_hls_lipschitz_all_rate_bridge
      hα hr Λ J x z β₁ β₂ K h hlip hbridge
  exact lemma_17_5_2_sandwich_of_decay_and_upper hα hr hdecay hupper

/-- **GJ §17.5 Lemma 17.5.2 upper bound from an existential infinite HLS
Lipschitz package and all-rate bridge**: if the infinite-volume HLS/Lipschitz
layer has produced an existential HLS constant package, and the named
all-rate bridge is available for the returned constant, then the named
`latticeMass` upper-bound predicate follows.

This avoids re-elaborating the heavy differentiability hypotheses of
`lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_hls_constant`; callers
pass that theorem's existential output directly. -/
theorem lemma_17_5_2_upper_bound_of_exists_infinite_hls_lipschitz_bridge
    {d α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ)
    (β₁ β₂ : ℝ) (h : ℝ → ℝ)
    (hpkg :
      ∃ K : ℝ, 0 < K ∧
        (∀ x' y' : Fin d → ℤ,
          ∑' w : Fin d → ℤ,
              (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
              (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
        ((∀ β' ∈ Set.Icc β₁ β₂,
            Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β' α K h) →
          |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
            ↑(2 * α + 1) * K / r * (β₂ - β₁))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      (Lemma_17_5_2_InfiniteHLSLipschitzAllRateBridge
          hα hr Λ J x z β₁ β₂ K h →
        Lemma_17_5_2_UpperBound hα hr Λ J β₂ x z
          (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r))) := by
  obtain ⟨K, hK, hK_conv, hlip⟩ := hpkg
  refine ⟨K, hK, hK_conv, fun hbridge => ?_⟩
  exact lemma_17_5_2_upper_bound_of_infinite_hls_lipschitz_all_rate_bridge
    hα hr Λ J x z β₁ β₂ K h hlip hbridge

/-- **GJ §17.5 Lemma 17.5.2 sandwich from an existential infinite HLS
Lipschitz package and all-rate bridge**: combine the preceding existential
upper-bound package with the lower pseudo-mass decay input. -/
theorem lemma_17_5_2_sandwich_of_exists_infinite_hls_lipschitz_bridge
    {d α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J : ℝ} {x z : Fin d → ℤ}
    {β₁ β₂ : ℝ} {h : ℝ → ℝ}
    (hpkg :
      ∃ K : ℝ, 0 < K ∧
        (∀ x' y' : Fin d → ℤ,
          ∑' w : Fin d → ℤ,
              (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
              (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
        ((∀ β' ∈ Set.Icc β₁ β₂,
            Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β' α K h) →
          |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
            ↑(2 * α + 1) * K / r * (β₂ - β₁)))
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      (Lemma_17_5_2_InfiniteHLSLipschitzAllRateBridge
          hα hr Λ J x z β₁ β₂ K h →
        ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
          ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
        latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
          ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
            ENNReal.ofReal
              (pseudoMassFromParamsAtPair hα hr d Λ
                (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) := by
  obtain ⟨K, hK, hK_conv, hupper⟩ :=
    lemma_17_5_2_upper_bound_of_exists_infinite_hls_lipschitz_bridge
      hα hr Λ J x z β₁ β₂ h hpkg
  refine ⟨K, hK, hK_conv, fun hbridge => ?_⟩
  exact lemma_17_5_2_sandwich_of_decay_and_upper hα hr hdecay (hupper hbridge)

/-- **GJ §17.5 Lemma 17.5.2 HLS-constant upper-bound package**: under the
HLS exponent condition, choose a positive convolution constant `K`. If every
admissible nonnegative exponential-decay rate is bounded by the HLS Lipschitz
coefficient `(2α+1)K/r` times the concrete pseudo-mass, then the named
Lemma 17.5.2 upper-bound predicate follows.

This fixes the exact all-rate target for the remaining analytic/HLS proof:
the future work should prove the premise for the returned HLS constant `K`,
then this theorem closes the `latticeMass` upper side by the order-theoretic
assembly in `Predicates`. -/
theorem lemma_17_5_2_hls_upper_bound_of_all_decay_rates_le
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d)
    {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ((∀ a : NNReal,
          HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) (a : ℝ) →
            (a : ENNReal) ≤
              ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
                ENNReal.ofReal
                  (pseudoMassFromParamsAtPair hα hr d Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) x z)) →
        Lemma_17_5_2_UpperBound hα hr Λ J β x z
          (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r))) := by
  obtain ⟨K, hK, hK_conv⟩ := lemma_17_5_2_hls_convolution_constant α d hαd
  refine ⟨K, hK, hK_conv, fun hdecay_le => ?_⟩
  exact lemma_17_5_2_upper_bound_of_all_decay_rates_le hα hr Λ J β x z
    (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r)) hdecay_le

/-- **GJ §17.5 Lemma 17.5.2 HLS-constant sandwich package**: once the
pseudo-mass rate itself validates exponential decay, the same HLS convolution
constant package reduces the full sandwich to the all-admissible-decay-rate
upper estimate.

This is the direct capstone shape for the remaining HLS proof: provide the
all-rate premise for the returned constant `K`, and this theorem returns
`ofReal m⁻ ≤ latticeMass ≤ ((2α+1)K/r) · ofReal m⁻`. -/
theorem lemma_17_5_2_hls_sandwich_of_decay_and_all_decay_rates_le
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d)
    {r : ℝ} (hr : 0 < r)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J β : ℝ} {x z : Fin d → ℤ}
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ((∀ a : NNReal,
          HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) (a : ℝ) →
            (a : ENNReal) ≤
              ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
                ENNReal.ofReal
                  (pseudoMassFromParamsAtPair hα hr d Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) x z)) →
        ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z)
          ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
        latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≤
          ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
            ENNReal.ofReal
              (pseudoMassFromParamsAtPair hα hr d Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z)) := by
  obtain ⟨K, hK, hK_conv, hupper⟩ :=
    lemma_17_5_2_hls_upper_bound_of_all_decay_rates_le
      hα hαd hr Λ J β x z
  refine ⟨K, hK, hK_conv, fun hdecay_le => ?_⟩
  exact lemma_17_5_2_sandwich_of_decay_and_upper hα hr hdecay
    (hupper hdecay_le)

/-- **GJ §17.5 Lemma 17.5.2 cubic high-temperature HLS-constant conditional
sandwich**: combine the existing cubic high-temperature lower-bound capstone
with the HLS convolution constant package. The remaining HLS input is exactly
the all-admissible-decay-rate estimate for the returned constant `K`.

This is the concrete cubic-exhaustion version of the HLS route toward the full
Lemma 17.5.2 sandwich. It keeps the final analytic/HLS all-rate estimate as an
explicit premise, rather than claiming the book's HLS-uniform upper side is
already proved. -/
theorem lemma_17_5_2_cubic_high_temp_hls_conditional_sandwich
    {α d : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hinputs :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
            {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2 ∧
        pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
          Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              {(0 : Fin d → ℤ), z}) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ((∀ a : NNReal,
          HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) (a : ℝ) →
            (a : ENNReal) ≤
              ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
                ENNReal.ofReal
                  (cubicOriginPseudoMassFromParamsAtPair hα hr β J z)) →
        HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
            (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∧
        ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ≤
          latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
        latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≤
          ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
            ENNReal.ofReal
              (cubicOriginPseudoMassFromParamsAtPair hα hr β J z)) := by
  obtain ⟨K, hK, hK_conv⟩ := lemma_17_5_2_hls_convolution_constant α d hαd
  refine ⟨K, hK, hK_conv, fun hdecay_le => ?_⟩
  have hlower :=
    lemma_17_5_2_cubic_high_temp_lower_capstone hα hr Λ hJ hβ hlt hinputs
  refine ⟨hlower.1, hlower.2.2, ?_⟩
  dsimp [latticeMass]
  apply sSup_le
  rintro b ⟨a, ha, rfl⟩
  exact hdecay_le a ha

/-- **GJ §17.5 Lemma 17.5.2 cubic high-temperature HLS sandwich from a
path-rate scalar comparison**: after choosing the HLS convolution constant,
the Step 115 all-rate path bound discharges the all-admissible-decay-rate
premise of `lemma_17_5_2_cubic_high_temp_hls_conditional_sandwich` whenever
`-log(tanh(βJ))` is bounded by the HLS coefficient times the anchored cubic
pseudo-mass.

This isolates the remaining upper-bound task to a scalar comparison between
the Step 115 path rate and the HLS Lipschitz coefficient. -/
theorem lemma_17_5_2_cubic_high_temp_hls_sandwich_of_path_rate_le_hls
    {α d : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) {r : ℝ} (hr : 0 < r)
    (hd : 0 < d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hinputs :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
            {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2 ∧
        pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
          Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              {(0 : Fin d → ℤ), z}) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      (ENNReal.ofReal (-Real.log (Real.tanh (β * J))) ≤
          ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
            ENNReal.ofReal
              (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) →
        HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
            (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∧
        ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ≤
          latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
        latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≤
          ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
            ENNReal.ofReal
              (cubicOriginPseudoMassFromParamsAtPair hα hr β J z)) := by
  obtain ⟨K, hK, hK_conv, hfinish⟩ :=
    lemma_17_5_2_cubic_high_temp_hls_conditional_sandwich
      hα hαd hr Λ hJ.le hβ hlt hinputs
  refine ⟨K, hK, hK_conv, fun hpath_le => hfinish ?_⟩
  intro a ha
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ.le, le_refl 0, hβ⟩
  have ha_cubic :
      HasExponentialDecay d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) (a : ℝ) :=
    HasExponentialDecay_transfer_exhaustion Λ (Ambient.cubicExhaustion d) hf ha
  exact (HasExponentialDecay_rate_le_neg_log_tanh_betaJ hd hJ hβ ha_cubic).trans hpath_le

/-- **GJ §17.5 Lemma 17.5.2 finite high-temperature HLS-style sandwich with
an enlarged constant**: in the cubic high-temperature active range, enlarge a
discrete HLS convolution constant enough to dominate the Step 115 path rate.
The resulting constant simultaneously carries the HLS convolution inequality
and gives the full `ofReal m⁻ ≤ latticeMass ≤ C · ofReal m⁻` sandwich.

The constant may depend on the current high-temperature parameters and the
anchored pair; this is the finite Step 115/HLS package, not the book's final
uniform HLS constant. -/
theorem lemma_17_5_2_cubic_high_temp_enlarged_hls_sandwich
    {α d : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) {r : ℝ} (hr : 0 < r)
    (hd : 0 < d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {z : Fin d → ℤ}
    (hinputs :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
            {(0 : Fin d → ℤ), z} ∈ Set.Ioo (0 : ℝ) 2 ∧
        pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
          Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              {(0 : Fin d → ℤ), z}) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ∧
      ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) ≤
        latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
          ENNReal.ofReal
            (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) := by
  obtain ⟨K₀, hK₀, hK₀_conv⟩ := lemma_17_5_2_hls_convolution_constant α d hαd
  let N : ℝ := ((2 * α + 1 : ℕ) : ℝ)
  let m : ℝ := cubicOriginPseudoMassFromParamsAtPair hα hr β J z
  let path : ℝ := -Real.log (Real.tanh (β * J))
  let K : ℝ := max K₀ (path * r / (N * m))
  have hN_pos : 0 < N := by
    dsimp [N]
    exact_mod_cast Nat.succ_pos (2 * α)
  have hm_pos : 0 < m := by
    dsimp [m]
    exact cubicOriginPseudoMassFromParamsAtPair_pos_of_cubic_corr_mem hα hr hinputs.1
  have hK_pos : 0 < K := hK₀.trans_le (le_max_left _ _)
  have hK_conv : ∀ x' y' : Fin d → ℤ,
      ∑' w : Fin d → ℤ,
          (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
          (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K := by
    intro x' y'
    exact (hK₀_conv x' y').trans (le_max_left _ _)
  have hpath_real : path ≤ (N * K / r) * m := by
    have hNm_pos : 0 < N * m := mul_pos hN_pos hm_pos
    have hscale_le : path * r / (N * m) ≤ K := le_max_right _ _
    have hmul_le : path * r ≤ K * (N * m) := by
      have h := mul_le_mul_of_nonneg_right hscale_le hNm_pos.le
      rwa [div_mul_cancel₀ (path * r) hNm_pos.ne'] at h
    have hdiv_le : path ≤ K * (N * m) / r := by
      have h := div_le_div_of_nonneg_right hmul_le hr.le
      rwa [mul_div_cancel_right₀ path hr.ne'] at h
    calc
      path ≤ K * (N * m) / r := hdiv_le
      _ = (N * K / r) * m := by ring
  have hpath_enn :
      ENNReal.ofReal path ≤
        ENNReal.ofReal (N * K / r) * ENNReal.ofReal m := by
    have hcoeff_nonneg : 0 ≤ N * K / r :=
      div_nonneg (mul_nonneg hN_pos.le hK_pos.le) hr.le
    have h := ENNReal.ofReal_le_ofReal hpath_real
    rw [ENNReal.ofReal_mul hcoeff_nonneg] at h
    exact h
  have hlower :=
    lemma_17_5_2_cubic_high_temp_lower_capstone hα hr Λ hJ.le hβ hlt hinputs
  refine ⟨K, hK_pos, hK_conv, hlower.1, hlower.2.2, ?_⟩
  dsimp [latticeMass]
  apply sSup_le
  rintro b ⟨a, ha, rfl⟩
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ.le, le_refl 0, hβ⟩
  have ha_cubic :
      HasExponentialDecay d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) (a : ℝ) :=
    HasExponentialDecay_transfer_exhaustion Λ (Ambient.cubicExhaustion d) hf ha
  calc
    (a : ENNReal) ≤ ENNReal.ofReal path :=
      HasExponentialDecay_rate_le_neg_log_tanh_betaJ hd hJ hβ ha_cubic
    _ ≤ ENNReal.ofReal (N * K / r) * ENNReal.ofReal m := hpath_enn
    _ = ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
        ENNReal.ofReal (cubicOriginPseudoMassFromParamsAtPair hα hr β J z) := by
      simp [N, m]

/-- **GJ §17.5 Lemma 17.5.2 finite high-temperature HLS-style sandwich for
an arbitrary cubic pair**: in the cubic high-temperature active range, enlarge
a discrete HLS convolution constant enough to dominate the Step 115 path rate
for the pair pseudo-mass attached to `{x,z}`.  The returned constant carries
the HLS convolution inequality and gives the target-exhaustion sandwich
`ofReal m⁻ ≤ latticeMass ≤ C · ofReal m⁻`, with
`m⁻ := pseudoMassFromParamsAtPair ... Λ ... x z`.

As with `lemma_17_5_2_cubic_high_temp_enlarged_hls_sandwich`, the enlarged
constant may depend on the parameters and the pair; it is a finite
Step 115/HLS package, not the book's final uniform HLS constant. -/
theorem lemma_17_5_2_cubic_pair_high_temp_enlarged_hls_sandwich
    {α d : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) {r : ℝ} (hr : 0 < r)
    (hd : 0 < d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hinputs :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
            ∈ Set.Ioo (0 : ℝ) 2 ∧
        pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
          Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z) ≤
        latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z) := by
  obtain ⟨K₀, hK₀, hK₀_conv⟩ := lemma_17_5_2_hls_convolution_constant α d hαd
  let N : ℝ := ((2 * α + 1 : ℕ) : ℝ)
  let p : IsingParams ℝ := ⟨J, 0, β⟩
  let m₀ : ℝ := pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d) p x z
  let path : ℝ := -Real.log (Real.tanh (β * J))
  let K : ℝ := max K₀ (path * r / (N * m₀))
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ.le, le_refl 0, hβ⟩
  have hm_eq :
      pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z = m₀ := by
    dsimp [m₀, p]
    exact pseudoMassFromParamsAtPair_indep_exhaustion hα hr d Λ
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) hf x z
  have hN_pos : 0 < N := by
    dsimp [N]
    exact_mod_cast Nat.succ_pos (2 * α)
  have hm_pos : 0 < m₀ := by
    dsimp [m₀, p]
    exact pseudoMassFromParamsAtPair_pos_of_corr_mem hα hr d
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) x z hinputs.1
  have hK_pos : 0 < K := hK₀.trans_le (le_max_left _ _)
  have hK_conv : ∀ x' y' : Fin d → ℤ,
      ∑' w : Fin d → ℤ,
          (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
          (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K := by
    intro x' y'
    exact (hK₀_conv x' y').trans (le_max_left _ _)
  have hpath_real : path ≤ (N * K / r) * m₀ := by
    have hNm_pos : 0 < N * m₀ := mul_pos hN_pos hm_pos
    have hscale_le : path * r / (N * m₀) ≤ K := le_max_right _ _
    have hmul_le : path * r ≤ K * (N * m₀) := by
      have h := mul_le_mul_of_nonneg_right hscale_le hNm_pos.le
      rwa [div_mul_cancel₀ (path * r) hNm_pos.ne'] at h
    have hdiv_le : path ≤ K * (N * m₀) / r := by
      have h := div_le_div_of_nonneg_right hmul_le hr.le
      rwa [mul_div_cancel_right₀ path hr.ne'] at h
    calc
      path ≤ K * (N * m₀) / r := hdiv_le
      _ = (N * K / r) * m₀ := by ring
  have hpath_enn :
      ENNReal.ofReal path ≤
        ENNReal.ofReal (N * K / r) * ENNReal.ofReal m₀ := by
    have hcoeff_nonneg : 0 ≤ N * K / r :=
      div_nonneg (mul_nonneg hN_pos.le hK_pos.le) hr.le
    have h := ENNReal.ofReal_le_ofReal hpath_real
    rw [ENNReal.ofReal_mul hcoeff_nonneg] at h
    exact h
  have hlower :=
    lemma_17_5_2_cubic_pair_high_temp_lower_capstone hα hr Λ hJ.le hβ hlt hinputs
  refine ⟨K, hK_pos, hK_conv, ?_, ?_, ?_⟩
  · simpa [hm_eq, m₀, p] using hlower.1
  · simpa [hm_eq, m₀, p] using hlower.2
  · dsimp [latticeMass]
    apply sSup_le
    rintro b ⟨a, ha, rfl⟩
    have ha_cubic :
        HasExponentialDecay d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) (a : ℝ) :=
      HasExponentialDecay_transfer_exhaustion Λ (Ambient.cubicExhaustion d) hf ha
    calc
      (a : ENNReal) ≤ ENNReal.ofReal path :=
        HasExponentialDecay_rate_le_neg_log_tanh_betaJ hd hJ hβ ha_cubic
      _ ≤ ENNReal.ofReal (N * K / r) * ENNReal.ofReal m₀ := hpath_enn
      _ = ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z) := by
        simp [N, m₀, p, hm_eq]

end Ambient
end IsingModel
