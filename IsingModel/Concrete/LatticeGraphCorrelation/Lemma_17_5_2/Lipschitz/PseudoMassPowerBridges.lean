import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.BetaDerivBridges
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CubicHighTemp

/-!
# GJ §17.5 Lemma 17.5.2 capstone — pseudo-mass power Lipschitz bridges

This module is part of the split
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.Lipschitz` development.
It collects the finite-stage and infinite-volume HLS-constant pseudo-mass power
Lipschitz and derivative bridges for `β ↦ (h β)^(2α+1)`, each carrying the
convolution inequality from `lemma_17_5_2_hls_convolution_constant`.

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

end Ambient
end IsingModel
