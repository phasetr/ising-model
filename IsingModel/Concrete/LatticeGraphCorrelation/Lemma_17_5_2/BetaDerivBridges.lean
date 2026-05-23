import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSConstants

/-!
# GJ §17.5 Lemma 17.5.2 capstone — β-derivative and pseudo-mass power bounds

This module is part of the split
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2` development. It
collects the finite-stage β-derivative absolute bound under the high-temperature
window, the HLS derivative-hypothesis bridges, and the pseudo-mass power
derivative bounds packaged for both the explicit constant `K` and the HLS
constant chosen from `lemma_17_5_2_hls_convolution_constant`.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and
  Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

/-- **GJ §17.5 Lemma 17.5.2 β-derivative absolute bound, finite-stage
high-temperature form**: for `β ∈ [a,b]` with `0 < a ≤ b` and `bJ·2d < 1`,
the finite-stage two-point β-derivative exists and is bounded in absolute value
by the uniform Lebowitz/susceptibility constant
`J * M^2 + J * 4d`, where `M = bJ·2d / (1 - bJ·2d)`.

This is the concrete derivative input that must be compared with the HLS
pseudo-mass denominator `K * c β / (m⁻ β)^(2α)` before applying
`pseudoMass_power_deriv_le` / `pseudoMass_pow_succ_lipschitz`.

References: Glimm--Jaffe §17.5, Theorem 17.5.1 proof and Lemma 17.5.2,
pp.~311--312. -/
theorem lemma_17_5_2_beta_deriv_abs_le_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ : 0 ≤ J)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (n : ℕ) (r s : ↑(Λ.volume n)) (hrs : r ≠ s)
    (β : ℝ) (hβ : β ∈ Set.Icc a b) :
    let G := inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)
    let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
    ∃ dval : ℝ,
      HasDerivAt
        (fun β' => IsingModel.correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s})
        dval β ∧
      |dval| ≤ J * M ^ 2 + J * (4 * ↑d) :=
  inducedLatticeGraph_beta_deriv_abs_le_high_temp Λ J hJ a b ha hab hlt
    n r s hrs β hβ

/-- **GJ §17.5 Lemma 17.5.2 HLS derivative-hypothesis bridge**:
an absolute derivative bound implies the exact HLS denominator hypothesis used by
`pseudoMass_power_deriv_le`, once the concrete bound has been compared with
`K * c β / (h β)^(2α)`.

This isolates the final scalar comparison from the pseudo-mass calculus API.

References: Glimm--Jaffe §17.5, Theorem 17.5.1 proof and Lemma 17.5.2,
pp.~311--312. -/
theorem lemma_17_5_2_hls_derivative_hypothesis_of_abs_bound
    {α : ℕ} {K B : ℝ} {h c : ℝ → ℝ} {c' β : ℝ}
    (habs : |c'| ≤ B)
    (hcomp : B ≤ K * c β / (h β) ^ (2 * α)) :
    |c'| ≤ K * c β / (h β) ^ (2 * α) :=
  habs.trans hcomp

/-- **GJ §17.5 Lemma 17.5.2 finite-stage HLS derivative hypothesis**:
the high-temperature finite-volume β-derivative estimate supplies the exact
HLS denominator hypothesis needed by `pseudoMass_power_deriv_le`, provided the
uniform Lebowitz/susceptibility constant has been compared with
`K * c(β) / (h β)^(2α)`.

This is the finite-stage packaging of the comparison step following the HLS
convolution bound in the proof of the pseudo-mass Lipschitz estimate.

References: Glimm--Jaffe §17.5, Theorem 17.5.1 proof and Lemma 17.5.2,
pp.~311--312. -/
theorem lemma_17_5_2_beta_hls_derivative_hypothesis_of_high_temp_bound
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ : 0 ≤ J)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (n : ℕ) (r s : ↑(Λ.volume n)) (hrs : r ≠ s)
    (β : ℝ) (hβ : β ∈ Set.Icc a b)
    {α : ℕ} {K : ℝ} {h : ℝ → ℝ}
    (hcomp :
      let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
      J * M ^ 2 + J * (4 * ↑d) ≤
        K *
          IsingModel.correlation
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
            (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} /
          (h β) ^ (2 * α)) :
    let G := inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)
    ∃ dval : ℝ,
      HasDerivAt
        (fun β' => IsingModel.correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s})
        dval β ∧
      |dval| ≤
        K * IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} /
          (h β) ^ (2 * α) := by
  obtain ⟨dval, hdval, habs⟩ :=
    lemma_17_5_2_beta_deriv_abs_le_high_temp Λ J hJ a b ha hab hlt
      n r s hrs β hβ
  exact ⟨dval, hdval, habs.trans (by simpa using hcomp)⟩

/-- **GJ §17.5 Lemma 17.5.2 finite-stage pseudo-mass power derivative
bound**: once the finite-stage high-temperature derivative bound has been
compared with the HLS denominator, the abstract pseudo-mass calculus gives
`(h β)^(2α) * |h'| ≤ K / rho`.

This is the concrete Lemma 17.5.2 handoff from the finite-volume
Lebowitz/HLS derivative estimate to `pseudoMass_power_deriv_le`.

References: Glimm--Jaffe §17.5, Theorem 17.5.1 proof and Lemma 17.5.2,
pp.~311--312. -/
theorem lemma_17_5_2_beta_pseudoMass_power_deriv_le_of_high_temp_bound
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ : 0 ≤ J)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (n : ℕ) (r s : ↑(Λ.volume n)) (hrs : r ≠ s)
    (β : ℝ) (hβ : β ∈ Set.Icc a b)
    {α : ℕ} {rho K : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ} {h' : ℝ}
    (hh : HasDerivAt h h' β)
    (hh_nonneg : 0 ≤ h β)
    (hg_eq : ∀ β',
      pseudoMassG α rho (h β') =
        IsingModel.correlation
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s})
    (hh_pos : 0 < h β)
    (hc_pos :
      0 <
        IsingModel.correlation
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (⟨J, 0, β⟩ : IsingParams ℝ) {r, s})
    (hcomp :
      let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
      J * M ^ 2 + J * (4 * ↑d) ≤
        K *
          IsingModel.correlation
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
            (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} /
          (h β) ^ (2 * α)) :
    (h β) ^ (2 * α) * |h'| ≤ K / rho := by
  obtain ⟨c', hc', hc_der⟩ :=
    lemma_17_5_2_beta_hls_derivative_hypothesis_of_high_temp_bound
      Λ J hJ a b ha hab hlt n r s hrs β hβ (α := α) (K := K) (h := h) hcomp
  exact pseudoMass_power_deriv_le α hrho hh hc' hh_nonneg hg_eq hh_pos hc_pos hc_der

/-- **GJ §17.5 Lemma 17.5.2 HLS-constant pseudo-mass power derivative
bridge**: under the HLS exponent condition `2α > d`, choose a positive HLS
convolution constant `K`.  If the finite-stage denominator comparison holds
for this `K` at `β`, then the concrete pseudo-mass power derivative estimate
`(h β)^(2α) * |h'| ≤ K / rho` follows.

This packages the positive constant from
`lemma_17_5_2_hls_convolution_constant` into the pointwise
`pseudoMass_power_deriv_le` handoff.

References: Glimm--Jaffe §17.5, Theorem 17.5.1 proof and Lemma 17.5.2,
pp.~311--312. -/
theorem lemma_17_5_2_beta_pseudoMass_power_deriv_le_of_hls_constant
    {d α : ℕ} (hαd : 2 * α > d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ : 0 ≤ J)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (n : ℕ) (r s : ↑(Λ.volume n)) (hrs : r ≠ s)
    (β : ℝ) (hβ : β ∈ Set.Icc a b)
    {rho : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ} {h' : ℝ}
    (hh : HasDerivAt h h' β)
    (hh_nonneg : 0 ≤ h β)
    (hg_eq : ∀ β',
      pseudoMassG α rho (h β') =
        IsingModel.correlation
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s})
    (hh_pos : 0 < h β)
    (hc_pos :
      0 <
        IsingModel.correlation
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (⟨J, 0, β⟩ : IsingParams ℝ) {r, s}) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x y : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      (Lemma_17_5_2_HLSDenominatorComparison Λ J b n r s β α K h →
        (h β) ^ (2 * α) * |h'| ≤ K / rho) := by
  obtain ⟨K, hK, hK_conv⟩ := lemma_17_5_2_hls_convolution_constant α d hαd
  refine ⟨K, hK, hK_conv, fun hcomp => ?_⟩
  exact lemma_17_5_2_beta_pseudoMass_power_deriv_le_of_high_temp_bound
    Λ J hJ a b ha hab hlt n r s hrs β hβ (α := α) (rho := rho) (K := K) hrho
    hh hh_nonneg hg_eq hh_pos hc_pos
    (by simpa [Lemma_17_5_2_HLSDenominatorComparison] using hcomp)

/-- **GJ §17.5 Lemma 17.5.2 finite-stage derivative bound for
`(m⁻)^(2α+1)`**: after the HLS denominator comparison, the concrete finite-stage
correlation derivative feeds the abstract pseudo-mass chain-rule theorem and
returns the derivative estimate for `β ↦ (h β)^(2α+1)`.

This is the finite-volume concrete form of the derivative bound underlying the
Lipschitz estimate in `pseudoMass_pow_succ_lipschitz`.

References: Glimm--Jaffe §17.5, Theorem 17.5.1 proof and Lemma 17.5.2,
pp.~311--312. -/
theorem lemma_17_5_2_beta_pseudoMass_pow_succ_deriv_bound_of_high_temp_bound
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ : 0 ≤ J)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (n : ℕ) (r s : ↑(Λ.volume n)) (hrs : r ≠ s)
    (β : ℝ) (hβ : β ∈ Set.Icc a b)
    {α : ℕ} {rho K : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ} {h' : ℝ}
    (hh : HasDerivAt h h' β)
    (hh_nonneg : 0 ≤ h β)
    (hg_eq : ∀ β',
      pseudoMassG α rho (h β') =
        IsingModel.correlation
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s})
    (hh_pos : 0 < h β)
    (hc_pos :
      0 <
        IsingModel.correlation
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (⟨J, 0, β⟩ : IsingParams ℝ) {r, s})
    (hcomp :
      let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
      J * M ^ 2 + J * (4 * ↑d) ≤
        K *
          IsingModel.correlation
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
            (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} /
          (h β) ^ (2 * α)) :
    ∃ dval : ℝ,
      HasDerivAt (fun β' => (h β') ^ (2 * α + 1)) dval β ∧
      |dval| ≤ ↑(2 * α + 1) * K / rho := by
  obtain ⟨c', hc', hc_der⟩ :=
    lemma_17_5_2_beta_hls_derivative_hypothesis_of_high_temp_bound
      Λ J hJ a b ha hab hlt n r s hrs β hβ (α := α) (K := K) (h := h) hcomp
  exact pseudoMass_pow_succ_deriv_bound α hrho hh hc' hh_nonneg hg_eq hh_pos hc_pos hc_der

/-- **GJ §17.5 Lemma 17.5.2 HLS-constant derivative bound for
`(m⁻)^(2α+1)`**: under `2α > d`, choose a positive HLS convolution constant
`K`.  If the finite-stage denominator comparison holds for this `K`, then
`β ↦ (h β)^(2α+1)` has a derivative at `β` bounded by
`(2α+1) * K / rho`.

This is the pointwise chain-rule companion to
`lemma_17_5_2_beta_pseudoMass_power_deriv_le_of_hls_constant`.

References: Glimm--Jaffe §17.5, Theorem 17.5.1 proof and Lemma 17.5.2,
pp.~311--312. -/
theorem lemma_17_5_2_beta_pseudoMass_pow_succ_deriv_bound_of_hls_constant
    {d α : ℕ} (hαd : 2 * α > d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ : 0 ≤ J)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (n : ℕ) (r s : ↑(Λ.volume n)) (hrs : r ≠ s)
    (β : ℝ) (hβ : β ∈ Set.Icc a b)
    {rho : ℝ} (hrho : 0 < rho)
    {h : ℝ → ℝ} {h' : ℝ}
    (hh : HasDerivAt h h' β)
    (hh_nonneg : 0 ≤ h β)
    (hg_eq : ∀ β',
      pseudoMassG α rho (h β') =
        IsingModel.correlation
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s})
    (hh_pos : 0 < h β)
    (hc_pos :
      0 <
        IsingModel.correlation
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (⟨J, 0, β⟩ : IsingParams ℝ) {r, s}) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x y : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      (Lemma_17_5_2_HLSDenominatorComparison Λ J b n r s β α K h →
        ∃ dval : ℝ,
          HasDerivAt (fun β' => (h β') ^ (2 * α + 1)) dval β ∧
          |dval| ≤ ↑(2 * α + 1) * K / rho) := by
  obtain ⟨K, hK, hK_conv⟩ := lemma_17_5_2_hls_convolution_constant α d hαd
  refine ⟨K, hK, hK_conv, fun hcomp => ?_⟩
  exact lemma_17_5_2_beta_pseudoMass_pow_succ_deriv_bound_of_high_temp_bound
    Λ J hJ a b ha hab hlt n r s hrs β hβ (α := α) (rho := rho) (K := K) hrho
    hh hh_nonneg hg_eq hh_pos hc_pos
    (by simpa [Lemma_17_5_2_HLSDenominatorComparison] using hcomp)

end Ambient
end IsingModel
