import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProviderInfiniteHLS
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProviderFiniteProfile
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.FiniteRegionPseudoMassDistContinuity
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferBasic
import IsingModel.ClusterExpansion.TwoPointConvergenceWindow

/-!
# GJ §17.5 Theorem 17.5.1 — conditional discharge of the infinite-volume HLS denominator comparison

This module discharges the predicate `Lemma_17_5_2_InfiniteHLSDenominatorComparison`
(`HLSConstants.lean`) on the **convergence window** of GJ §17.5, *conditionally* on a
**per-pair correlation lower bound** `hprofile : pseudoMassG α ρ q ≤ correlationInfinite {x,z}`
(with `q = −log(βJ·2d)`).

The mathematical content (GJ p. 312) is reorganized to avoid matching the polynomial decay of
the derivative numerator to the exponential decay of the correlation `c`:

* the numerator `|c'|` is bounded *above* by a pair- and stage-independent **constant** `B`
  (the existing high-temperature susceptibility bound
  `lemma_17_5_2_finite_deriv_abs_le_high_temp_on_Icc_all_stages`, passed to the limiting
  derivative profile through the axiom-free window provider
  `ConvergenceRegion.derivativeLimit_on_window`);
* the hypothesis `hprofile` bounds the denominator ratio `c / m^(2α)` *below* by the
  pair-independent positive **constant** `L := pseudoMassG α ρ q / q^(2α)`
  (`profile_lower_ratio_lower`);
* then `K := max 1 (B / L)` gives `|c'| ≤ B ≤ K·L ≤ K·c/m^(2α)`.

**Honesty note.** The `∀`-displacement form of `hprofile` is *provably false* (no-go #4270,
`not_forall_cubicTanhProfileBound_…`): a fixed-radius profile cannot lower-bound an
exponentially-decaying correlation at every displacement.  Hence `hprofile` is a genuine
*per-pair* hypothesis (e.g. true for nearby pairs), and the result is a documented
**conditional** (Partial), matching the lower side of the existing §17.5 sandwich.  The
unconditional headline is the faithful distance-parametrized route
(`globalPseudoMassDist_fullSandwich`, #4317).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and Lemma 17.5.2,
  pp.~311--312.
-/

namespace IsingModel
namespace Ambient

open Set Real

/-- **GJ §17.5 ratio lower bound from the per-pair profile lower bound.**

For a distinct pair `(x, z)` at high temperature (`0 < βJ·2d < 1`) with active correlation
`c ∈ Ioo 0 2`, the per-pair correlation lower bound `hprofile : pseudoMassG α ρ q ≤ c`
(`q := −log(βJ·2d)`) yields the *pair-independent* positive lower bound on the HLS denominator
ratio
`pseudoMassG α ρ q / q^(2α) ≤ c / (pseudoMassFromParamsAtPair … x z)^(2α)`.

This is the denominator side of the GJ p. 312 estimate: the fixed positive constant
`L := pseudoMassG α ρ q / q^(2α)` lower-bounds `c / m^(2α)` because the per-pair pseudo-mass
`m` is dominated by the high-temperature rate `q`
(`pseudoMassFromParamsAtPair_le_high_temp_rate_of_pseudoMassG_le_corr`), so `m^(2α) ≤ q^(2α)`,
while `c ≥ pseudoMassG α ρ q ≥ 0`.

References: Glimm--Jaffe §17.5, Theorem 17.5.1 proof, pp.~311--312. -/
theorem lemma_17_5_2_profile_lower_ratio_lower_cubic
    {d α : ℕ} (hα : 1 ≤ α) (hd : 1 ≤ d) {ρ : ℝ} (hρ : 0 < ρ)
    {J β : ℝ} (hJ_pos : 0 < J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
      ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile : pseudoMassG α ρ (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    pseudoMassG α ρ (-Real.log (β * J * ↑(2 * d))) /
        (-Real.log (β * J * ↑(2 * d))) ^ (2 * α)
      ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} /
        (pseudoMassFromParamsAtPair hα hρ d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z) ^ (2 * α) := by
  set q : ℝ := -Real.log (β * J * ↑(2 * d)) with hq_def
  set c : ℝ := Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} with hc_def
  set m : ℝ := pseudoMassFromParamsAtPair hα hρ d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) x z with hm_def
  -- Positivity facts.
  have hd_pos : 0 < ((2 * d : ℕ) : ℝ) := by
    have : 0 < (2 * d : ℕ) := by omega
    exact_mod_cast this
  have hβJd_pos : 0 < β * J * ↑(2 * d) := by positivity
  have hq_pos : 0 < q := by
    rw [hq_def]
    exact neg_pos.mpr (Real.log_neg hβJd_pos hlt)
  have hm_pos : 0 < m := by
    rw [hm_def]
    exact pseudoMassFromParamsAtPair_pos_of_corr_mem hα hρ d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) x z hcorr
  have hgq_pos : 0 < pseudoMassG α ρ q :=
    pseudoMassG_pos α hq_pos.le hρ
  -- `m ≤ q`.
  have hmq : m ≤ q := by
    rw [hm_def, hq_def]
    exact pseudoMassFromParamsAtPair_le_high_temp_rate_of_pseudoMassG_le_corr
      hα hρ (Ambient.cubicExhaustion d) hJ_pos.le hβ hlt hcorr hprofile
  -- power monotonicity.
  have hm_pow_pos : 0 < m ^ (2 * α) := pow_pos hm_pos _
  have hpow_le : m ^ (2 * α) ≤ q ^ (2 * α) :=
    pow_le_pow_left₀ hm_pos.le hmq _
  -- c ≥ pseudoMassG α ρ q ≥ 0.
  have hc_ge : pseudoMassG α ρ q ≤ c := by rw [hc_def]; exact hprofile
  -- assemble: g(q)/q^{2α} ≤ g(q)/m^{2α} ≤ c/m^{2α}.
  calc pseudoMassG α ρ q / q ^ (2 * α)
      ≤ pseudoMassG α ρ q / m ^ (2 * α) :=
        div_le_div_of_nonneg_left hgq_pos.le hm_pow_pos hpow_le
    _ ≤ c / m ^ (2 * α) :=
        div_le_div_of_nonneg_right hc_ge hm_pow_pos.le

/-- **GJ §17.5 Theorem 17.5.1 — conditional infinite-volume HLS denominator comparison on the
convergence window.**

For a distinct pair `(x, z)` and `β` in the (axiom-free) convergence window
`ConvergenceRegion.window d J`, the per-pair correlation lower bound
`hprofile : pseudoMassG α ρ q ≤ correlationInfinite {x,z}` (with `q = −log(βJ·2d)`) discharges the
named predicate `Lemma_17_5_2_InfiniteHLSDenominatorComparison` for some `K > 0`:
`|c'(β)| ≤ K · c(β) / (pseudoMassFromParamsAtPair … x z)^(2α)`.

Proof (GJ p. 312, reorganized to avoid the exponential/polynomial mismatch):
* the numerator `|c'|` is bounded above by the pair- and stage-independent constant
  `B := J·(βJ·2d/(1−βJ·2d))² + J·4d` — the high-temperature susceptibility bound
  `lemma_17_5_2_finite_deriv_abs_le_high_temp_on_Icc_all_stages`, passed to the limiting
  derivative profile through the axiom-free window provider
  `ConvergenceRegion.derivativeLimit_on_window` (`le_of_tendsto`);
* `hprofile` lower-bounds the denominator ratio `c / m^(2α)` by the positive constant
  `L := pseudoMassG α ρ q / q^(2α)` (`lemma_17_5_2_profile_lower_ratio_lower_cubic`);
* `K := max 1 (B / L)` gives `|c'| ≤ B ≤ K·L ≤ K·c/m^(2α)`.

**Conditional / Partial.** The `∀`-displacement form of `hprofile` is provably false (no-go
#4270); this is a genuine per-pair hypothesis, so the theorem is a documented conditional matching
the lower side of the existing §17.5 sandwich.  The unconditional headline is the faithful
distance-parametrized route (`globalPseudoMassDist_fullSandwich`, #4317).

References: Glimm--Jaffe §17.5, Theorem 17.5.1 proof and Lemma 17.5.2, pp.~311--312. -/
theorem lemma_17_5_2_infinite_hls_denominator_comparison_cubic_of_profile_lower
    {d α : ℕ} (hα : 1 ≤ α) (hd : 1 ≤ d) {ρ : ℝ} (hρ : 0 < ρ)
    {J β : ℝ} (hJ_pos : 0 < J)
    (hβ_window : β ∈ ConvergenceRegion.window d J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hprofile : pseudoMassG α ρ (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    ∃ K : ℝ, 0 < K ∧
      Lemma_17_5_2_InfiniteHLSDenominatorComparison
        (Ambient.cubicExhaustion d) J x z β α K
        (lemma_17_5_2_concretePseudoMassBetaProfile
          hα hρ (Ambient.cubicExhaustion d) J x z) := by
  classical
  -- high-temperature window facts.
  have hβ_highTemp : β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) :=
    ConvergenceRegion.window_subset_highTemp d J hJ_pos hd hβ_window
  have hβ_pos : 0 < β := hβ_highTemp.1
  have hJd_pos : 0 < J * ↑(2 * d) := by
    have hd_pos : 0 < ((2 * d : ℕ) : ℝ) := by
      have : 0 < (2 * d : ℕ) := by omega
      exact_mod_cast this
    positivity
  have hlt : β * J * ↑(2 * d) < 1 := by
    have hmul : β * (J * ↑(2 * d)) < 1 := (lt_div_iff₀ hJd_pos).mp hβ_highTemp.2
    rw [mul_assoc]; exact hmul
  have hβJ_pos : 0 < β * J := mul_pos hβ_pos hJ_pos
  -- active range.
  have hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
      ∈ Set.Ioo (0 : ℝ) 2 :=
    correlationInfinite_pair_active_of_betaJ_pos_exhaustion
      (Ambient.cubicExhaustion d) hβ_pos hβJ_pos x z hxz
  -- denominator ratio lower bound.
  set q : ℝ := -Real.log (β * J * ↑(2 * d)) with hq_def
  have hβJd_pos : 0 < β * J * ↑(2 * d) := by positivity
  have hq_pos : 0 < q := by rw [hq_def]; exact neg_pos.mpr (Real.log_neg hβJd_pos hlt)
  set L : ℝ := pseudoMassG α ρ q / q ^ (2 * α) with hL_def
  have hL_pos : 0 < L := by
    rw [hL_def]; exact div_pos (pseudoMassG_pos α hq_pos.le hρ) (pow_pos hq_pos _)
  have hratio : L ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} /
      (pseudoMassFromParamsAtPair hα hρ d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z) ^ (2 * α) := by
    rw [hL_def, hq_def]
    exact lemma_17_5_2_profile_lower_ratio_lower_cubic hα hd hρ hJ_pos hβ_pos hlt hcorr hprofile
  -- numerator constant.
  set B : ℝ := J * (β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) ^ 2 + J * (4 * ↑d) with hB_def
  have hfinite : ∀ n,
      |deriv (fun β' =>
        Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β| ≤ B := by
    intro n
    have h := lemma_17_5_2_finite_deriv_abs_le_high_temp_on_Icc_all_stages
      (Ambient.cubicExhaustion d) J hJ_pos.le hβ_pos (le_refl β) hlt
      (fun β' hβ' => hβ') hxz n β ⟨le_refl β, le_refl β⟩
    rw [hB_def]; exact h
  -- the constant K.
  set K : ℝ := max 1 (B / L) with hK_def
  have hK_pos : 0 < K := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hK_ge : B / L ≤ K := le_max_right _ _
  -- the derivative-limit provider on the window (axiom-free).
  have hprovider : Lemma_17_5_2_DerivativeLimitProviderOn
      (ConvergenceRegion.window d J) (Ambient.cubicExhaustion d) J x z :=
    ConvergenceRegion.derivativeLimit_on_window d J (Ambient.cubicExhaustion d) hJ_pos hxz
  refine ⟨K, hK_pos, ?_⟩
  refine lemma_17_5_2_infinite_hls_comparison_of_deriv_bound_provider
    hd (Ambient.cubicExhaustion d) J hJ_pos x z hxz β K isOpen_Ioo
    (ConvergenceRegion.window_subset_highTemp d J hJ_pos hd) hβ_window
    (lemma_17_5_2_concretePseudoMassBetaProfile hα hρ (Ambient.cubicExhaustion d) J x z)
    hprovider ?_
  intro g' hg_tlu
  -- |g' β| ≤ B from the locally-uniform limit + the finite stage bound.
  have hpoint : Filter.Tendsto
      (fun n => deriv (fun β' =>
        Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
      Filter.atTop (nhds (g' β)) :=
    hg_tlu.tendsto_at hβ_window
  have hgB : |g' β| ≤ B :=
    le_of_tendsto ((continuous_abs.tendsto (g' β)).comp hpoint)
      (Filter.Eventually.of_forall hfinite)
  -- B ≤ K·c/(h β)^(2α).
  have hm : (lemma_17_5_2_concretePseudoMassBetaProfile hα hρ
      (Ambient.cubicExhaustion d) J x z) β =
      pseudoMassFromParamsAtPair hα hρ d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z := rfl
  have hchain : B ≤ K *
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} /
      (lemma_17_5_2_concretePseudoMassBetaProfile hα hρ
        (Ambient.cubicExhaustion d) J x z) β ^ (2 * α) := by
    rw [hm, mul_div_assoc]
    calc B = B / L * L := by rw [div_mul_cancel₀ B hL_pos.ne']
      _ ≤ K * L := mul_le_mul_of_nonneg_right hK_ge hL_pos.le
      _ ≤ K * (Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} /
          (pseudoMassFromParamsAtPair hα hρ d (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) x z) ^ (2 * α)) :=
        mul_le_mul_of_nonneg_left hratio hK_pos.le
  exact le_trans hgB hchain

end Ambient
end IsingModel
