import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProviderInfiniteHLS
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProviderFiniteProfile
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsRegularity
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

/-- **GJ §17.5 Theorem 17.5.1 — conditional interval Lipschitz of `(m⁻)^{2α+1}` on the convergence
window.**

For a distinct pair `(x, z)` and a closed interval `Icc β₁ β₂ ⊆ ConvergenceRegion.window d J`, the
per-pair correlation lower bound `hprofile` (on the whole interval) yields the GJ §17.5 Theorem
17.5.1 intermediate Lipschitz estimate with a *single* constant:
`∃ K>0, |m⁻(β₂)^{2α+1} − m⁻(β₁)^{2α+1}| ≤ (2α+1)·K/ρ·(β₂−β₁)`,
where `m⁻(β) = pseudoMassFromParamsAtPair … x z` at `β`.

This feeds the fixed-`K` interval `hcomp` into the existing consumer
`pseudoMassFromParamsAtPair_beta_pow_succ_lipschitz_on_Icc_of_corr_differentiableAt`.  The single
`K` is obtained by combining:
* the pair- and stage-uniform numerator bound `B := J·(β₂J·2d/(1−β₂J·2d))²+J·4d` (the susceptibility
  bound, passed to the limiting derivative through the axiom-free window provider), valid for every
  `β ∈ Icc`;
* the *interval-uniform* denominator ratio lower bound `L_min := pseudoMassG α ρ q₁ / q₁^{2α}`
  (`q₁ := −log(β₁J·2d)`), obtained from the per-`β` ratio lower bound
  `lemma_17_5_2_profile_lower_ratio_lower_cubic` and the monotonicity of `q` and `pseudoMassG` (no
  compactness argument needed): `q(β) ≤ q₁` for `β ≥ β₁`, and `pseudoMassG` is `AntitoneOn (Ici 0)`,
  so `L_min ≤ L(β) ≤ c(β)/m(β)^{2α}`.
Then `K := max 1 (B/L_min)` gives `|deriv c β| ≤ B ≤ K·L_min ≤ K·c(β)/m(β)^{2α}` for all `β ∈ Icc`.

**Conditional / Partial.** `hprofile` is a genuine per-pair hypothesis (its `∀`-displacement form is
provably false, no-go #4270); the unconditional headline is `globalPseudoMassDist_fullSandwich`
(#4317).  Downstream, the *system* pseudo-mass `globalPseudoMassDist` (infinite lower envelope)
continuity is **not** automatic — large-separation pairs make the per-pair Lipschitz constant
`(2α+1)·K/ρ` blow up — so this is the per-pair endpoint of the conditional Lipschitz chain.

References: Glimm--Jaffe §17.5, Theorem 17.5.1 proof and Lemma 17.5.2, pp.~311--312. -/
theorem lemma_17_5_2_pseudoMass_pow_succ_lipschitz_on_window_of_profile_lower
    {d α : ℕ} (hα : 1 ≤ α) (hd : 1 ≤ d) {ρ : ℝ} (hρ : 0 < ρ)
    {J β₁ β₂ : ℝ} (hJ_pos : 0 < J) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ ConvergenceRegion.window d J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hprofile : ∀ β ∈ Set.Icc β₁ β₂,
      pseudoMassG α ρ (-Real.log (β * J * ↑(2 * d))) ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    ∃ K : ℝ, 0 < K ∧
      |(pseudoMassFromParamsAtPair hα hρ d (Ambient.cubicExhaustion d)
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) ^ (2 * α + 1) -
          (pseudoMassFromParamsAtPair hα hρ d (Ambient.cubicExhaustion d)
            (⟨J, 0, β₁⟩ : IsingParams ℝ) x z) ^ (2 * α + 1)| ≤
        ↑(2 * α + 1) * K / ρ * (β₂ - β₁) := by
  classical
  -- abbreviations
  set c : ℝ → ℝ := fun β =>
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} with hc_def
  set m : ℝ → ℝ := fun β =>
    pseudoMassFromParamsAtPair hα hρ d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) x z with hm_def
  -- per-β high-temperature facts on the interval.
  have hβ_window : ∀ β ∈ Set.Icc β₁ β₂, β ∈ ConvergenceRegion.window d J :=
    fun β hβ => hIcc hβ
  have hβ_highTemp : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) :=
    fun β hβ => ConvergenceRegion.window_subset_highTemp d J hJ_pos hd (hβ_window β hβ)
  have hd_pos : 0 < ((2 * d : ℕ) : ℝ) := by
    have : 0 < (2 * d : ℕ) := by omega
    exact_mod_cast this
  have hJd_pos : 0 < J * ↑(2 * d) := by positivity
  have hβ₁_mem : β₁ ∈ Set.Icc β₁ β₂ := ⟨le_refl β₁, hβ₁₂⟩
  have hβ₂_mem : β₂ ∈ Set.Icc β₁ β₂ := ⟨hβ₁₂, le_refl β₂⟩
  have hβ₁_pos : 0 < β₁ := (hβ_highTemp β₁ hβ₁_mem).1
  have hlt : ∀ β ∈ Set.Icc β₁ β₂, β * J * ↑(2 * d) < 1 := by
    intro β hβ
    have hmul : β * (J * ↑(2 * d)) < 1 := (lt_div_iff₀ hJd_pos).mp (hβ_highTemp β hβ).2
    rw [mul_assoc]; exact hmul
  have hlt₂ : β₂ * J * ↑(2 * d) < 1 := hlt β₂ hβ₂_mem
  -- active range on the interval.
  have hcorr : ∀ β ∈ Set.Icc β₁ β₂, c β ∈ Set.Ioo (0 : ℝ) 2 := by
    intro β hβ
    have hβ_pos : 0 < β := (hβ_highTemp β hβ).1
    have hβJ_pos : 0 < β * J := mul_pos hβ_pos hJ_pos
    exact correlationInfinite_pair_active_of_betaJ_pos_exhaustion
      (Ambient.cubicExhaustion d) hβ_pos hβJ_pos x z hxz
  -- the axiom-free window derivative-limit provider.
  obtain ⟨g', hderiv_lim⟩ :=
    ConvergenceRegion.derivativeLimit_on_window d J (Ambient.cubicExhaustion d) hJ_pos hxz
  have hwin_open : IsOpen (ConvergenceRegion.window d J) := isOpen_Ioo
  have hwin_sub : ConvergenceRegion.window d J ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) :=
    ConvergenceRegion.window_subset_highTemp d J hJ_pos hd
  -- HasDerivAt of the infinite correlation with profile g' on the window.
  have hHasDeriv : ∀ β ∈ Set.Icc β₁ β₂, HasDerivAt c (g' β) β := by
    intro β hβ
    exact correlationInfinite_hasDerivAt_beta_of_tendstoLocallyUniformlyOn_deriv
      hd (Ambient.cubicExhaustion d) x z hxz J hJ_pos g' hwin_open hwin_sub hderiv_lim
      β (hβ_window β hβ)
  have hc_diff : ∀ β ∈ Set.Icc β₁ β₂,
      DifferentiableAt ℝ
        (fun β' => Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}) β := by
    intro β hβ
    simpa [hc_def] using (hHasDeriv β hβ).differentiableAt
  -- uniform numerator bound `B`.
  set B : ℝ := J * (β₂ * J * ↑(2 * d) / (1 - β₂ * J * ↑(2 * d))) ^ 2 + J * (4 * ↑d) with hB_def
  have hfinall := lemma_17_5_2_finite_deriv_abs_le_high_temp_on_Icc_all_stages
    (Ambient.cubicExhaustion d) J hJ_pos.le hβ₁_pos hβ₁₂ hlt₂ (fun β' hβ' => hβ') hxz
  have hgB : ∀ β ∈ Set.Icc β₁ β₂, |g' β| ≤ B := by
    intro β hβ
    have hpoint : Filter.Tendsto
        (fun n => deriv (fun β' =>
          Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        Filter.atTop (nhds (g' β)) :=
      hderiv_lim.tendsto_at (hβ_window β hβ)
    refine le_of_tendsto ((continuous_abs.tendsto (g' β)).comp hpoint)
      (Filter.Eventually.of_forall (fun n => ?_))
    rw [hB_def]; exact hfinall n β hβ
  -- interval-uniform ratio lower bound `L_min`.
  set q₁ : ℝ := -Real.log (β₁ * J * ↑(2 * d)) with hq₁_def
  have hβ₁Jd_pos : 0 < β₁ * J * ↑(2 * d) := by positivity
  have hq₁_pos : 0 < q₁ := by
    rw [hq₁_def]; exact neg_pos.mpr (Real.log_neg hβ₁Jd_pos (hlt β₁ hβ₁_mem))
  set Lmin : ℝ := pseudoMassG α ρ q₁ / q₁ ^ (2 * α) with hLmin_def
  have hLmin_pos : 0 < Lmin := by
    rw [hLmin_def]; exact div_pos (pseudoMassG_pos α hq₁_pos.le hρ) (pow_pos hq₁_pos _)
  -- `Lmin ≤ c(β)/m(β)^{2α}` for every `β ∈ Icc`.
  have hratio : ∀ β ∈ Set.Icc β₁ β₂, Lmin ≤ c β / (m β) ^ (2 * α) := by
    intro β hβ
    have hβ_pos : 0 < β := (hβ_highTemp β hβ).1
    set q : ℝ := -Real.log (β * J * ↑(2 * d)) with hq_def
    have hβJd_pos : 0 < β * J * ↑(2 * d) := by positivity
    have hq_pos : 0 < q := by
      rw [hq_def]; exact neg_pos.mpr (Real.log_neg hβJd_pos (hlt β hβ))
    -- per-β ratio lower bound from the merged helper.
    have hperβ : pseudoMassG α ρ q / q ^ (2 * α) ≤ c β / (m β) ^ (2 * α) := by
      rw [hc_def, hm_def, hq_def]
      exact lemma_17_5_2_profile_lower_ratio_lower_cubic hα hd hρ hJ_pos hβ_pos
        (hlt β hβ) (hcorr β hβ) (hprofile β hβ)
    -- `q ≤ q₁` since `β₁ ≤ β`.
    have hq_le : q ≤ q₁ := by
      rw [hq_def, hq₁_def]
      apply neg_le_neg
      apply Real.log_le_log hβ₁Jd_pos
      have : β₁ * J * ↑(2 * d) ≤ β * J * ↑(2 * d) := by
        apply mul_le_mul_of_nonneg_right _ hd_pos.le
        exact mul_le_mul_of_nonneg_right hβ.1 hJ_pos.le
      exact this
    -- `Lmin ≤ pseudoMassG α ρ q / q^{2α}` by monotonicity.
    have hgq_anti : pseudoMassG α ρ q₁ ≤ pseudoMassG α ρ q :=
      pseudoMassG_antitoneOn hα hρ (Set.mem_Ici.mpr hq_pos.le)
        (Set.mem_Ici.mpr hq₁_pos.le) hq_le
    have hq_pow_le : q ^ (2 * α) ≤ q₁ ^ (2 * α) := pow_le_pow_left₀ hq_pos.le hq_le _
    have hLmin_le : Lmin ≤ pseudoMassG α ρ q / q ^ (2 * α) := by
      rw [hLmin_def]
      calc pseudoMassG α ρ q₁ / q₁ ^ (2 * α)
          ≤ pseudoMassG α ρ q / q₁ ^ (2 * α) :=
            div_le_div_of_nonneg_right hgq_anti (pow_pos hq₁_pos _).le
        _ ≤ pseudoMassG α ρ q / q ^ (2 * α) :=
            div_le_div_of_nonneg_left (pseudoMassG_pos α hq_pos.le hρ).le
              (pow_pos hq_pos _) hq_pow_le
    exact le_trans hLmin_le hperβ
  -- the fixed constant `K`.
  set K : ℝ := max 1 (B / Lmin) with hK_def
  have hK_pos : 0 < K := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hK_ge : B / Lmin ≤ K := le_max_right _ _
  -- the interval `hcomp` with the single `K`.
  have hcomp : ∀ β ∈ Set.Icc β₁ β₂,
      |deriv (fun β' =>
          Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}) β| ≤
        K *
          Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} /
          (pseudoMassFromParamsAtPair hα hρ d (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) x z) ^ (2 * α) := by
    intro β hβ
    have hderiv_eq : deriv (fun β' =>
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}) β = g' β := by
      have := (hHasDeriv β hβ).deriv
      simpa [hc_def] using this
    rw [hderiv_eq, mul_div_assoc]
    calc |g' β| ≤ B := hgB β hβ
      _ = B / Lmin * Lmin := by rw [div_mul_cancel₀ B hLmin_pos.ne']
      _ ≤ K * Lmin := mul_le_mul_of_nonneg_right hK_ge hLmin_pos.le
      _ ≤ K * (c β / (m β) ^ (2 * α)) := mul_le_mul_of_nonneg_left (hratio β hβ) hK_pos.le
  -- feed the consumer.
  refine ⟨K, hK_pos, ?_⟩
  exact pseudoMassFromParamsAtPair_beta_pow_succ_lipschitz_on_Icc_of_corr_differentiableAt
    hα hρ (Ambient.cubicExhaustion d) J x z hβ₁₂ hc_diff hcorr hcomp

end Ambient
end IsingModel
