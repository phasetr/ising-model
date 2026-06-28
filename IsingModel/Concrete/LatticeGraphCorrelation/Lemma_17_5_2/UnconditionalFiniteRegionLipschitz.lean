import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.UnconditionalProfileLower

/-!
# GJ §17.5 Lemma 17.5.2(a) — UNCONDITIONAL finite-region Lipschitz of `m⁻(σ, A)`

This module removes the `hprofile` hypothesis from the conditional finite-region Lipschitz
(`FiniteRegionPseudoMassDistLipschitz.lean`, #4332) by re-parametrizing the chain to the **faithful
inverse-correlation-length rate `−log tanh(βJ)`** and discharging the per-pair profile lower bound
with the unconditional bound `pseudoMassG_dist_tanh_rate_le_correlationInfinite_cubic` (#4333).

The engine is the rate-agnostic abstracted interval Lipschitz
`pseudoMassFromParamsAtPair_pow_succ_lipschitz_on_window_of_ratio_lower`, which takes a single
interval-uniform denominator ratio lower bound `Lmin ≤ c(β)/m(β)^(2α)` (instead of a profile
hypothesis at a fixed rate); the conditional #4331 and the unconditional route below are both thin
consumers of it.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 / Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

open Set

/-- **Rate-agnostic abstracted interval Lipschitz of `(m⁻)^{2α+1}` on the window.**
Given any interval-uniform denominator ratio lower bound `Lmin ≤ c(β)/m(β)^(2α)` (`0 < Lmin`), the
`(2α+1)`-power of the fixed-radius per-pair pseudo-mass is Lipschitz on `Icc β₁ β₂ ⊆ window` with a
single constant.  This is the rate-independent engine extracted from
`lemma_17_5_2_pseudoMass_pow_succ_lipschitz_on_window_of_profile_lower` (#4331): the numerator bound
`B`, the axiom-free window provider, differentiability and active range are all rate-agnostic; only
the ratio lower bound carries the rate, here abstracted into `hratio`. -/
theorem pseudoMassFromParamsAtPair_pow_succ_lipschitz_on_window_of_ratio_lower
    {d α : ℕ} (hα : 1 ≤ α) (hd : 1 ≤ d) {ρ : ℝ} (hρ : 0 < ρ)
    {J β₁ β₂ : ℝ} (hJ_pos : 0 < J) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ ConvergenceRegion.window d J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    (Lmin : ℝ) (hLmin_pos : 0 < Lmin)
    (hratio : ∀ β ∈ Set.Icc β₁ β₂,
      Lmin ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} /
        (pseudoMassFromParamsAtPair hα hρ d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z) ^ (2 * α)) :
    ∃ K : ℝ, 0 < K ∧
      |(pseudoMassFromParamsAtPair hα hρ d (Ambient.cubicExhaustion d)
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) ^ (2 * α + 1) -
          (pseudoMassFromParamsAtPair hα hρ d (Ambient.cubicExhaustion d)
            (⟨J, 0, β₁⟩ : IsingParams ℝ) x z) ^ (2 * α + 1)| ≤
        ↑(2 * α + 1) * K / ρ * (β₂ - β₁) := by
  classical
  set c : ℝ → ℝ := fun β =>
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} with hc_def
  set m : ℝ → ℝ := fun β =>
    pseudoMassFromParamsAtPair hα hρ d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) x z with hm_def
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
  have hcorr : ∀ β ∈ Set.Icc β₁ β₂, c β ∈ Set.Ioo (0 : ℝ) 2 := by
    intro β hβ
    have hβ_pos : 0 < β := (hβ_highTemp β hβ).1
    have hβJ_pos : 0 < β * J := mul_pos hβ_pos hJ_pos
    exact correlationInfinite_pair_active_of_betaJ_pos_exhaustion
      (Ambient.cubicExhaustion d) hβ_pos hβJ_pos x z hxz
  obtain ⟨g', hderiv_lim⟩ :=
    ConvergenceRegion.derivativeLimit_on_window d J (Ambient.cubicExhaustion d) hJ_pos hxz
  have hwin_open : IsOpen (ConvergenceRegion.window d J) := isOpen_Ioo
  have hwin_sub : ConvergenceRegion.window d J ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) :=
    ConvergenceRegion.window_subset_highTemp d J hJ_pos hd
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
  set K : ℝ := max 1 (B / Lmin) with hK_def
  have hK_pos : 0 < K := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hK_ge : B / Lmin ≤ K := le_max_right _ _
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
  refine ⟨K, hK_pos, ?_⟩
  exact pseudoMassFromParamsAtPair_beta_pow_succ_lipschitz_on_Icc_of_corr_differentiableAt
    hα hρ (Ambient.cubicExhaustion d) J x z hβ₁₂ hc_diff hcorr hcomp

/-- **General-rate ratio lower bound.**  For any positive rate `q` with the profile lower bound
`pseudoMassG α ρ q ≤ c` (and active range `c ∈ Ioo 0 2`), the denominator ratio is lower-bounded:
`pseudoMassG α ρ q / q^(2α) ≤ c / m^(2α)` (`m = pseudoMassFromParamsAtPair`).  This is the
rate-generalized form of `lemma_17_5_2_profile_lower_ratio_lower_cubic` (#4330), which fixed
`q = −log(βJ·2d)`; here `q` is arbitrary (used at the faithful rate `q = −log tanh(βJ)`). -/
theorem pseudoMassFromParamsAtPair_ratio_lower_of_pseudoMassG_le_corr
    {α d : ℕ} (hα : 1 ≤ α) {ρ : ℝ} (hρ : 0 < ρ) {J β q : ℝ} (hq_pos : 0 < q)
    {x z : Fin d → ℤ}
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2)
    (hprofile : pseudoMassG α ρ q ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    pseudoMassG α ρ q / q ^ (2 * α) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} /
        (pseudoMassFromParamsAtPair hα hρ d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z) ^ (2 * α) := by
  set c : ℝ := Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} with hc_def
  set m : ℝ := pseudoMassFromParamsAtPair hα hρ d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) x z with hm_def
  have hm_pos : 0 < m := by
    rw [hm_def]
    exact pseudoMassFromParamsAtPair_pos_of_corr_mem hα hρ d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) x z hcorr
  have hgq_pos : 0 < pseudoMassG α ρ q := pseudoMassG_pos α hq_pos.le hρ
  have hmq : m ≤ q := by
    have hm_eq : m = pseudoMass hα hρ hcorr := by
      rw [hm_def]; exact pseudoMassExt_of_mem hα hρ hcorr
    rw [hm_eq]
    exact (pseudoMass_le_iff_pseudoMassG_le hα hρ hcorr hq_pos.le).mpr hprofile
  have hm_pow_pos : 0 < m ^ (2 * α) := pow_pos hm_pos _
  have hpow_le : m ^ (2 * α) ≤ q ^ (2 * α) := pow_le_pow_left₀ hm_pos.le hmq _
  have hc_ge : pseudoMassG α ρ q ≤ c := by rw [hc_def]; exact hprofile
  calc pseudoMassG α ρ q / q ^ (2 * α)
      ≤ pseudoMassG α ρ q / m ^ (2 * α) :=
        div_le_div_of_nonneg_left hgq_pos.le hm_pow_pos hpow_le
    _ ≤ c / m ^ (2 * α) :=
        div_le_div_of_nonneg_right hc_ge hm_pow_pos.le


/-- **GJ §17.5 UNCONDITIONAL per-pair distance interval Lipschitz of `(m⁻(x,z,·))^{2α+1}` on the
window.**  For any distinct pair `x ≠ z` and `Icc β₁ β₂ ⊆ ConvergenceRegion.window d J`,
`∃ K>0, |m⁻(x,z,β₂)^{2α+1} − m⁻(x,z,β₁)^{2α+1}| ≤ (2α+1)K/dist·(β₂−β₁)` with **no profile
hypothesis** — the faithful profile lower bound is discharged by
`pseudoMassG_dist_tanh_rate_le_correlationInfinite_cubic` (#4333) at the rate `−log tanh(βJ)`.

The interval-uniform ratio lower bound `Lmin = pseudoMassG α (dist) q₁ / q₁^{2α}`
(`q₁ = −log tanh(β₁J)`) is established from the per-`β` general ratio lower bound and the
monotonicity of `q(β) = −log tanh(βJ)` (decreasing in `β`) and `pseudoMassG`. -/
theorem pseudoMassFromParamsAtPairDist_pow_succ_lipschitz_on_window
    {d α : ℕ} (hα : 1 ≤ α) (hd : 1 ≤ d)
    {J β₁ β₂ : ℝ} (hJ_pos : 0 < J) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ ConvergenceRegion.window d J)
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    ∃ K : ℝ, 0 < K ∧
      |(pseudoMassFromParamsAtPairDist hα (Ambient.cubicExhaustion d)
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) ^ (2 * α + 1) -
          (pseudoMassFromParamsAtPairDist hα (Ambient.cubicExhaustion d)
            (⟨J, 0, β₁⟩ : IsingParams ℝ) x z) ^ (2 * α + 1)| ≤
        ↑(2 * α + 1) * K / (IsingModel.latticeDistance d x z : ℝ) * (β₂ - β₁) := by
  have hpos : (0 : ℝ) < (IsingModel.latticeDistance d x z : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (fun h => hxz ((IsingModel.latticeDistance_eq_zero_iff d x z).mp h))
  have hβ_window : ∀ β ∈ Set.Icc β₁ β₂, β ∈ ConvergenceRegion.window d J := fun β hβ => hIcc hβ
  have hβ_pos : ∀ β ∈ Set.Icc β₁ β₂, 0 < β := fun β hβ => (hβ_window β hβ).1
  have hβ₁_mem : β₁ ∈ Set.Icc β₁ β₂ := ⟨le_refl β₁, hβ₁₂⟩
  -- rate `q(β) = −log tanh(βJ)`, positive and decreasing in β.
  have hq_pos : ∀ β ∈ Set.Icc β₁ β₂, (0 : ℝ) < -Real.log (Real.tanh (β * J)) := fun β hβ =>
    lt_of_lt_of_le one_pos (one_le_neg_log_tanh_betaJ_of_window hJ_pos (hβ_window β hβ))
  have hcorr : ∀ β ∈ Set.Icc β₁ β₂,
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2 := by
    intro β hβ
    exact correlationInfinite_pair_active_of_betaJ_pos_exhaustion
      (Ambient.cubicExhaustion d) (hβ_pos β hβ) (mul_pos (hβ_pos β hβ) hJ_pos) x z hxz
  set q₁ : ℝ := -Real.log (Real.tanh (β₁ * J)) with hq₁_def
  have hq₁_pos : 0 < q₁ := hq_pos β₁ hβ₁_mem
  set Lmin : ℝ :=
    pseudoMassG α (IsingModel.latticeDistance d x z : ℝ) q₁ / q₁ ^ (2 * α) with hLmin_def
  have hLmin_pos : 0 < Lmin := by
    rw [hLmin_def]; exact div_pos (pseudoMassG_pos α hq₁_pos.le hpos) (pow_pos hq₁_pos _)
  have hratio : ∀ β ∈ Set.Icc β₁ β₂,
      Lmin ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} /
        (pseudoMassFromParamsAtPair hα hpos d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z) ^ (2 * α) := by
    intro β hβ
    set q : ℝ := -Real.log (Real.tanh (β * J)) with hq_def
    have hq_pos' : 0 < q := hq_pos β hβ
    -- per-β ratio lower bound (general rate q), discharged by #4333.
    have hprofile : pseudoMassG α (IsingModel.latticeDistance d x z : ℝ) q ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} := by
      rw [hq_def]
      exact pseudoMassG_dist_tanh_rate_le_correlationInfinite_cubic hJ_pos (hβ_pos β hβ) hxz
        (hβ_window β hβ)
    have hperβ := pseudoMassFromParamsAtPair_ratio_lower_of_pseudoMassG_le_corr
      hα hpos hq_pos' (hcorr β hβ) hprofile
    -- `q ≤ q₁` since tanh is increasing and β₁ ≤ β.
    have hq_le : q ≤ q₁ := by
      rw [hq_def, hq₁_def]
      apply neg_le_neg
      apply Real.log_le_log (by
        rw [Real.tanh_eq_sinh_div_cosh]
        exact div_pos (Real.sinh_pos_iff.mpr (mul_pos (hβ_pos β₁ hβ₁_mem) hJ_pos))
          (Real.cosh_pos _))
      exact Real.tanh_strictMono.monotone (by
        exact mul_le_mul_of_nonneg_right hβ.1 hJ_pos.le)
    have hgq_anti : pseudoMassG α (IsingModel.latticeDistance d x z : ℝ) q₁
        ≤ pseudoMassG α (IsingModel.latticeDistance d x z : ℝ) q :=
      pseudoMassG_antitoneOn hα hpos (Set.mem_Ici.mpr hq_pos'.le)
        (Set.mem_Ici.mpr hq₁_pos.le) hq_le
    have hq_pow_le : q ^ (2 * α) ≤ q₁ ^ (2 * α) := pow_le_pow_left₀ hq_pos'.le hq_le _
    have hLmin_le :
        Lmin ≤ pseudoMassG α (IsingModel.latticeDistance d x z : ℝ) q / q ^ (2 * α) := by
      rw [hLmin_def]
      calc pseudoMassG α (IsingModel.latticeDistance d x z : ℝ) q₁ / q₁ ^ (2 * α)
          ≤ pseudoMassG α (IsingModel.latticeDistance d x z : ℝ) q / q₁ ^ (2 * α) :=
            div_le_div_of_nonneg_right hgq_anti (pow_pos hq₁_pos _).le
        _ ≤ pseudoMassG α (IsingModel.latticeDistance d x z : ℝ) q / q ^ (2 * α) :=
            div_le_div_of_nonneg_left (pseudoMassG_pos α hq_pos'.le hpos).le
              (pow_pos hq_pos' _) hq_pow_le
    exact le_trans hLmin_le hperβ
  obtain ⟨K, hK, hb⟩ :=
    pseudoMassFromParamsAtPair_pow_succ_lipschitz_on_window_of_ratio_lower
      hα hd hpos hJ_pos hβ₁₂ hIcc hxz Lmin hLmin_pos hratio
  refine ⟨K, hK, ?_⟩
  rw [pseudoMassFromParamsAtPairDist_eq_atPair_cubic hα _ hxz hpos,
    pseudoMassFromParamsAtPairDist_eq_atPair_cubic hα _ hxz hpos]
  exact hb


/-- **GJ §17.5 Lemma 17.5.2(a) — UNCONDITIONAL finite-region Lipschitz of `m⁻(σ, A)^{2α+1}`.**
For a *fixed* bounded region `A` (with at least one distinct pair) and `Icc β₁ β₂` inside the
convergence window, **with no profile hypothesis**,
`∃ C>0, |m⁻(σ₂, A)^{2α+1} − m⁻(σ₁, A)^{2α+1}| ≤ C·(β₂ − β₁)`.

This removes the conditional `hprofile` of #4332: each per-pair distance interval Lipschitz is now
unconditional (`pseudoMassFromParamsAtPairDist_pow_succ_lipschitz_on_window`, discharged via the
faithful-rate profile bound #4333); the finite `Finset.inf'` assembly is unchanged (odd-power
commutes with `inf'`; `inf'` of finitely many Lipschitz functions is Lipschitz via the achieved
infimum).  The constant is per-`A` (uniform-in-`A` / infinite-envelope continuity remains a separate
question, #4320).

References: Glimm--Jaffe §17.5, Theorem 17.5.1 / Lemma 17.5.2, pp.~311--312. -/
theorem finiteRegionPseudoMassDist_pow_succ_lipschitz_on_window
    {d α : ℕ} (hα : 1 ≤ α) (hd : 1 ≤ d)
    {J β₁ β₂ : ℝ} (hJ_pos : 0 < J) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ ConvergenceRegion.window d J)
    {A : Finset (Fin d → ℤ)} (hA : (finiteRegionDistinctPairs A).Nonempty) :
    ∃ C : ℝ, 0 < C ∧
      |(finiteRegionPseudoMassDist hα (Ambient.cubicExhaustion d)
            (⟨J, 0, β₂⟩ : IsingParams ℝ) A hA) ^ (2 * α + 1) -
          (finiteRegionPseudoMassDist hα (Ambient.cubicExhaustion d)
            (⟨J, 0, β₁⟩ : IsingParams ℝ) A hA) ^ (2 * α + 1)| ≤ C * (β₂ - β₁) := by
  classical
  set pairs := finiteRegionDistinctPairs A with hpairs_def
  set hpow : ℝ → (Fin d → ℤ) × (Fin d → ℤ) → ℝ := fun β q =>
    (pseudoMassFromParamsAtPairDist hα (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) q.1 q.2) ^ (2 * α + 1) with hhpow_def
  have hmono : Monotone (fun t : ℝ => t ^ (2 * α + 1)) :=
    (Odd.strictMono_pow ⟨α, by ring⟩).monotone
  have hginf : ∀ a b : ℝ, (a ⊓ b) ^ (2 * α + 1) = a ^ (2 * α + 1) ⊓ b ^ (2 * α + 1) := by
    intro a b
    rcases le_total a b with h | h
    · rw [inf_eq_left.mpr h, inf_eq_left.mpr (hmono h)]
    · rw [inf_eq_right.mpr h, inf_eq_right.mpr (hmono h)]
  have hpow_eq : ∀ β,
      (finiteRegionPseudoMassDist hα (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) A hA) ^ (2 * α + 1)
        = pairs.inf' hA (hpow β) := by
    intro β
    unfold finiteRegionPseudoMassDist
    rw [Finset.comp_inf'_eq_inf'_comp hA (fun t => t ^ (2 * α + 1)) hginf]
    rfl
  have hper : ∀ q ∈ pairs, ∃ Cq : ℝ, 0 < Cq ∧
      |hpow β₂ q - hpow β₁ q| ≤ Cq * (β₂ - β₁) := by
    intro q hq
    obtain ⟨_hq1, _hq2, hxz⟩ := mem_finiteRegionDistinctPairs.mp hq
    have hpos : (0 : ℝ) < (IsingModel.latticeDistance d q.1 q.2 : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero
        (fun h => hxz ((IsingModel.latticeDistance_eq_zero_iff d q.1 q.2).mp h))
    obtain ⟨K, hK, hb⟩ :=
      pseudoMassFromParamsAtPairDist_pow_succ_lipschitz_on_window
        hα hd hJ_pos hβ₁₂ hIcc hxz
    exact ⟨↑(2 * α + 1) * K / (IsingModel.latticeDistance d q.1 q.2 : ℝ),
      by positivity, hb⟩
  choose! Cq hCqpos hCqbd using hper
  refine ⟨pairs.sup' hA Cq, ?_, ?_⟩
  · obtain ⟨q₀, hq₀⟩ := hA
    exact lt_of_lt_of_le (hCqpos q₀ hq₀) (Finset.le_sup' Cq hq₀)
  · set C := pairs.sup' hA Cq with hC_def
    have hβsub_nn : 0 ≤ β₂ - β₁ := by linarith
    have hperC : ∀ q ∈ pairs, |hpow β₂ q - hpow β₁ q| ≤ C * (β₂ - β₁) := by
      intro q hq
      refine le_trans (hCqbd q hq) ?_
      exact mul_le_mul_of_nonneg_right (Finset.le_sup' Cq hq) hβsub_nn
    rw [hpow_eq β₂, hpow_eq β₁, abs_le]
    constructor
    · obtain ⟨q₂, hq₂_mem, hq₂_eq⟩ := Finset.exists_mem_eq_inf' hA (hpow β₂)
      have h1 : pairs.inf' hA (hpow β₁) ≤ hpow β₁ q₂ := Finset.inf'_le _ hq₂_mem
      have h2 : |hpow β₂ q₂ - hpow β₁ q₂| ≤ C * (β₂ - β₁) := hperC q₂ hq₂_mem
      rw [hq₂_eq]
      have := (abs_le.mp h2).1
      linarith
    · obtain ⟨q₁, hq₁_mem, hq₁_eq⟩ := Finset.exists_mem_eq_inf' hA (hpow β₁)
      have h1 : pairs.inf' hA (hpow β₂) ≤ hpow β₂ q₁ := Finset.inf'_le _ hq₁_mem
      have h2 : |hpow β₂ q₁ - hpow β₁ q₁| ≤ C * (β₂ - β₁) := hperC q₁ hq₁_mem
      rw [hq₁_eq]
      have := (abs_le.mp h2).2
      linarith


end Ambient
end IsingModel
