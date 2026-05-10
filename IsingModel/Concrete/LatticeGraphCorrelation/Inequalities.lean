import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundation
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransfer
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassLebowitzDerivative
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempLipschitz
import IsingModel.Concrete.LatticeGraphCorrelation.InfiniteVolumeCorrelationInequalities
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationSymmetry
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationDecay
import IsingModel.Concrete.LatticeGraphCorrelation.PointwiseRegularity
import IsingModel.Concrete.LatticeGraphCorrelation.SusceptibilityPointwiseRegularity
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.AmbientLattice.BetaDerivative
import IsingModel.Inequalities.HighTemp
import IsingModel.LatticeExpSum
import IsingModel.BetaDerivative
import IsingModel.PseudoMass
import Mathlib.Topology.UniformSpace.Dini
import Mathlib.Analysis.BoundedVariation

/-!
# Inequalities and §17 lattice mass at ℤ^d

ℤ^d wrappers for:
1. GHS inequality (truncated3 ≤ 0) and Lebowitz inequality (truncated4 ≤ 0)
2. §17.1/§17.5 lattice mass / correlation length

This module also imports
`IsingModel.Concrete.LatticeGraphCorrelation.CorrelationDecay` to preserve the
legacy `Inequalities` import path for §5.1 conditional and distance-based
cluster-decay wrappers, and
`IsingModel.Concrete.LatticeGraphCorrelation.PointwiseRegularity` /
`IsingModel.Concrete.LatticeGraphCorrelation.SusceptibilityPointwiseRegularity`
to preserve the legacy path for finite-stage correlation and susceptibility
regularity compatibility names. New code should import the narrower child
modules directly for those declarations.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ## §17.1 / §17.5 lattice mass / correlation length foundation

The foundational `HasExponentialDecay` and `latticeMass` API now lives in
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundation`. This
module imports it to preserve the legacy `Inequalities` import path.
-/

/-! ## §5.1 / §17.5 high-temperature lattice-mass bounds

The concrete high-temperature `HasExponentialDecay`, lattice-mass bounds,
antitonicity, and tanh lower-bound API now lives in
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature`. This
module imports it to preserve the legacy `Inequalities` import path.
-/

/-! ## §17.1 / §17.5 pseudo-mass transfer and critical-temperature bridges

The concrete product-summability, critical inverse temperature, pseudo-mass
transfer, and below-critical cluster / summability bridge API now lives in
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransfer`.
This module imports it to preserve the legacy `Inequalities` import path.
-/

/-! ## §17.1 d = 0 special case -/

/-- **Vacuous HasExponentialDecay in dimension zero**: for `d = 0`, the lattice
`Fin 0 → ℤ` is a singleton, so there are no distinct pairs `(i, j)`, and
`HasExponentialDecay 0 Λ p α` holds for every `Λ`, `p`, and `α`. -/
private lemma HasExponentialDecay_dim_zero
    (Λ : Ambient.Exhaustion (Fin 0 → ℤ)) (p : IsingParams ℝ) (α : ℝ) :
    HasExponentialDecay 0 Λ p α :=
  ⟨0, le_refl _, fun _i _j hij =>
    absurd (funext (fun x => Fin.elim0 x)) hij⟩

/-- **Lattice mass is `⊤` in dimension zero**: the set of valid decay rates is all of
`NNReal` (vacuous condition), so `latticeMass = sSup (NNReal → ENNReal) = ⊤`. -/
private lemma latticeMass_eq_top_of_dim_zero
    (Λ : Ambient.Exhaustion (Fin 0 → ℤ)) (p : IsingParams ℝ) :
    latticeMass 0 Λ p = ⊤ := by
  refine eq_top_iff.mpr ?_
  refine le_sSup_iff.mpr ?_
  intro b hb
  by_contra hb_ne
  rw [not_le] at hb_ne
  set α : NNReal := b.toNNReal + 1
  have hαmem : (α : ENNReal) ∈ (fun α : NNReal => (α : ENNReal)) ''
      {α : NNReal | HasExponentialDecay 0 Λ p (α : ℝ)} :=
    ⟨α, HasExponentialDecay_dim_zero Λ p (α : ℝ), rfl⟩
  have hα_le_b : (α : ENNReal) ≤ b := hb hαmem
  have hb_ne_top : b ≠ ⊤ := ne_of_lt hb_ne
  have hb_toNN : ((b.toNNReal : ENNReal) : ENNReal) = b := ENNReal.coe_toNNReal hb_ne_top
  have hα_eq : (α : ENNReal) = b + 1 := by
    simp only [α, ENNReal.coe_add, ENNReal.coe_one, hb_toNN]
  rw [hα_eq] at hα_le_b
  exact absurd hα_le_b (not_le.mpr (ENNReal.lt_add_right hb_ne_top one_ne_zero))

/-- **Critical inverse temperature is `⊤` in dimension zero** (GJ §17.1):
for `d = 0` (single-site model, no neighbors), the lattice mass is always `⊤ > 0`,
so all `β ≥ 0` are in the high-temperature set and `criticalInverseTemp 0 J = ⊤`.

Physics: a zero-dimensional Ising model has no ferromagnetic interactions and no
phase transition at any temperature; the "critical temperature" is infinite (β_c = ⊤). -/
theorem criticalInverseTemp_eq_top_of_dim_zero (J : ℝ) :
    criticalInverseTemp 0 J = ⊤ := by
  unfold criticalInverseTemp
  refine eq_top_iff.mpr ?_
  refine le_sSup_iff.mpr ?_
  intro b hb
  by_contra hb_ne
  rw [not_le] at hb_ne
  have hb_ne_top : b ≠ ⊤ := ne_of_lt hb_ne
  set β₀ : NNReal := b.toNNReal + 1
  have hmass_pos : 0 < latticeMass 0 (cubicExhaustion 0)
      (⟨J, 0, (β₀ : ℝ)⟩ : IsingParams ℝ) := by
    rw [latticeMass_eq_top_of_dim_zero]
    simp
  have hmem : ENNReal.ofReal (β₀ : ℝ) ∈ ENNReal.ofReal ''
      { β : ℝ | 0 ≤ β ∧ 0 < latticeMass 0 (cubicExhaustion 0)
          (⟨J, 0, β⟩ : IsingParams ℝ) } :=
    ⟨(β₀ : ℝ), ⟨NNReal.coe_nonneg _, hmass_pos⟩, rfl⟩
  have hle : ENNReal.ofReal (β₀ : ℝ) ≤ b := hb hmem
  have hb_toNN : ((b.toNNReal : ENNReal) : ENNReal) = b := ENNReal.coe_toNNReal hb_ne_top
  have hβ₀_eq : ENNReal.ofReal (β₀ : ℝ) = b + 1 := by
    simp only [β₀, ENNReal.ofReal_coe_nnreal, ENNReal.coe_add, ENNReal.coe_one, hb_toNN]
  rw [hβ₀_eq] at hle
  exact absurd hle (not_le.mpr (ENNReal.lt_add_right hb_ne_top one_ne_zero))

/-! ## §17.1 J = 0 special case -/

/-- **Critical inverse temperature is `⊤` when `J = 0`** (GJ §17.1):
for zero coupling constant, `latticeMass = ⊤` for every `β ≥ 0` (either from
`latticeMass_top_of_beta_zero` at `β = 0`, or from `latticeMass_top_of_J_zero` at `β > 0`),
so the defining set is all of `[0,∞)` and `criticalInverseTemp d 0 = ⊤`.

Physics: with no coupling between sites, no phase transition occurs at any finite inverse
temperature (β_c = ⊤ means T_c = 0). This is the J = 0 companion of
`criticalInverseTemp_eq_top_of_dim_zero`. -/
theorem criticalInverseTemp_eq_top_of_J_zero (d : ℕ) :
    criticalInverseTemp d 0 = ⊤ := by
  apply le_antisymm le_top
  rw [← ENNReal.iSup_natCast]
  apply iSup_le
  intro n
  rw [← ENNReal.ofReal_natCast n]
  apply criticalInverseTemp_ge_ofReal_of_latticeMass_pos (Nat.cast_nonneg n)
  rcases n with _ | n
  · rw [Nat.cast_zero, latticeMass_top_of_beta_zero]; exact ENNReal.zero_lt_top
  · have hf : Ferromagnetic (⟨(0 : ℝ), (0 : ℝ), (↑(n + 1) : ℝ)⟩ : IsingParams ℝ) :=
      ⟨le_refl _, le_refl _, by positivity⟩
    rw [latticeMass_top_of_J_zero d (cubicExhaustion d) 0 _ hf]
    exact ENNReal.zero_lt_top

/-! ## §17.1 / §17.5 finite susceptibility and Lebowitz derivative bounds

The concrete finite-susceptibility wrapper and Lebowitz derivative bound API
now lives in
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassLebowitzDerivative`.
This module imports it to preserve the legacy `Inequalities` import path.
-/

/-! ## §17.5 high-temperature Lipschitz and uniform convergence wrappers

The concrete high-temperature Lipschitz, continuity, uniform convergence,
a.e. differentiability, locally bounded variation, locally uniform convergence,
and interior-continuity API now lives in
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempLipschitz`.
This module imports it to preserve the legacy `Inequalities` import path.
-/

/-- **Per-stage linear bound at β = 0** (Step 176, helper):
For each finite-volume stage `n`, `r ≠ s`, and high-temperature `β ∈ (0, b]` with `bJ·2d < 1`:
`corr_n(r, s, β) ≤ (J·M(b)² + J·4d) · β`.

Proof: For any `0 < a ≤ β`, by Step 167's uniform-in-n Lipschitz on `[a, b]` plus
monotonicity, `corr_n(β) ≤ corr_n(a) + C · β`. Taking `a → 0⁺` and using continuity
of `corr_n` at 0 with `corr_n(0) = 0`, we conclude `corr_n(β) ≤ C · β`. -/
private lemma inducedLatticeGraph_correlation_le_const_mul_beta
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ : 0 ≤ J)
    (b : ℝ) (hlt : b * J * ↑(2 * d) < 1)
    (n : ℕ) (r s : ↑(Λ.volume n)) (hrs : r ≠ s)
    (β : ℝ) (hβ_pos : 0 < β) (hβb : β ≤ b) :
    let G := inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)
    let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
    IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} ≤
      (J * M ^ 2 + J * (4 * ↑d)) * β := by
  intro G M
  set C : ℝ := J * M ^ 2 + J * (4 * ↑d) with hC_def
  -- For each 0 < a ≤ β: corr_n(β) ≤ corr_n(a) + C * (β - a)
  have h_per_a : ∀ a : ℝ, 0 < a → a ≤ β →
      IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} ≤
      IsingModel.correlation G (⟨J, 0, a⟩ : IsingParams ℝ) {r, s} + C * (β - a) := by
    intro a ha hab
    have h_lip := inducedLatticeGraph_correlation_norm_sub_le Λ J hJ a b ha (hab.trans hβb) hlt
        n r s hrs a β (Set.left_mem_Icc.mpr (hab.trans hβb)) ⟨hab, hβb⟩
    -- h_lip : ‖corr(β) - corr(a)‖ ≤ C * ‖β - a‖ (with let G, let M)
    -- Strip the lets via simp
    simp only at h_lip
    have hβ_minus_a_nonneg : 0 ≤ β - a := by linarith
    have hcorr_diff_nonneg : 0 ≤
        IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} -
        IsingModel.correlation G (⟨J, 0, a⟩ : IsingParams ℝ) {r, s} := by
      have hmono := IsingModel.correlation_monotoneOn_beta G J hJ {r, s}
      have ha_in : a ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr ha.le
      have hβ_in : β ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hβ_pos.le
      linarith [hmono ha_in hβ_in hab]
    have habs1 : ‖IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} -
        IsingModel.correlation G (⟨J, 0, a⟩ : IsingParams ℝ) {r, s}‖ =
        IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} -
        IsingModel.correlation G (⟨J, 0, a⟩ : IsingParams ℝ) {r, s} :=
      Real.norm_of_nonneg hcorr_diff_nonneg
    have habs2 : ‖β - a‖ = β - a := Real.norm_of_nonneg hβ_minus_a_nonneg
    rw [habs1, habs2] at h_lip
    linarith
  -- Now show corr_n(β) ≤ C * β by taking a → 0+
  have h_cont_corr_at_0 : ContinuousAt
      (fun a => IsingModel.correlation G (⟨J, 0, a⟩ : IsingParams ℝ) {r, s}) 0 :=
    IsingModel.correlation_continuousAt_beta G J 0 {r, s}
  have h_corr_at_0 : IsingModel.correlation G (⟨J, 0, 0⟩ : IsingParams ℝ) {r, s} = 0 :=
    IsingModel.correlation_beta_zero_vanish_of_nonempty_A G J 0 {r, s}
      (Finset.insert_nonempty _ _)
  -- The filter nhdsWithin 0 (Ioi 0) is NeBot
  have h_neBot : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  -- g(a) = corr_n(a) + C * (β - a) tends to 0 + C * β = C * β as a → 0+
  have h_g_tendsto : Filter.Tendsto
      (fun a => IsingModel.correlation G (⟨J, 0, a⟩ : IsingParams ℝ) {r, s} + C * (β - a))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (C * β)) := by
    have h1 : Filter.Tendsto
        (fun a => IsingModel.correlation G (⟨J, 0, a⟩ : IsingParams ℝ) {r, s})
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have htend := h_cont_corr_at_0.tendsto
      rw [h_corr_at_0] at htend
      exact htend.mono_left nhdsWithin_le_nhds
    have h2 : Filter.Tendsto
        (fun a : ℝ => C * (β - a)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (C * β)) := by
      have hf : Continuous fun a : ℝ => C * (β - a) := by
        exact Continuous.mul continuous_const (Continuous.sub continuous_const continuous_id)
      have hcont : Filter.Tendsto (fun a : ℝ => C * (β - a)) (nhds 0) (nhds (C * (β - 0))) :=
        hf.continuousAt (x := (0 : ℝ))
      have heq : C * (β - 0) = C * β := by ring
      rw [heq] at hcont
      exact hcont.mono_left nhdsWithin_le_nhds
    have hsum := h1.add h2
    simpa using hsum
  -- corr_n(β) ≤ g(a) eventually as a → 0+
  -- Need to restrict to a ≤ β. Use the fact that {a : a ≤ β} contains a neighborhood of 0 in Ioi 0
  have h_eventual : ∀ᶠ a in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} ≤
      IsingModel.correlation G (⟨J, 0, a⟩ : IsingParams ℝ) {r, s} + C * (β - a) := by
    -- Pick the neighborhood {a : a ≤ β} which is in nhds 0 (since 0 < β)
    have h_le : ∀ᶠ a in nhdsWithin (0 : ℝ) (Set.Ioi 0), a ≤ β := by
      have h_nhd : Set.Iic β ∈ nhds (0 : ℝ) := Iic_mem_nhds hβ_pos
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds h_nhd] with a ha hab
      exact hab
    filter_upwards [self_mem_nhdsWithin, h_le] with a ha hab
    exact h_per_a a ha hab
  exact ge_of_tendsto h_g_tendsto h_eventual

/-- **Linear bound on corr_∞ at β = 0** (Step 176, GJ §17.5):
For `0 ≤ J`, `1 ≤ d`, `0 < b` with `bJ·2d < 1`, and any `r ≠ s`, on the interval `(0, b]`:
`corr_∞(r, s, β) ≤ (J·M(b)² + J·4d) · β`,
where `M(b) = bJ·2d/(1 - bJ·2d)`.

In particular, `corr_∞(r, s, β) → 0` as `β → 0⁺`. -/
theorem correlationInfinite_le_const_mul_beta_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * J * ↑(2 * d) < 1)
    (β : ℝ) (hβ_pos : 0 < β) (hβb : β ≤ b) :
    let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      {r_val, s_val} ≤ (J * M ^ 2 + J * (4 * ↑d)) * β := by
  intro M
  set C : ℝ := J * M ^ 2 + J * (4 * ↑d) with hC_def
  have hferro : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
    ⟨hJ, le_refl 0, hβ_pos⟩
  -- corr_∞ = ⨆ n, corr_n_along_exhaustion. Use ciSup_le.
  rw [correlationInfinite_eq_ciSup]
  apply ciSup_le
  intro n
  -- For each n: corr_n_along_exhaustion ≤ C * β
  by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
  · -- Subset case: identify with finite-volume correlation and apply per-stage bound
    have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
    have hsn : s_val ∈ Λ.volume n :=
      Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
    have heq : correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n =
               IsingModel.correlation
                  (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                ⟨s_val, hsn⟩} := by
      rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
      congr 1
      ext u; rw [mem_liftFinset]
      simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
    rw [heq]
    have hsubsne : (⟨r_val, hrn⟩ : ↑(Λ.volume n)) ≠ ⟨s_val, hsn⟩ :=
      fun h => hrs (congrArg Subtype.val h)
    exact inducedLatticeGraph_correlation_le_const_mul_beta Λ J hJ b hlt n
      ⟨r_val, hrn⟩ ⟨s_val, hsn⟩ hsubsne β hβ_pos hβb
  · -- Non-subset case: corr_n_along_exhaustion = 0
    rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
    have hC_nn : 0 ≤ C := by
      have hb_pos' : 0 < b := hb_pos
      have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
      have hM_nn : 0 ≤ M :=
        div_nonneg (mul_nonneg (mul_nonneg hb_pos'.le hJ) (Nat.cast_nonneg _)) hdenom_b.le
      exact add_nonneg (mul_nonneg hJ (pow_nonneg hM_nn 2))
                       (mul_nonneg hJ (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
    exact mul_nonneg hC_nn hβ_pos.le

/-! ## Step 230: linear bound at J = 0 + right-continuity in J -/

/-- **Helper for Step 230**: per-stage finite-volume linear bound at J = 0. -/
private lemma inducedLatticeGraph_correlation_le_const_mul_J
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (β : ℝ) (hβ : 0 < β)
    (b : ℝ) (hlt : b * β * ↑(2 * d) < 1)
    (n : ℕ) (r s : ↑(Λ.volume n)) (hrs : r ≠ s)
    (J : ℝ) (hJ_pos : 0 < J) (hJb : J ≤ b) :
    let G := inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)
    let M : ℝ := b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d))
    IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} ≤
      (β * M ^ 2 + β * (4 * ↑d)) * J := by
  intro G M
  set C : ℝ := β * M ^ 2 + β * (4 * ↑d) with hC_def
  have h_per_a : ∀ a : ℝ, 0 < a → a ≤ J →
      IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} ≤
      IsingModel.correlation G (⟨a, 0, β⟩ : IsingParams ℝ) {r, s} + C * (J - a) := by
    intro a ha hab
    have h_lip := inducedLatticeGraph_correlation_norm_sub_le_J Λ β hβ a b ha (hab.trans hJb) hlt
        n r s hrs a J (Set.left_mem_Icc.mpr (hab.trans hJb)) ⟨hab, hJb⟩
    simp only at h_lip
    have hJ_minus_a_nonneg : 0 ≤ J - a := by linarith
    have hcorr_diff_nonneg : 0 ≤
        IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} -
        IsingModel.correlation G (⟨a, 0, β⟩ : IsingParams ℝ) {r, s} := by
      have hmono := IsingModel.correlation_monotone_J G 0 (le_refl 0) β hβ {r, s}
      have ha_in : a ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr ha.le
      have hJ_in : J ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hJ_pos.le
      have hmono_app : IsingModel.correlation G (⟨a, 0, β⟩ : IsingParams ℝ) {r, s} ≤
                       IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} :=
        hmono ha_in hJ_in hab
      linarith
    have habs1 : ‖IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} -
        IsingModel.correlation G (⟨a, 0, β⟩ : IsingParams ℝ) {r, s}‖ =
        IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} -
        IsingModel.correlation G (⟨a, 0, β⟩ : IsingParams ℝ) {r, s} :=
      Real.norm_of_nonneg hcorr_diff_nonneg
    have habs2 : ‖J - a‖ = J - a := Real.norm_of_nonneg hJ_minus_a_nonneg
    rw [habs1, habs2] at h_lip
    linarith
  have h_cont_corr_at_0 : ContinuousAt
      (fun a => IsingModel.correlation G (⟨a, 0, β⟩ : IsingParams ℝ) {r, s}) 0 :=
    (IsingModel.correlation_continuous_J G 0 β {r, s}).continuousAt
  have h_corr_at_0 : IsingModel.correlation G (⟨0, 0, β⟩ : IsingParams ℝ) {r, s} = 0 :=
    IsingModel.correlation_zero_params_vanish_of_nonempty_A G β {r, s}
      (Finset.insert_nonempty _ _)
  have h_neBot : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  have h_g_tendsto : Filter.Tendsto
      (fun a => IsingModel.correlation G (⟨a, 0, β⟩ : IsingParams ℝ) {r, s} + C * (J - a))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (C * J)) := by
    have h1 : Filter.Tendsto
        (fun a => IsingModel.correlation G (⟨a, 0, β⟩ : IsingParams ℝ) {r, s})
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have htend := h_cont_corr_at_0.tendsto
      rw [h_corr_at_0] at htend
      exact htend.mono_left nhdsWithin_le_nhds
    have h2 : Filter.Tendsto
        (fun a : ℝ => C * (J - a)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (C * J)) := by
      have hf : Continuous fun a : ℝ => C * (J - a) := by
        exact Continuous.mul continuous_const (Continuous.sub continuous_const continuous_id)
      have hcont : Filter.Tendsto (fun a : ℝ => C * (J - a)) (nhds 0) (nhds (C * (J - 0))) :=
        hf.continuousAt (x := (0 : ℝ))
      have heq : C * (J - 0) = C * J := by ring
      rw [heq] at hcont
      exact hcont.mono_left nhdsWithin_le_nhds
    have hsum := h1.add h2
    simpa using hsum
  have h_eventual : ∀ᶠ a in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} ≤
      IsingModel.correlation G (⟨a, 0, β⟩ : IsingParams ℝ) {r, s} + C * (J - a) := by
    have h_le : ∀ᶠ a in nhdsWithin (0 : ℝ) (Set.Ioi 0), a ≤ J := by
      have h_nhd : Set.Iic J ∈ nhds (0 : ℝ) := Iic_mem_nhds hJ_pos
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds h_nhd] with a ha hab
      exact hab
    filter_upwards [self_mem_nhdsWithin, h_le] with a ha hab
    exact h_per_a a ha hab
  exact ge_of_tendsto h_g_tendsto h_eventual

/-- **Linear bound on corr_∞ at J = 0** (Step 230):
For `0 < β`, `0 < b` with `bβ·2d < 1`, and any `r ≠ s`, on the interval `(0, b]`:
`corr_∞(r, s, J) ≤ (β·M(b)² + β·4d) · J`,
where `M(b) = bβ·2d/(1 - bβ·2d)`.

Direct J-direction analogue of Step 176. As an immediate corollary,
`corr_∞(r, s, J) → 0` as `J → 0⁺` (right-continuity at 0). -/
theorem correlationInfinite_le_const_mul_J_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * β * ↑(2 * d) < 1)
    (J : ℝ) (hJ_pos : 0 < J) (hJb : J ≤ b) :
    let M : ℝ := b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d))
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      {r_val, s_val} ≤ (β * M ^ 2 + β * (4 * ↑d)) * J := by
  intro M
  set C : ℝ := β * M ^ 2 + β * (4 * ↑d) with hC_def
  have hferro : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
    ⟨hJ_pos.le, le_refl 0, hβ⟩
  rw [correlationInfinite_eq_ciSup]
  apply ciSup_le
  intro n
  by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
  · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
    have hsn : s_val ∈ Λ.volume n :=
      Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
    have heq : correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n =
               IsingModel.correlation
                  (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, β⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                ⟨s_val, hsn⟩} := by
      rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
      congr 1
      ext u; rw [mem_liftFinset]
      simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
    rw [heq]
    have hsubsne : (⟨r_val, hrn⟩ : ↑(Λ.volume n)) ≠ ⟨s_val, hsn⟩ :=
      fun h => hrs (congrArg Subtype.val h)
    exact inducedLatticeGraph_correlation_le_const_mul_J Λ β hβ b hlt n
      ⟨r_val, hrn⟩ ⟨s_val, hsn⟩ hsubsne J hJ_pos hJb
  · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
    have hC_nn : 0 ≤ C := by
      have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
      have hM_nn : 0 ≤ M :=
        div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hβ.le) (Nat.cast_nonneg _)) hdenom_b.le
      exact add_nonneg (mul_nonneg hβ.le (pow_nonneg hM_nn 2))
                       (mul_nonneg hβ.le (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
    exact mul_nonneg hC_nn hJ_pos.le

/-- **Helper: corr_∞ vanishes at β = 0 for r ≠ s** (Step 177 helper):
The infinite-volume two-point function at β = 0, h = 0 is zero (since the Boltzmann
weight is constant and the spin product over a non-empty set averages to zero). -/
private lemma correlationInfinite_eq_zero_at_beta_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (J : ℝ) :
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
      {r_val, s_val} = 0 := by
  rw [correlationInfinite_eq_ciSup]
  apply le_antisymm
  · apply ciSup_le
    intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      have heq : correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, 0⟩ : IsingParams ℝ) {r_val, s_val} n =
                 IsingModel.correlation
                    (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                    (⟨J, 0, 0⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                  ⟨s_val, hsn⟩} := by
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
      rw [heq]
      rw [IsingModel.correlation_beta_zero_vanish_of_nonempty_A _ J 0 _
            (Finset.insert_nonempty _ _)]
    · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
  · apply le_ciSup_of_le _ 0
    · by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume 0
      · have hrn : r_val ∈ Λ.volume 0 := Finset.insert_subset_iff.mp h_sub |>.1
        have hsn : s_val ∈ Λ.volume 0 :=
          Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
        have heq : correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                      (⟨J, 0, 0⟩ : IsingParams ℝ) {r_val, s_val} 0 =
                   IsingModel.correlation
                      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume 0))
                      (⟨J, 0, 0⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume 0)),
                                                    ⟨s_val, hsn⟩} := by
          rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
          congr 1
          ext u; rw [mem_liftFinset]
          simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
        rw [heq]
        rw [IsingModel.correlation_beta_zero_vanish_of_nonempty_A _ J 0 _
              (Finset.insert_nonempty _ _)]
      · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
    · exact ⟨1, fun y hy => by
        obtain ⟨n, rfl⟩ := hy
        exact correlationAlongExhaustion_le_one (IsingModel.latticeGraph d) Λ _ _ _⟩

/-- **ContinuousOn of corr_∞ on closed interval [0, b]** (Step 177):
For `1 ≤ d`, `0 < J`, `0 < b`, `bJ·2d < 1`: `β ↦ corr_∞(r, s, β)` is continuous on `[0, b]`,
extending Step 169 to include β = 0.

Proof: For β > 0 use Step 175 ContinuousAt. For β = 0, use Step 176 squeeze
`0 ≤ corr_∞(β) ≤ C·β` for β ∈ (0, b]. -/
theorem correlationInfinite_continuousOn_beta_of_high_temp_zero_closed
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * J * ↑(2 * d) < 1) :
    ContinuousOn
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc 0 b) := by
  have h2d_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
    exact_mod_cast this
  have hJ2d_pos : 0 < J * ↑(2 * d) := mul_pos hJ_pos h2d_pos
  have hb_lt_βc : b < 1 / (J * ↑(2 * d)) := by
    rw [lt_div_iff₀ hJ2d_pos]; linarith
  intro β hβ
  rcases eq_or_lt_of_le hβ.1 with hβ0 | hβ_pos
  · -- β = 0: right-continuity from Step 176 squeeze
    subst hβ0
    set M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d)) with hM_def
    set C : ℝ := J * M ^ 2 + J * (4 * ↑d) with hC_def
    have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
    have hM_nn : 0 ≤ M :=
      div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hJ_pos.le) (Nat.cast_nonneg _)) hdenom_b.le
    have hC_nn : 0 ≤ C :=
      add_nonneg (mul_nonneg hJ_pos.le (pow_nonneg hM_nn 2))
                 (mul_nonneg hJ_pos.le (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
    have h_corr_at_zero : correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) {r_val, s_val} = 0 :=
      correlationInfinite_eq_zero_at_beta_zero Λ r_val s_val J
    rw [ContinuousWithinAt]
    show Filter.Tendsto _ _ (nhds _)
    rw [h_corr_at_zero]
    -- Need: Tendsto (fun β => corr_∞(β)) (𝓝[Icc 0 b] 0) (𝓝 0)
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    refine ⟨ε / (C + 1), div_pos hε (by linarith), ?_⟩
    intro x hx_in hx_dist
    have hx_nn : 0 ≤ x := hx_in.1
    have hx_le_b : x ≤ b := hx_in.2
    have hcorr_x_nn : 0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, x⟩ : IsingParams ℝ) {r_val, s_val} := by
      rcases eq_or_lt_of_le hx_nn with hx0 | hx_pos
      · rw [← hx0, correlationInfinite_eq_zero_at_beta_zero]
      · exact correlationInfinite_nonneg _ _ _ ⟨hJ_pos.le, le_refl 0, hx_pos⟩ _
    have hcorr_x_le_Cx : correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, x⟩ : IsingParams ℝ) {r_val, s_val} ≤ C * x := by
      rcases eq_or_lt_of_le hx_nn with hx0 | hx_pos
      · rw [← hx0, correlationInfinite_eq_zero_at_beta_zero, mul_zero]
      · have hbound := correlationInfinite_le_const_mul_beta_of_high_temp
          Λ r_val s_val hrs J hJ_pos.le b hb_pos hlt x hx_pos hx_le_b
        have heq_M : M = b * J * (2 * ↑d) / (1 - b * J * (2 * ↑d)) := by
          rw [hM_def]; push_cast; ring
        have heq_C : C = J * (b * J * (2 * ↑d) / (1 - b * J * (2 * ↑d))) ^ 2 + J * (4 * ↑d) := by
          rw [hC_def, heq_M]
        rw [heq_C]
        simpa using hbound
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hcorr_x_nn]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hx_nn] at hx_dist
    calc correlationInfinite _ _ _ _ ≤ C * x := hcorr_x_le_Cx
      _ ≤ (C + 1) * x := by nlinarith
      _ < (C + 1) * (ε / (C + 1)) := by
        apply (mul_lt_mul_iff_of_pos_left (by linarith)).mpr hx_dist
      _ = ε := by field_simp
  · -- β > 0: from Step 175
    have hβ_lt_βc : β < 1 / (J * ↑(2 * d)) := lt_of_le_of_lt hβ.2 hb_lt_βc
    have hβ_in_open : β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) := ⟨hβ_pos, hβ_lt_βc⟩
    exact (correlationInfinite_continuousAt_beta_of_high_temp
      hd Λ r_val s_val hrs J hJ_pos β hβ_in_open).continuousWithinAt

/-- **Helper: corr_∞ vanishes at J = 0 for r ≠ s** (Step 231 helper):
At J = h = 0 (any β), every Boltzmann weight = exp(0) = 1, so the correlation
sum reduces to the spin-product sum which vanishes for nonempty A. Hence
each `corr_n(J=0) = 0` and `corr_∞(J=0) = ⨆_n 0 = 0`. -/
private lemma correlationInfinite_eq_zero_at_J_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (β : ℝ) :
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      {r_val, s_val} = 0 := by
  rw [correlationInfinite_eq_ciSup]
  apply le_antisymm
  · apply ciSup_le
    intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      have heq : correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨0, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n =
                 IsingModel.correlation
                    (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                    (⟨0, 0, β⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                  ⟨s_val, hsn⟩} := by
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
      rw [heq]
      rw [IsingModel.correlation_zero_params_vanish_of_nonempty_A _ β _
            (Finset.insert_nonempty _ _)]
    · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
  · apply le_ciSup_of_le _ 0
    · by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume 0
      · have hrn : r_val ∈ Λ.volume 0 := Finset.insert_subset_iff.mp h_sub |>.1
        have hsn : s_val ∈ Λ.volume 0 :=
          Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
        have heq : correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                      (⟨0, 0, β⟩ : IsingParams ℝ) {r_val, s_val} 0 =
                   IsingModel.correlation
                      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume 0))
                      (⟨0, 0, β⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume 0)),
                                                    ⟨s_val, hsn⟩} := by
          rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
          congr 1
          ext u; rw [mem_liftFinset]
          simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
        rw [heq]
        rw [IsingModel.correlation_zero_params_vanish_of_nonempty_A _ β _
              (Finset.insert_nonempty _ _)]
      · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
    · -- BddAbove of range
      by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume 0
      · exact ⟨1, fun y hy => by
          obtain ⟨n, rfl⟩ := hy
          exact correlationAlongExhaustion_le_one (IsingModel.latticeGraph d) Λ _ _ _⟩
      · exact ⟨1, fun y hy => by
          obtain ⟨n, rfl⟩ := hy
          exact correlationAlongExhaustion_le_one (IsingModel.latticeGraph d) Λ _ _ _⟩

/-- **ContinuousOn of corr_∞ on closed interval [0, b] in J** (Step 231):
For `0 < β`, `0 < b`, `bβ·2d < 1`: `J ↦ corr_∞(r, s, J)` is continuous on `[0, b]`,
extending Step 223 to include J = 0.

Direct J-direction analogue of Step 177. Proof: For J > 0 use Step 229 ContinuousAt.
For J = 0, use Step 230 squeeze `0 ≤ corr_∞(J) ≤ C·J` for J ∈ (0, b]. -/
theorem correlationInfinite_continuousOn_J_of_high_temp_zero_closed
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * β * ↑(2 * d) < 1) :
    ContinuousOn
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc 0 b) := by
  have h2d_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
    exact_mod_cast this
  have hβ2d_pos : 0 < β * ↑(2 * d) := mul_pos hβ_pos h2d_pos
  have hb_lt_Jc : b < 1 / (β * ↑(2 * d)) := by
    rw [lt_div_iff₀ hβ2d_pos]; linarith
  intro J hJ
  rcases eq_or_lt_of_le hJ.1 with hJ0 | hJ_pos
  · subst hJ0
    set M : ℝ := b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d)) with hM_def
    set C : ℝ := β * M ^ 2 + β * (4 * ↑d) with hC_def
    have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
    have hM_nn : 0 ≤ M :=
      div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hβ_pos.le) (Nat.cast_nonneg _)) hdenom_b.le
    have hC_nn : 0 ≤ C :=
      add_nonneg (mul_nonneg hβ_pos.le (pow_nonneg hM_nn 2))
                 (mul_nonneg hβ_pos.le (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
    have h_corr_at_zero : correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) {r_val, s_val} = 0 :=
      correlationInfinite_eq_zero_at_J_zero Λ r_val s_val β
    rw [ContinuousWithinAt]
    show Filter.Tendsto _ _ (nhds _)
    rw [h_corr_at_zero]
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    refine ⟨ε / (C + 1), div_pos hε (by linarith), ?_⟩
    intro x hx_in hx_dist
    have hx_nn : 0 ≤ x := hx_in.1
    have hx_le_b : x ≤ b := hx_in.2
    have hcorr_x_nn : 0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨x, 0, β⟩ : IsingParams ℝ) {r_val, s_val} := by
      rcases eq_or_lt_of_le hx_nn with hx0 | hx_pos
      · rw [← hx0, correlationInfinite_eq_zero_at_J_zero]
      · exact correlationInfinite_nonneg _ _ _ ⟨hx_pos.le, le_refl 0, hβ_pos⟩ _
    have hcorr_x_le_Cx : correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨x, 0, β⟩ : IsingParams ℝ) {r_val, s_val} ≤ C * x := by
      rcases eq_or_lt_of_le hx_nn with hx0 | hx_pos
      · rw [← hx0, correlationInfinite_eq_zero_at_J_zero, mul_zero]
      · have hbound := correlationInfinite_le_const_mul_J_of_high_temp
          Λ r_val s_val hrs β hβ_pos b hb_pos hlt x hx_pos hx_le_b
        have heq_M : M = b * β * (2 * ↑d) / (1 - b * β * (2 * ↑d)) := by
          rw [hM_def]; push_cast; ring
        have heq_C : C = β * (b * β * (2 * ↑d) / (1 - b * β * (2 * ↑d))) ^ 2 + β * (4 * ↑d) := by
          rw [hC_def, heq_M]
        rw [heq_C]
        simpa using hbound
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hcorr_x_nn]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hx_nn] at hx_dist
    calc correlationInfinite _ _ _ _ ≤ C * x := hcorr_x_le_Cx
      _ ≤ (C + 1) * x := by nlinarith
      _ < (C + 1) * (ε / (C + 1)) := by
        apply (mul_lt_mul_iff_of_pos_left (by linarith)).mpr hx_dist
      _ = ε := by field_simp
  · have hJ_lt_Jc : J < 1 / (β * ↑(2 * d)) := lt_of_le_of_lt hJ.2 hb_lt_Jc
    have hJ_in_open : J ∈ Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d))) := ⟨hJ_pos, hJ_lt_Jc⟩
    exact (correlationInfinite_continuousAt_J_of_high_temp
      hd Λ r_val s_val hrs β hβ_pos J hJ_in_open).continuousWithinAt

/-- **Helper: corr_n vanishes at β = 0** (Step 178 helper):
At β = 0, the finite-volume correlation along exhaustion is zero. -/
private lemma correlationAlongExhaustion_eq_zero_at_beta_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (J : ℝ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
      (⟨J, 0, 0⟩ : IsingParams ℝ) {r_val, s_val} n = 0 := by
  by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
  · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
    have hsn : s_val ∈ Λ.volume n :=
      Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
    have heq : correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, 0⟩ : IsingParams ℝ) {r_val, s_val} n =
               IsingModel.correlation
                  (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, 0⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                ⟨s_val, hsn⟩} := by
      rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
      congr 1
      ext u; rw [mem_liftFinset]
      simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
    rw [heq]
    exact IsingModel.correlation_beta_zero_vanish_of_nonempty_A _ J 0 _
      (Finset.insert_nonempty _ _)
  · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]

/-- **TendstoUniformlyOn corr_n → corr_∞ on closed interval [0, b]** (Step 178):
Strengthens Step 170 to include β = 0.

Proof: Apply Dini's theorem (`Monotone.tendstoUniformlyOn_of_forall_tendsto`) on the
compact interval `[0, b]` using continuity of each corr_n, monotonicity in n
(at β = 0 it's trivial since both sides are 0), continuity of corr_∞ (Step 177),
and pointwise convergence. -/
theorem correlationAlongExhaustion_tendstoUniformlyOn_beta_zero_closed
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * J * ↑(2 * d) < 1) :
    TendstoUniformlyOn
      (fun n β => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n)
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      Filter.atTop (Set.Icc 0 b) := by
  apply Monotone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc
  · -- (1) ContinuousOn of each corr_n on [0, b]
    intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      intro β _
      apply ContinuousAt.continuousWithinAt
      have heq : (fun β' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {r_val, s_val} n) =
                 (fun β' => IsingModel.correlation
                    (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                    ⟨s_val, hsn⟩}) := by
        funext β'
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
      rw [heq]
      exact IsingModel.correlation_continuousAt_beta _ J β _
    · simp only [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      exact continuousOn_const
  · -- (2) Monotone in n for each β ∈ [0, b]
    intro β hβ
    rcases eq_or_lt_of_le hβ.1 with hβ0 | hβ_pos
    · -- β = 0: corr_n(0) = 0 for all n, monotone trivially
      subst hβ0
      intro n m _
      simp only [correlationAlongExhaustion_eq_zero_at_beta_zero, le_refl]
    · -- β > 0: use the standard monotone theorem
      exact correlationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ⟨hJ_pos.le, le_refl 0, hβ_pos⟩ {r_val, s_val}
  · -- (3) Continuity of corr_∞ on [0, b] (Step 177)
    exact correlationInfinite_continuousOn_beta_of_high_temp_zero_closed
      hd Λ r_val s_val hrs J hJ_pos b hb_pos hlt
  · -- (4) Pointwise convergence at each β ∈ [0, b]
    intro β hβ
    rcases eq_or_lt_of_le hβ.1 with hβ0 | hβ_pos
    · -- β = 0: both corr_n(0) and corr_∞(0) are 0
      subst hβ0
      simp only [correlationAlongExhaustion_eq_zero_at_beta_zero,
                 correlationInfinite_eq_zero_at_beta_zero]
      exact tendsto_const_nhds
    · -- β > 0: use correlationAlongExhaustion_tendsto_ciSup
      have hf : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
        ⟨hJ_pos.le, le_refl 0, hβ_pos⟩
      have htend := IsingModel.Ambient.correlationAlongExhaustion_tendsto_ciSup
        (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf {r_val, s_val}
      rw [correlationInfinite_eq_ciSup]
      exact htend

/-- **Helper: corr_n vanishes at J = 0** (Step 232 helper):
At J = h = 0 (any β), the finite-volume correlation along exhaustion is zero. -/
private lemma correlationAlongExhaustion_eq_zero_at_J_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (β : ℝ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
      (⟨0, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n = 0 := by
  by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
  · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
    have hsn : s_val ∈ Λ.volume n :=
      Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
    have heq : correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨0, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n =
               IsingModel.correlation
                  (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨0, 0, β⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                ⟨s_val, hsn⟩} := by
      rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
      congr 1
      ext u; rw [mem_liftFinset]
      simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
    rw [heq]
    exact IsingModel.correlation_zero_params_vanish_of_nonempty_A _ β _
      (Finset.insert_nonempty _ _)
  · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]

/-- **TendstoUniformlyOn corr_n → corr_∞ on closed [0, b] in J including J = 0** (Step 232):
For `0 < β`, `0 < b`, `bβ·2d < 1`: corr_n → corr_∞ uniformly on `[0, b]` in J at h = 0.

Direct J-direction analogue of Step 178. Strengthens Step 224 to include J = 0.
Proof: Dini's theorem (`Monotone.tendstoUniformlyOn_of_forall_tendsto`) on the compact
[0, b] with: (1) ContinuousOn each corr_n; (2) Monotonicity in n at J = 0 trivial,
at J > 0 from `correlationAlongExhaustion_monotone`; (3) ContinuousOn corr_∞ from
Step 231; (4) pointwise convergence at J = 0 trivial, at J > 0 from
`correlationAlongExhaustion_tendsto_ciSup`. -/
theorem correlationAlongExhaustion_tendstoUniformlyOn_J_zero_closed
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * β * ↑(2 * d) < 1) :
    TendstoUniformlyOn
      (fun n J => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n)
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      Filter.atTop (Set.Icc 0 b) := by
  apply Monotone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc
  · intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      intro J _
      apply ContinuousAt.continuousWithinAt
      have heq : (fun J' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J', 0, β⟩ : IsingParams ℝ) {r_val, s_val} n) =
                 (fun J' => IsingModel.correlation
                    (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                    (⟨J', 0, β⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                    ⟨s_val, hsn⟩}) := by
        funext J'
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
      rw [heq]
      exact (IsingModel.correlation_continuous_J _ 0 β _).continuousAt
    · simp only [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      exact continuousOn_const
  · intro J hJ
    rcases eq_or_lt_of_le hJ.1 with hJ0 | hJ_pos
    · subst hJ0
      intro n m _
      simp only [correlationAlongExhaustion_eq_zero_at_J_zero, le_refl]
    · exact correlationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ⟨hJ_pos.le, le_refl 0, hβ_pos⟩ {r_val, s_val}
  · exact correlationInfinite_continuousOn_J_of_high_temp_zero_closed
      hd Λ r_val s_val hrs β hβ_pos b hb_pos hlt
  · intro J hJ
    rcases eq_or_lt_of_le hJ.1 with hJ0 | hJ_pos
    · subst hJ0
      simp only [correlationAlongExhaustion_eq_zero_at_J_zero,
                 correlationInfinite_eq_zero_at_J_zero]
      exact tendsto_const_nhds
    · have hf : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
        ⟨hJ_pos.le, le_refl 0, hβ_pos⟩
      have htend := IsingModel.Ambient.correlationAlongExhaustion_tendsto_ciSup
        (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf {r_val, s_val}
      rw [correlationInfinite_eq_ciSup]
      exact htend

/-- **MonotoneOn corr_∞ in β on closed interval [0, b]** (Step 179 helper):
The infinite-volume two-point function is monotone non-decreasing in β on `[0, b]`.

Proof: at β > 0 use `correlationInfinite_monotone_beta` (MonotoneOn `Ioi 0`);
at β = 0, corr_∞(0) = 0 ≤ corr_∞(β₂) by `correlationInfinite_nonneg`. -/
theorem correlationInfinite_monotoneOn_beta_zero_closed
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (J : ℝ) (hJ : 0 ≤ J) (b : ℝ) :
    MonotoneOn
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc 0 b) := by
  intro β₁ hβ₁ β₂ hβ₂ hβ
  -- Reduce lambda to be able to rewrite
  simp only
  rcases eq_or_lt_of_le hβ₁.1 with hβ₁0 | hβ₁_pos
  · -- β₁ = 0: corr_∞(0) = 0 ≤ corr_∞(β₂)
    rw [← hβ₁0, correlationInfinite_eq_zero_at_beta_zero]
    rcases eq_or_lt_of_le (hβ₁0.le.trans hβ) with hβ₂0 | hβ₂_pos
    · rw [← hβ₂0, correlationInfinite_eq_zero_at_beta_zero]
    · exact correlationInfinite_nonneg _ _ _ ⟨hJ, le_refl 0, hβ₂_pos⟩ _
  · -- β₁ > 0: use existing MonotoneOn on Ioi 0
    have hβ₁_in : β₁ ∈ Set.Ioi (0 : ℝ) := hβ₁_pos
    have hβ₂_in : β₂ ∈ Set.Ioi (0 : ℝ) := hβ₁_pos.trans_le hβ
    exact correlationInfinite_monotone_beta (IsingModel.latticeGraph d) Λ hJ (le_refl 0) _
      hβ₁_in hβ₂_in hβ

/-- **A.e. differentiability of corr_∞ on closed [0, b]** (Step 179):
For ferromagnetic h = 0, β ∈ [0, b]: `β ↦ corr_∞(β)` is differentiable within `[0, b]` at
Lebesgue-a.e. β.

Proof: corr_∞ is monotone on `[0, b]` (helper above), hence locally bounded variation
(`MonotoneOn.locallyBoundedVariationOn`), hence a.e. differentiable
(`LocallyBoundedVariationOn.ae_differentiableWithinAt`). Strengthens Step 171
from `[a, b]` (a > 0) to closed `[0, b]`. -/
theorem correlationInfinite_ae_differentiableWithinAt_beta_zero_closed
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (J : ℝ) (hJ : 0 ≤ J) (b : ℝ) :
    ∀ᵐ β ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 b),
    DifferentiableWithinAt ℝ
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc 0 b) β := by
  have hmono := correlationInfinite_monotoneOn_beta_zero_closed Λ r_val s_val J hJ b
  exact hmono.locallyBoundedVariationOn.ae_differentiableWithinAt measurableSet_Icc

/-- **MonotoneOn corr_∞ in J on closed interval [0, b]** (Step 233 helper):
For `0 < β`: `J ↦ corr_∞(r, s, J)` is monotone non-decreasing on `[0, b]`.

Direct J-direction analogue of `correlationInfinite_monotoneOn_beta_zero_closed`.
Proof: at J > 0 use `correlationInfinite_monotone_J` (MonotoneOn `Ici 0`);
at J = 0, corr_∞(0) = 0 ≤ corr_∞(J₂) by `correlationInfinite_nonneg`. -/
theorem correlationInfinite_monotoneOn_J_zero_closed
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (β : ℝ) (hβ : 0 < β) (b : ℝ) :
    MonotoneOn
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc 0 b) := by
  intro J₁ hJ₁ J₂ hJ₂ hJ_le
  simp only
  rcases eq_or_lt_of_le hJ₁.1 with hJ₁0 | hJ₁_pos
  · rw [← hJ₁0, correlationInfinite_eq_zero_at_J_zero]
    rcases eq_or_lt_of_le (hJ₁0.le.trans hJ_le) with hJ₂0 | hJ₂_pos
    · rw [← hJ₂0, correlationInfinite_eq_zero_at_J_zero]
    · exact correlationInfinite_nonneg _ _ _ ⟨hJ₂_pos.le, le_refl 0, hβ⟩ _
  · have hJ₁_in : J₁ ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hJ₁_pos.le
    have hJ₂_in : J₂ ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (hJ₁_pos.le.trans hJ_le)
    have hmono := correlationInfinite_monotone_J (IsingModel.latticeGraph d) Λ
      (le_refl 0) hβ {r_val, s_val} hJ₁_in hJ₂_in hJ_le
    exact hmono

/-- **A.e. differentiability of corr_∞ in J on closed [0, b]** (Step 233):
For `0 < β`, `b ∈ ℝ`: `J ↦ corr_∞(J)` is differentiable within `[0, b]` at Lebesgue-a.e. J.

Direct J-direction analogue of Step 179. Proof: corr_∞ is monotone on `[0, b]`
(helper above), hence locally bounded variation, hence a.e. differentiable. -/
theorem correlationInfinite_ae_differentiableWithinAt_J_zero_closed
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (β : ℝ) (hβ : 0 < β) (b : ℝ) :
    ∀ᵐ J ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 b),
    DifferentiableWithinAt ℝ
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc 0 b) J := by
  have hmono := correlationInfinite_monotoneOn_J_zero_closed Λ r_val s_val β hβ b
  exact hmono.locallyBoundedVariationOn.ae_differentiableWithinAt measurableSet_Icc

/-- **Helper for Step 180**: ordered Lipschitz bound on [0, b] (closed including β = 0).
For `0 ≤ β₁ ≤ β₂` with `β₂ ≤ b` and `bJ·2d < 1`:
`corr_∞(β₂) - corr_∞(β₁) ≤ C · (β₂ - β₁)` where `C = J·M² + J·4d`. -/
private lemma correlationInfinite_diff_le_const_mul_diff
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * J * ↑(2 * d) < 1)
    (β₁ β₂ : ℝ) (hβ₁_nn : 0 ≤ β₁) (hβ : β₁ ≤ β₂) (hβ₂_le_b : β₂ ≤ b) :
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      {r_val, s_val} -
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β₁⟩ : IsingParams ℝ)
      {r_val, s_val} ≤
    (J * (b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))) ^ 2 + J * (4 * ↑d)) *
      (β₂ - β₁) := by
  rcases eq_or_lt_of_le hβ₁_nn with hβ₁0 | hβ₁_pos
  · -- β₁ = 0
    rw [← hβ₁0, correlationInfinite_eq_zero_at_beta_zero, sub_zero, sub_zero]
    rcases eq_or_lt_of_le (hβ₁0.le.trans hβ) with hβ₂0 | hβ₂_pos
    · rw [← hβ₂0, correlationInfinite_eq_zero_at_beta_zero]
      have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
      have hM_nn : 0 ≤ b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d)) :=
        div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hJ) (Nat.cast_nonneg _)) hdenom_b.le
      positivity
    · -- β₂ > 0: use Step 176
      have hbound := correlationInfinite_le_const_mul_beta_of_high_temp
        Λ r_val s_val hrs J hJ b hb_pos hlt β₂ hβ₂_pos hβ₂_le_b
      -- hbound has let M = b*J*↑(2*d)/(1-b*J*↑(2*d)), so we directly get the bound
      simpa using hbound
  · -- β₁ > 0: use Step 168 (LipschitzOnWith on [β₁, b])
    -- Step 168's `let M` wrapper requires explicit type ascription below
    have hlip_let := correlationInfinite_lipschitzOnWith_beta_of_high_temp
      Λ r_val s_val hrs J hJ β₁ b hβ₁_pos (hβ.trans hβ₂_le_b) hlt
    -- Extract the underlying LipschitzOnWith (the `let M :=` is just notation)
    have hlip : LipschitzOnWith
        ⟨J * (b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))) ^ 2 + J * (4 * ↑d), by
          have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
          have hM_nn : 0 ≤ b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d)) :=
            div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hJ)
                         (Nat.cast_nonneg _)) hdenom_b.le
          positivity⟩
        (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val})
        (Set.Icc β₁ b) := hlip_let
    have hβ₁_in : β₁ ∈ Set.Icc β₁ b := Set.mem_Icc.mpr ⟨le_refl _, hβ.trans hβ₂_le_b⟩
    have hβ₂_in : β₂ ∈ Set.Icc β₁ b := Set.mem_Icc.mpr ⟨hβ, hβ₂_le_b⟩
    have hdist := hlip.dist_le_mul β₁ hβ₁_in β₂ hβ₂_in
    have hcorr_nn :
        0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) {r_val, s_val} -
            correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β₁⟩ : IsingParams ℝ) {r_val, s_val} := by
      have hmono := correlationInfinite_monotoneOn_beta_zero_closed Λ r_val s_val J hJ b
      have h1 : β₁ ∈ Set.Icc (0 : ℝ) b := Set.mem_Icc.mpr ⟨hβ₁_pos.le, hβ.trans hβ₂_le_b⟩
      have h2 : β₂ ∈ Set.Icc (0 : ℝ) b := Set.mem_Icc.mpr ⟨hβ₁_pos.le.trans hβ, hβ₂_le_b⟩
      linarith [hmono h1 h2 hβ]
    have hβ_nn : 0 ≤ β₂ - β₁ := by linarith
    simp only [Real.dist_eq] at hdist
    rw [abs_sub_comm β₁ β₂, abs_of_nonneg hβ_nn,
        abs_sub_comm
          (correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β₁⟩ : IsingParams ℝ) {r_val, s_val})
          (correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) {r_val, s_val}),
        abs_of_nonneg hcorr_nn] at hdist
    push_cast at hdist
    -- Convert ↑(2*d) ↔ 2 * ↑d for matching
    convert hdist using 2
    push_cast; ring

/-- **LipschitzOnWith of corr_∞ on closed [0, b] (including β = 0)** (Step 180):
For `0 ≤ J`, `0 < b`, `bJ·2d < 1`: `β ↦ corr_∞(β)` is `C`-Lipschitz on `[0, b]`
with the same constant `C = J·M² + J·4d` as Step 168.

Strengthens Step 168 from `[a, b]` (a > 0) to closed `[0, b]`. -/
theorem correlationInfinite_lipschitzOnWith_beta_zero_closed
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * J * ↑(2 * d) < 1) :
    LipschitzOnWith ⟨J * (b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))) ^ 2 + J * (4 * ↑d), by
        have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
        have hM_nn : 0 ≤ b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d)) :=
          div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hJ)
                       (Nat.cast_nonneg _)) hdenom_b.le
        have := hM_nn
        positivity⟩
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc 0 b) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro β₁ hβ₁ β₂ hβ₂
  -- Generic argument: the bound depends on min/max of β₁, β₂
  rcases le_total β₁ β₂ with hβ | hβ
  · -- β₁ ≤ β₂: |f β₁ - f β₂| ≤ K * |β₁ - β₂|
    have hcorr_nn :
        0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) {r_val, s_val} -
            correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β₁⟩ : IsingParams ℝ) {r_val, s_val} := by
      have hmono := correlationInfinite_monotoneOn_beta_zero_closed Λ r_val s_val J hJ b
      linarith [hmono hβ₁ hβ₂ hβ]
    have hβ_nn : 0 ≤ β₂ - β₁ := by linarith
    rw [Real.dist_eq, Real.dist_eq, abs_sub_comm β₁ β₂,
        abs_sub_comm
          ((fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) β₁)
          ((fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) β₂),
        abs_of_nonneg hcorr_nn, abs_of_nonneg hβ_nn]
    have hbound := correlationInfinite_diff_le_const_mul_diff Λ r_val s_val hrs J hJ b hb_pos hlt
      β₁ β₂ hβ₁.1 hβ hβ₂.2
    push_cast
    push_cast at hbound
    exact hbound
  · -- β₂ ≤ β₁: similar with roles swapped
    have hcorr_nn :
        0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β₁⟩ : IsingParams ℝ) {r_val, s_val} -
            correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) {r_val, s_val} := by
      have hmono := correlationInfinite_monotoneOn_beta_zero_closed Λ r_val s_val J hJ b
      linarith [hmono hβ₂ hβ₁ hβ]
    have hβ_nn : 0 ≤ β₁ - β₂ := by linarith
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg hcorr_nn, abs_of_nonneg hβ_nn]
    have hbound := correlationInfinite_diff_le_const_mul_diff Λ r_val s_val hrs J hJ b hb_pos hlt
      β₂ β₁ hβ₂.1 hβ hβ₁.2
    push_cast
    push_cast at hbound
    exact hbound

/-- **Helper for Step 234**: ordered Lipschitz bound on [0, b] in J (closed including J = 0).
For `0 ≤ J₁ ≤ J₂` with `J₂ ≤ b`, `0 < β`, `bβ·2d < 1`:
`corr_∞(J₂) - corr_∞(J₁) ≤ C · (J₂ - J₁)` where `C = β·M² + β·4d`. -/
private lemma correlationInfinite_diff_le_const_mul_diff_J
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * β * ↑(2 * d) < 1)
    (J₁ J₂ : ℝ) (hJ₁_nn : 0 ≤ J₁) (hJ : J₁ ≤ J₂) (hJ₂_le_b : J₂ ≤ b) :
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J₂, 0, β⟩ : IsingParams ℝ)
      {r_val, s_val} -
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J₁, 0, β⟩ : IsingParams ℝ)
      {r_val, s_val} ≤
    (β * (b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d))) ^ 2 + β * (4 * ↑d)) *
      (J₂ - J₁) := by
  rcases eq_or_lt_of_le hJ₁_nn with hJ₁0 | hJ₁_pos
  · rw [← hJ₁0, correlationInfinite_eq_zero_at_J_zero, sub_zero, sub_zero]
    rcases eq_or_lt_of_le (hJ₁0.le.trans hJ) with hJ₂0 | hJ₂_pos
    · rw [← hJ₂0, correlationInfinite_eq_zero_at_J_zero]
      have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
      have hM_nn : 0 ≤ b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d)) :=
        div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hβ.le) (Nat.cast_nonneg _)) hdenom_b.le
      positivity
    · have hbound := correlationInfinite_le_const_mul_J_of_high_temp
        Λ r_val s_val hrs β hβ b hb_pos hlt J₂ hJ₂_pos hJ₂_le_b
      simpa using hbound
  · have hlip_let := correlationInfinite_lipschitzOnWith_J_of_high_temp
      Λ r_val s_val hrs β hβ J₁ b hJ₁_pos (hJ.trans hJ₂_le_b) hlt
    have hlip : LipschitzOnWith
        ⟨β * (b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d))) ^ 2 + β * (4 * ↑d), by
          have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
          have hM_nn : 0 ≤ b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d)) :=
            div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hβ.le)
                         (Nat.cast_nonneg _)) hdenom_b.le
          positivity⟩
        (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val})
        (Set.Icc J₁ b) := hlip_let
    have hJ₁_in : J₁ ∈ Set.Icc J₁ b := Set.mem_Icc.mpr ⟨le_refl _, hJ.trans hJ₂_le_b⟩
    have hJ₂_in : J₂ ∈ Set.Icc J₁ b := Set.mem_Icc.mpr ⟨hJ, hJ₂_le_b⟩
    have hdist := hlip.dist_le_mul J₁ hJ₁_in J₂ hJ₂_in
    have hcorr_nn :
        0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J₂, 0, β⟩ : IsingParams ℝ) {r_val, s_val} -
            correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J₁, 0, β⟩ : IsingParams ℝ) {r_val, s_val} := by
      have hmono := correlationInfinite_monotoneOn_J_zero_closed Λ r_val s_val β hβ b
      have h1 : J₁ ∈ Set.Icc (0 : ℝ) b := Set.mem_Icc.mpr ⟨hJ₁_pos.le, hJ.trans hJ₂_le_b⟩
      have h2 : J₂ ∈ Set.Icc (0 : ℝ) b := Set.mem_Icc.mpr ⟨hJ₁_pos.le.trans hJ, hJ₂_le_b⟩
      linarith [hmono h1 h2 hJ]
    have hJ_nn : 0 ≤ J₂ - J₁ := by linarith
    simp only [Real.dist_eq] at hdist
    rw [abs_sub_comm J₁ J₂, abs_of_nonneg hJ_nn,
        abs_sub_comm
          (correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J₁, 0, β⟩ : IsingParams ℝ) {r_val, s_val})
          (correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J₂, 0, β⟩ : IsingParams ℝ) {r_val, s_val}),
        abs_of_nonneg hcorr_nn] at hdist
    push_cast at hdist
    convert hdist using 2
    push_cast; ring

/-- **LipschitzOnWith of corr_∞ on closed [0, b] (including J = 0) in J** (Step 234):
For `0 < β`, `0 < b`, `bβ·2d < 1`: `J ↦ corr_∞(J)` is `C`-Lipschitz on `[0, b]` in J
with the same constant `C = β·M² + β·4d` as Step 222.

Direct J-direction analogue of Step 180. Strengthens Step 222 from `[a, b]` (a > 0)
to closed `[0, b]`. -/
theorem correlationInfinite_lipschitzOnWith_J_zero_closed
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * β * ↑(2 * d) < 1) :
    LipschitzOnWith ⟨β * (b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d))) ^ 2 + β * (4 * ↑d), by
        have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
        have hM_nn : 0 ≤ b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d)) :=
          div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hβ.le)
                       (Nat.cast_nonneg _)) hdenom_b.le
        have := hM_nn
        positivity⟩
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc 0 b) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro J₁ hJ₁ J₂ hJ₂
  rcases le_total J₁ J₂ with hJ_le | hJ_le
  · have hcorr_nn :
        0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J₂, 0, β⟩ : IsingParams ℝ) {r_val, s_val} -
            correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J₁, 0, β⟩ : IsingParams ℝ) {r_val, s_val} := by
      have hmono := correlationInfinite_monotoneOn_J_zero_closed Λ r_val s_val β hβ b
      linarith [hmono hJ₁ hJ₂ hJ_le]
    have hJ_nn : 0 ≤ J₂ - J₁ := by linarith
    rw [Real.dist_eq, Real.dist_eq, abs_sub_comm J₁ J₂,
        abs_sub_comm
          ((fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) J₁)
          ((fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) J₂),
        abs_of_nonneg hcorr_nn, abs_of_nonneg hJ_nn]
    have hbound := correlationInfinite_diff_le_const_mul_diff_J Λ r_val s_val hrs β hβ b hb_pos hlt
      J₁ J₂ hJ₁.1 hJ_le hJ₂.2
    push_cast
    push_cast at hbound
    exact hbound
  · have hcorr_nn :
        0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J₁, 0, β⟩ : IsingParams ℝ) {r_val, s_val} -
            correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J₂, 0, β⟩ : IsingParams ℝ) {r_val, s_val} := by
      have hmono := correlationInfinite_monotoneOn_J_zero_closed Λ r_val s_val β hβ b
      linarith [hmono hJ₂ hJ₁ hJ_le]
    have hJ_nn : 0 ≤ J₁ - J₂ := by linarith
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg hcorr_nn, abs_of_nonneg hJ_nn]
    have hbound := correlationInfinite_diff_le_const_mul_diff_J Λ r_val s_val hrs β hβ b hb_pos hlt
      J₂ J₁ hJ₂.1 hJ_le hJ₁.2
    push_cast
    push_cast at hbound
    exact hbound

/-- **Linear bound on corr_∞ at β = 0** (Step 181, β ≥ 0 version):
For `0 ≤ J`, `0 < b`, `bJ·2d < 1`, and any `r ≠ s`, on the interval `[0, b]`:
`corr_∞(r, s, β) ≤ (J·M(b)² + J·4d) · β`,
where `M(b) = bJ·2d/(1 - bJ·2d)`. Extension of Step 176 to include β = 0
(where both sides are 0).

In particular, `corr_∞(r, s, β) → 0` as `β → 0⁺` (right-continuity at 0). -/
theorem correlationInfinite_le_const_mul_beta_of_high_temp_zero_incl
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * J * ↑(2 * d) < 1)
    (β : ℝ) (hβ_nn : 0 ≤ β) (hβb : β ≤ b) :
    let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      {r_val, s_val} ≤ (J * M ^ 2 + J * (4 * ↑d)) * β := by
  intro M
  rcases eq_or_lt_of_le hβ_nn with hβ0 | hβ_pos
  · -- β = 0: both sides are 0
    rw [← hβ0, correlationInfinite_eq_zero_at_beta_zero, mul_zero]
  · -- β > 0: direct from Step 176
    exact correlationInfinite_le_const_mul_beta_of_high_temp
      Λ r_val s_val hrs J hJ b hb_pos hlt β hβ_pos hβb

/-- **Linear bound on corr_∞ at J = 0** (Step 235, J ≥ 0 version):
For `0 < β`, `0 < b`, `bβ·2d < 1`, and any `r ≠ s`, on the interval `[0, b]`:
`corr_∞(r, s, J) ≤ (β·M(b)² + β·4d) · J`,
where `M(b) = bβ·2d/(1 - bβ·2d)`. Direct J-direction analogue of Step 181:
extends Step 230 to include J = 0 (where both sides are 0). -/
theorem correlationInfinite_le_const_mul_J_of_high_temp_zero_incl
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * β * ↑(2 * d) < 1)
    (J : ℝ) (hJ_nn : 0 ≤ J) (hJb : J ≤ b) :
    let M : ℝ := b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d))
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      {r_val, s_val} ≤ (β * M ^ 2 + β * (4 * ↑d)) * J := by
  intro M
  rcases eq_or_lt_of_le hJ_nn with hJ0 | hJ_pos
  · rw [← hJ0, correlationInfinite_eq_zero_at_J_zero, mul_zero]
  · exact correlationInfinite_le_const_mul_J_of_high_temp
      Λ r_val s_val hrs β hβ b hb_pos hlt J hJ_pos hJb

/-- **ContinuousOn corr_∞ on Ico 0 β_c (half-open high-temperature interval)** (Step 182):
For `0 < J`, `1 ≤ d`: `β ↦ corr_∞(β)` is continuous on `Ico 0 (1/(J·2d))`
(closed at 0, open at β_c).

Combines Step 173 (continuity on Ioo 0 β_c) with Step 177 (continuity on Icc 0 b).

Proof: for each β₀ in the interval:
- β₀ > 0: use Step 175 ContinuousAt
- β₀ = 0: use Step 177 with b = (β_c)/2 (which is < β_c). -/
theorem correlationInfinite_continuousOn_beta_of_high_temp_Ico
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J) :
    ContinuousOn
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ico (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  have h2d_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
    exact_mod_cast this
  have hJ2d_pos : 0 < J * ↑(2 * d) := mul_pos hJ_pos h2d_pos
  have hβc_pos : 0 < 1 / (J * ↑(2 * d)) := one_div_pos.mpr hJ2d_pos
  intro β₀ hβ₀
  rcases eq_or_lt_of_le hβ₀.1 with hβ₀0 | hβ₀_pos
  · -- β₀ = 0: use Step 177 with b = β_c/2
    subst hβ₀0
    set b' : ℝ := (1 / (J * ↑(2 * d))) / 2 with hb'_def
    have hb'_pos : 0 < b' := by positivity
    have hb'_lt_βc : b' < 1 / (J * ↑(2 * d)) := by
      have : b' = (1 / (J * ↑(2 * d))) / 2 := rfl
      linarith
    have hlt : b' * J * ↑(2 * d) < 1 := by
      have h1 : b' * (J * ↑(2 * d)) < 1 := by
        have := (lt_div_iff₀ hJ2d_pos).mp hb'_lt_βc
        linarith [this]
      linarith [h1]
    have hcont_closed := correlationInfinite_continuousOn_beta_of_high_temp_zero_closed
      hd Λ r_val s_val hrs J hJ_pos b' hb'_pos hlt
    -- ContinuousOn [0, b'] ⇒ ContinuousWithinAt at 0 within [0, b']
    have hcwa := hcont_closed 0 (Set.mem_Icc.mpr ⟨le_refl _, hb'_pos.le⟩)
    -- Need: ContinuousWithinAt at 0 within Ico 0 β_c
    -- Use the fact that nhdsWithin (Icc 0 b') 0 contains points in (Ico 0 β_c) near 0
    apply hcwa.mono_of_mem_nhdsWithin
    -- Need: Set.Icc 0 b' ∈ 𝓝[Ico 0 β_c] 0
    rw [mem_nhdsWithin]
    refine ⟨Set.Iio b', isOpen_Iio, ?_, ?_⟩
    · exact hb'_pos
    · intro x hx
      have hx_lt_b' : x < b' := hx.1
      have hx_in_Ico : x ∈ Set.Ico (0 : ℝ) (1 / (J * ↑(2 * d))) := hx.2
      exact Set.mem_Icc.mpr ⟨hx_in_Ico.1, hx_lt_b'.le⟩
  · -- β₀ > 0: use Step 175
    have hβ₀_in_open : β₀ ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) := ⟨hβ₀_pos, hβ₀.2⟩
    exact (correlationInfinite_continuousAt_beta_of_high_temp
      hd Λ r_val s_val hrs J hJ_pos β₀ hβ₀_in_open).continuousWithinAt

/-- **ContinuousOn corr_∞ on Ico 0 J_c (half-open) in J** (Step 236):
For `0 < β`, `1 ≤ d`: `J ↦ corr_∞(J)` is continuous on `Ico 0 (1/(β·2d))`
(closed at 0, open at J_c). Direct J-direction analogue of Step 182. -/
theorem correlationInfinite_continuousOn_J_of_high_temp_Ico
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β) :
    ContinuousOn
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ico (0 : ℝ) (1 / (β * ↑(2 * d)))) := by
  have h2d_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
    exact_mod_cast this
  have hβ2d_pos : 0 < β * ↑(2 * d) := mul_pos hβ_pos h2d_pos
  have hJc_pos : 0 < 1 / (β * ↑(2 * d)) := one_div_pos.mpr hβ2d_pos
  intro J₀ hJ₀
  rcases eq_or_lt_of_le hJ₀.1 with hJ₀0 | hJ₀_pos
  · subst hJ₀0
    set b' : ℝ := (1 / (β * ↑(2 * d))) / 2 with hb'_def
    have hb'_pos : 0 < b' := by positivity
    have hb'_lt_Jc : b' < 1 / (β * ↑(2 * d)) := by
      have : b' = (1 / (β * ↑(2 * d))) / 2 := rfl
      linarith
    have hlt : b' * β * ↑(2 * d) < 1 := by
      have h1 : b' * (β * ↑(2 * d)) < 1 := by
        have := (lt_div_iff₀ hβ2d_pos).mp hb'_lt_Jc
        linarith [this]
      linarith [h1]
    have hcont_closed := correlationInfinite_continuousOn_J_of_high_temp_zero_closed
      hd Λ r_val s_val hrs β hβ_pos b' hb'_pos hlt
    have hcwa := hcont_closed 0 (Set.mem_Icc.mpr ⟨le_refl _, hb'_pos.le⟩)
    apply hcwa.mono_of_mem_nhdsWithin
    rw [mem_nhdsWithin]
    refine ⟨Set.Iio b', isOpen_Iio, ?_, ?_⟩
    · exact hb'_pos
    · intro x hx
      have hx_lt_b' : x < b' := hx.1
      have hx_in_Ico : x ∈ Set.Ico (0 : ℝ) (1 / (β * ↑(2 * d))) := hx.2
      exact Set.mem_Icc.mpr ⟨hx_in_Ico.1, hx_lt_b'.le⟩
  · have hJ₀_in_open : J₀ ∈ Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d))) := ⟨hJ₀_pos, hJ₀.2⟩
    exact (correlationInfinite_continuousAt_J_of_high_temp
      hd Λ r_val s_val hrs β hβ_pos J₀ hJ₀_in_open).continuousWithinAt

/-- **MonotoneOn corr_∞ in β on the half-line Ici 0** (Step 183):
For `0 ≤ J`: corr_∞ is monotone non-decreasing in β on the entire half-line `Ici 0`.

Proof: at β > 0 use `correlationInfinite_monotone_beta` (Ioi 0);
at β = 0, corr_∞(0) = 0 ≤ corr_∞(β₂) by nonnegativity. -/
theorem correlationInfinite_monotoneOn_beta_Ici_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (J : ℝ) (hJ : 0 ≤ J) :
    MonotoneOn
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ici (0 : ℝ)) := by
  intro β₁ hβ₁ β₂ hβ₂ hβ
  simp only
  have hβ₁_nn : 0 ≤ β₁ := hβ₁
  rcases eq_or_lt_of_le hβ₁_nn with hβ₁0 | hβ₁_pos
  · rw [← hβ₁0, correlationInfinite_eq_zero_at_beta_zero]
    rcases eq_or_lt_of_le (hβ₁0.le.trans hβ) with hβ₂0 | hβ₂_pos
    · rw [← hβ₂0, correlationInfinite_eq_zero_at_beta_zero]
    · exact correlationInfinite_nonneg _ _ _ ⟨hJ, le_refl 0, hβ₂_pos⟩ _
  · have hβ₁_in : β₁ ∈ Set.Ioi (0 : ℝ) := hβ₁_pos
    have hβ₂_in : β₂ ∈ Set.Ioi (0 : ℝ) := hβ₁_pos.trans_le hβ
    exact correlationInfinite_monotone_beta (IsingModel.latticeGraph d) Λ hJ (le_refl 0) _
      hβ₁_in hβ₂_in hβ

/-- **A.e. differentiability of corr_∞ on Ici 0** (Step 183):
For `0 ≤ J`: `β ↦ corr_∞(β)` is differentiable within `Ici 0` at Lebesgue-a.e. β.

Proof: `MonotoneOn.locallyBoundedVariationOn` (Step 183 monotonicity) +
`LocallyBoundedVariationOn.ae_differentiableWithinAt`. No high-temperature condition needed. -/
theorem correlationInfinite_ae_differentiableWithinAt_beta_Ici_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (J : ℝ) (hJ : 0 ≤ J) :
    ∀ᵐ β ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ici (0 : ℝ)),
    DifferentiableWithinAt ℝ
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ici (0 : ℝ)) β := by
  have hmono := correlationInfinite_monotoneOn_beta_Ici_zero Λ r_val s_val J hJ
  exact hmono.locallyBoundedVariationOn.ae_differentiableWithinAt measurableSet_Ici

/-- **MonotoneOn corr_∞ in J on the half-line Ici 0** (Step 237):
For `0 < β`: corr_∞ is monotone non-decreasing in J on the entire half-line `Ici 0`.

Direct J-direction analogue of Step 183. Direct application of
`correlationInfinite_monotone_J` at h = 0. -/
theorem correlationInfinite_monotoneOn_J_Ici_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (β : ℝ) (hβ : 0 < β) :
    MonotoneOn
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ici (0 : ℝ)) :=
  correlationInfinite_monotone_J (IsingModel.latticeGraph d) Λ (le_refl 0) hβ {r_val, s_val}

/-- **A.e. differentiability of corr_∞ on Ici 0 in J** (Step 237):
For `0 < β`: `J ↦ corr_∞(J)` is differentiable within `Ici 0` at Lebesgue-a.e. J.

Direct J-direction analogue of Step 183. Proof: `MonotoneOn.locallyBoundedVariationOn`
+ `LocallyBoundedVariationOn.ae_differentiableWithinAt`. No high-temperature condition. -/
theorem correlationInfinite_ae_differentiableWithinAt_J_Ici_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (β : ℝ) (hβ : 0 < β) :
    ∀ᵐ J ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ici (0 : ℝ)),
    DifferentiableWithinAt ℝ
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ici (0 : ℝ)) J := by
  have hmono := correlationInfinite_monotoneOn_J_Ici_zero Λ r_val s_val β hβ
  exact hmono.locallyBoundedVariationOn.ae_differentiableWithinAt measurableSet_Ici

/-- **TendstoLocallyUniformlyOn corr_n → corr_∞ on Ico 0 β_c (half-open)** (Step 184):
For `0 < J`, `1 ≤ d`: corr_n converges locally uniformly to corr_∞ on `Ico 0 (1/(J·2d))`.

Combines Step 174 (Ioo 0 β_c) with Step 178 (Icc 0 b) via Dini's locally-uniform theorem
on the half-open interval. -/
theorem correlationAlongExhaustion_tendstoLocallyUniformlyOn_beta_Ico
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J) :
    TendstoLocallyUniformlyOn
      (fun n β => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n)
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      Filter.atTop (Set.Ico (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  apply Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto
  · -- (1) ContinuousOn each corr_n on Ico 0 β_c
    intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      intro β _
      apply ContinuousAt.continuousWithinAt
      have heq : (fun β' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {r_val, s_val} n) =
                 (fun β' => IsingModel.correlation
                    (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                    ⟨s_val, hsn⟩}) := by
        funext β'
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
      rw [heq]
      exact IsingModel.correlation_continuousAt_beta _ J β _
    · simp only [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      exact continuousOn_const
  · -- (2) Monotone in n at each β ∈ Ico 0 β_c
    intro β hβ
    rcases eq_or_lt_of_le hβ.1 with hβ0 | hβ_pos
    · subst hβ0
      intro n m _
      simp only [correlationAlongExhaustion_eq_zero_at_beta_zero, le_refl]
    · exact correlationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ⟨hJ_pos.le, le_refl 0, hβ_pos⟩ {r_val, s_val}
  · -- (3) ContinuousOn corr_∞ on Ico 0 β_c (Step 182)
    exact correlationInfinite_continuousOn_beta_of_high_temp_Ico hd Λ r_val s_val hrs J hJ_pos
  · -- (4) Pointwise convergence
    intro β hβ
    rcases eq_or_lt_of_le hβ.1 with hβ0 | hβ_pos
    · subst hβ0
      simp only [correlationAlongExhaustion_eq_zero_at_beta_zero,
                 correlationInfinite_eq_zero_at_beta_zero]
      exact tendsto_const_nhds
    · have hf : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
        ⟨hJ_pos.le, le_refl 0, hβ_pos⟩
      have htend := IsingModel.Ambient.correlationAlongExhaustion_tendsto_ciSup
        (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf {r_val, s_val}
      rw [correlationInfinite_eq_ciSup]
      exact htend

/-- **TendstoLocallyUniformlyOn corr_n → corr_∞ on Ico 0 J_c (half-open) in J** (Step 238):
For `0 < β`, `1 ≤ d`: corr_n converges locally uniformly to corr_∞ on `Ico 0 (1/(β·2d))` in J.

Direct J-direction analogue of Step 184. Combines Step 228 (Ioo 0 J_c) with Step 232
(Icc 0 b) via Dini's locally-uniform theorem on the half-open interval. -/
theorem correlationAlongExhaustion_tendstoLocallyUniformlyOn_J_Ico
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β) :
    TendstoLocallyUniformlyOn
      (fun n J => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n)
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      Filter.atTop (Set.Ico (0 : ℝ) (1 / (β * ↑(2 * d)))) := by
  apply Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto
  · intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      intro J _
      apply ContinuousAt.continuousWithinAt
      have heq : (fun J' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J', 0, β⟩ : IsingParams ℝ) {r_val, s_val} n) =
                 (fun J' => IsingModel.correlation
                    (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                    (⟨J', 0, β⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                    ⟨s_val, hsn⟩}) := by
        funext J'
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
      rw [heq]
      exact (IsingModel.correlation_continuous_J _ 0 β _).continuousAt
    · simp only [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      exact continuousOn_const
  · intro J hJ
    rcases eq_or_lt_of_le hJ.1 with hJ0 | hJ_pos
    · subst hJ0
      intro n m _
      simp only [correlationAlongExhaustion_eq_zero_at_J_zero, le_refl]
    · exact correlationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ⟨hJ_pos.le, le_refl 0, hβ_pos⟩ {r_val, s_val}
  · exact correlationInfinite_continuousOn_J_of_high_temp_Ico hd Λ r_val s_val hrs β hβ_pos
  · intro J hJ
    rcases eq_or_lt_of_le hJ.1 with hJ0 | hJ_pos
    · subst hJ0
      simp only [correlationAlongExhaustion_eq_zero_at_J_zero,
                 correlationInfinite_eq_zero_at_J_zero]
      exact tendsto_const_nhds
    · have hf : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
        ⟨hJ_pos.le, le_refl 0, hβ_pos⟩
      have htend := IsingModel.Ambient.correlationAlongExhaustion_tendsto_ciSup
        (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf {r_val, s_val}
      rw [correlationInfinite_eq_ciSup]
      exact htend

/-- **truncated2Infinite ContinuousOn β at h = 0 on Ioo 0 β_c** (Step 185, GJ §17.5):
For `0 < J`, `1 ≤ d`, `r ≠ s`: the infinite-volume Ursell 2-point function is continuous
in β on the open high-temperature interval.

Proof: at h = 0, `truncated2Infinite = correlationInfinite {r, s}` (`truncated2Infinite_h_zero`).
Apply Step 173. -/
theorem truncated2Infinite_continuousOn_beta_of_high_temp_open
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J) :
    ContinuousOn
      (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  have heq : (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext β
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_continuousOn_beta_of_high_temp_open hd Λ r_val s_val hrs J hJ_pos

/-- **truncated2Infinite ContinuousOn β on closed [0, b]** (Step 185 closed variant). -/
theorem truncated2Infinite_continuousOn_beta_of_high_temp_zero_closed
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * J * ↑(2 * d) < 1) :
    ContinuousOn
      (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Icc (0 : ℝ) b) := by
  have heq : (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext β
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_continuousOn_beta_of_high_temp_zero_closed
    hd Λ r_val s_val hrs J hJ_pos b hb_pos hlt

/-- **truncated2Infinite ContinuousOn β on Ico 0 β_c (half-open)** (Step 185 Ico variant). -/
theorem truncated2Infinite_continuousOn_beta_of_high_temp_Ico
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J) :
    ContinuousOn
      (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Ico (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  have heq : (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext β
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_continuousOn_beta_of_high_temp_Ico hd Λ r_val s_val hrs J hJ_pos

/-- **truncated2Infinite ContinuousOn J on Ioo 0 J_c at h = 0** (Step 239):
J-direction analogue of Step 185 (Ioo variant). At h = 0, truncated2Infinite is
correlationInfinite {r, s}, so the result reduces to Step 227. -/
theorem truncated2Infinite_continuousOn_J_of_high_temp_open
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β) :
    ContinuousOn
      (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d)))) := by
  have heq : (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext J
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_continuousOn_J_of_high_temp_open hd Λ r_val s_val hrs β hβ_pos

/-- **truncated2Infinite ContinuousOn J on closed [0, b] at h = 0** (Step 239 closed variant).
J-direction analogue of Step 185 closed variant. -/
theorem truncated2Infinite_continuousOn_J_of_high_temp_zero_closed
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * β * ↑(2 * d) < 1) :
    ContinuousOn
      (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Icc (0 : ℝ) b) := by
  have heq : (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext J
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_continuousOn_J_of_high_temp_zero_closed
    hd Λ r_val s_val hrs β hβ_pos b hb_pos hlt

/-- **truncated2Infinite ContinuousOn J on Ico 0 J_c (half-open)** (Step 239 Ico variant). -/
theorem truncated2Infinite_continuousOn_J_of_high_temp_Ico
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β) :
    ContinuousOn
      (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Ico (0 : ℝ) (1 / (β * ↑(2 * d)))) := by
  have heq : (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext J
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_continuousOn_J_of_high_temp_Ico hd Λ r_val s_val hrs β hβ_pos

/-- **truncated2Infinite LipschitzOnWith β on [a, b] at h = 0** (Step 186 closed [a, b]).

Wrapper of Step 168 (corr_∞ LipschitzOnWith on [a, b]). -/
theorem truncated2Infinite_lipschitzOnWith_beta_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1) :
    let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
    LipschitzOnWith ⟨J * M ^ 2 + J * (4 * ↑d), by
        have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
        have hb_pos : 0 < b := ha.trans_le hab
        have hM_nn : 0 ≤ b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d)) :=
          div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hJ)
                       (Nat.cast_nonneg _)) hdenom_b.le
        exact add_nonneg (mul_nonneg hJ (pow_nonneg hM_nn 2))
               (mul_nonneg hJ (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))⟩
      (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Icc a b) := by
  intro M
  have heq : (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext β
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_lipschitzOnWith_beta_of_high_temp Λ r_val s_val hrs J hJ a b ha hab hlt

/-- **truncated2Infinite LipschitzOnWith β on closed [0, b] at h = 0** (Step 186 closed [0, b]).

Wrapper of Step 180. -/
theorem truncated2Infinite_lipschitzOnWith_beta_zero_closed
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * J * ↑(2 * d) < 1) :
    LipschitzOnWith ⟨J * (b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))) ^ 2 + J * (4 * ↑d), by
        have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
        have hM_nn : 0 ≤ b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d)) :=
          div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hJ)
                       (Nat.cast_nonneg _)) hdenom_b.le
        have := hM_nn
        positivity⟩
      (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Icc 0 b) := by
  have heq : (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext β
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_lipschitzOnWith_beta_zero_closed Λ r_val s_val hrs J hJ b hb_pos hlt

/-- **truncated2Infinite ae DifferentiableWithinAt on Ici 0 at h = 0** (Step 186 ae version).

Wrapper of Step 183. No high-temperature condition needed. -/
theorem truncated2Infinite_ae_differentiableWithinAt_beta_Ici_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (J : ℝ) (hJ : 0 ≤ J) :
    ∀ᵐ β ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ici (0 : ℝ)),
    DifferentiableWithinAt ℝ
      (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Ici (0 : ℝ)) β := by
  have heq : (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext β
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_ae_differentiableWithinAt_beta_Ici_zero Λ r_val s_val J hJ

/-- **truncated2Infinite MonotoneOn β on Ici 0 at h = 0** (Step 187):
For `0 ≤ J`: truncated2Infinite is monotone non-decreasing in β on `Ici 0` at h = 0.
Wrapper of Step 183 via `truncated2Infinite_h_zero`. -/
theorem truncated2Infinite_monotoneOn_beta_Ici_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (J : ℝ) (hJ : 0 ≤ J) :
    MonotoneOn
      (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Ici (0 : ℝ)) := by
  have heq : (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext β
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_monotoneOn_beta_Ici_zero Λ r_val s_val J hJ

/-! ## Step 240: truncated2Infinite J-direction Lipschitz/ae diff/MonotoneOn -/

/-- **truncated2Infinite LipschitzOnWith J on [a, b] at h = 0** (Step 240).
J-direction analogue of Step 186 (Icc a b). Wrapper of Step 222. -/
theorem truncated2Infinite_lipschitzOnWith_J_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * β * ↑(2 * d) < 1) :
    let M : ℝ := b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d))
    LipschitzOnWith ⟨β * M ^ 2 + β * (4 * ↑d), by
        have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
        have hb_pos : 0 < b := ha.trans_le hab
        have hM_nn : 0 ≤ b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d)) :=
          div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hβ.le)
                       (Nat.cast_nonneg _)) hdenom_b.le
        exact add_nonneg (mul_nonneg hβ.le (pow_nonneg hM_nn 2))
               (mul_nonneg hβ.le (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))⟩
      (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Icc a b) := by
  intro M
  have heq : (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext J
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_lipschitzOnWith_J_of_high_temp Λ r_val s_val hrs β hβ a b ha hab hlt

/-- **truncated2Infinite LipschitzOnWith J on closed [0, b] at h = 0** (Step 240).
J-direction analogue of Step 186 (Icc 0 b). Wrapper of Step 234. -/
theorem truncated2Infinite_lipschitzOnWith_J_zero_closed
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * β * ↑(2 * d) < 1) :
    LipschitzOnWith ⟨β * (b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d))) ^ 2 + β * (4 * ↑d), by
        have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
        have hM_nn : 0 ≤ b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d)) :=
          div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hβ.le)
                       (Nat.cast_nonneg _)) hdenom_b.le
        have := hM_nn
        positivity⟩
      (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Icc 0 b) := by
  have heq : (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext J
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_lipschitzOnWith_J_zero_closed Λ r_val s_val hrs β hβ b hb_pos hlt

/-- **truncated2Infinite ae DifferentiableWithinAt on Ici 0 in J at h = 0** (Step 240).
J-direction analogue of Step 186 (ae version). Wrapper of Step 237. -/
theorem truncated2Infinite_ae_differentiableWithinAt_J_Ici_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (β : ℝ) (hβ : 0 < β) :
    ∀ᵐ J ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ici (0 : ℝ)),
    DifferentiableWithinAt ℝ
      (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Ici (0 : ℝ)) J := by
  have heq : (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext J
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_ae_differentiableWithinAt_J_Ici_zero Λ r_val s_val β hβ

/-- **truncated2Infinite MonotoneOn J on Ici 0 at h = 0** (Step 240).
J-direction analogue of Step 187. Wrapper of Step 237. -/
theorem truncated2Infinite_monotoneOn_J_Ici_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (β : ℝ) (hβ : 0 < β) :
    MonotoneOn
      (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Ici (0 : ℝ)) := by
  have heq : (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext J
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_monotoneOn_J_Ici_zero Λ r_val s_val β hβ

/-! ## Step 241: truncated2Infinite ContinuousAt at every interior point in β + J -/

/-- **truncated2Infinite ContinuousAt every β ∈ Ioo 0 β_c at h = 0** (Step 241).
For any β₀ ∈ Ioo 0 (1/(J·2d)): truncated2Infinite is ContinuousAt at β₀
(full neighborhood, not just within-set). Wrapper of Step 175. -/
theorem truncated2Infinite_continuousAt_beta_of_high_temp
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J)
    (β₀ : ℝ) (hβ₀ : β₀ ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) :
    ContinuousAt
      (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      β₀ := by
  have heq : (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext β
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_continuousAt_beta_of_high_temp hd Λ r_val s_val hrs J hJ_pos β₀ hβ₀

/-- **truncated2Infinite ContinuousAt every J ∈ Ioo 0 J_c at h = 0** (Step 241).
For any J₀ ∈ Ioo 0 (1/(β·2d)): truncated2Infinite is ContinuousAt at J₀
(full neighborhood, not just within-set). Wrapper of Step 229. -/
theorem truncated2Infinite_continuousAt_J_of_high_temp
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β)
    (J₀ : ℝ) (hJ₀ : J₀ ∈ Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d)))) :
    ContinuousAt
      (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      J₀ := by
  have heq : (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext J
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_continuousAt_J_of_high_temp hd Λ r_val s_val hrs β hβ_pos J₀ hJ₀

end Ambient

end IsingModel
