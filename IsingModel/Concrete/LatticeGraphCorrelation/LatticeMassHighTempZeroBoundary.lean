import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempLipschitz.NormSub

/-!
# ℤ^d linear bounds on the two-point function at the zero boundary (§17.5)

Instantiates at `IsingModel.latticeGraph d`, for an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ` at zero external field, the bound of the two-point correlation by an explicit
constant times the parameter that is being sent to zero, in the inverse-temperature direction
and in the coupling direction. Each direction is proved first on the subgraph induced by the
volume of a single exhaustion stage, for two distinct vertices of that volume, and then in
the infinite-volume limit, for two distinct sites of the lattice. The inverse-temperature
statements assume `0 ≤ J` and confine the inverse temperature to `(0, b]` with `b` times the
coupling times `2 * d` below one; the coupling statements assume `0 < β` and confine the
coupling to `(0, b]` with `b` times the inverse temperature times `2 * d` below one; the
infinite-volume statements assume `0 < b` as well. The module also records that the
infinite-volume correlation vanishes at zero inverse temperature and zero field, for an
arbitrary pair of sites, not assumed distinct, and with no hypothesis at all.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

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
lemma correlationInfinite_eq_zero_at_beta_zero
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

end Ambient
end IsingModel
