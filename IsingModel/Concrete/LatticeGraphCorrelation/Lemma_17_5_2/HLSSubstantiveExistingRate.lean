import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSSubstantiveSimonLieb

/-!
# Substantive HLS existing-rate bridge

This module contains the full-rate high-temperature route from existing
`HasExponentialDecay` infrastructure to the substantive HLS tsum bound and its
basic canonical rate/decay accessors.

**Reference:** Glimm-Jaffe §17.5 Lemma 17.5.2.
-/

namespace IsingModel
namespace Ambient

/-! ## Existing HasExponentialDecay to substantive HLS sum bridges -/

/-- **Substantive tsum bound at h=0 from the existing high-temp
HasExponentialDecay** (FULL rate `-log(β·J·(2d))`, stronger than #3199). -/
theorem exists_tsum_truncated2Infinite_prod_le_of_existing_high_temp
    {d : ℕ} {β J : ℝ}
    (hβJ : 0 ≤ β * J) (hβJd_pos : 0 < β * J * (2 * d))
    (hβJd_lt : β * J * ↑(2 * d) < 1)
    (hβ : 0 < β) (hJ : 0 ≤ J) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) x z *
            truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) y z
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ)) := by
  obtain ⟨C, hC_nn, hbound⟩ := hasExponentialDecay_of_high_temp hβJ hβJd_lt
  set α := -Real.log (β * J * ↑(2 * d)) with hα_def
  have hα_pos : 0 < α := by
    rw [hα_def]
    apply neg_pos.mpr
    have h_cast : β * J * ↑(2 * d) = β * J * (2 * d) := by push_cast; ring
    rw [h_cast]
    exact Real.log_neg hβJd_pos (by rw [← h_cast]; exact hβJd_lt)
  have hα_half_pos : 0 < α / 2 := by linarith
  refine ⟨(C + 1) ^ 2 *
            (2 * ∑' z : Fin d → ℤ,
              Real.exp (-(α / 2) * (latticeDistance d 0 z : ℝ))), α / 4,
          ?_, by linarith, ?_⟩
  · have h_K_factor1_nn : (0 : ℝ) ≤ (C + 1) ^ 2 := sq_nonneg _
    have h_tsum_nn : 0 ≤ ∑' z : Fin d → ℤ,
        Real.exp (-(α / 2) * (latticeDistance d 0 z : ℝ)) :=
      tsum_nonneg (fun _ => (Real.exp_pos _).le)
    have h_K_factor2_nn : (0 : ℝ) ≤ 2 * ∑' z : Fin d → ℤ,
        Real.exp (-(α / 2) * (latticeDistance d 0 z : ℝ)) :=
      mul_nonneg (by norm_num) h_tsum_nn
    exact mul_nonneg h_K_factor1_nn h_K_factor2_nn
  · intro x y
    have h_tsum := tsum_truncated2Infinite_prod_le
      hJ hβ hα_pos hC_nn hbound x y
    have h_rate_eq : -(α / 2) * (latticeDistance d x y : ℝ) / 2 =
        -(α / 4) * (latticeDistance d x y : ℝ) := by ring
    have h_exp_eq : Real.exp (-(α / 2) * (latticeDistance d x y : ℝ) / 2) =
        Real.exp (-(α / 4) * (latticeDistance d x y : ℝ)) := by rw [h_rate_eq]
    rw [h_exp_eq] at h_tsum
    exact h_tsum

/-- **Ferromagnetic-form alias** of the existing-rate substantive bound. -/
theorem exists_tsum_truncated2Infinite_prod_le_of_existing_ferromagnetic_high_temp
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) x z *
            truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) y z
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ)) :=
  exists_tsum_truncated2Infinite_prod_le_of_existing_high_temp
    (mul_nonneg hf.hβ.le hf.hJ) hβJd_pos hβJd_lt hf.hβ hf.hJ

/-- **Correlation-form via h=0 identity**. -/
theorem exists_tsum_correlationInfinite_pair_product_le_of_existing_ferromagnetic
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {y, z}
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ)) := by
  obtain ⟨K, M, hK_nn, hM_pos, h_bound⟩ :=
    exists_tsum_truncated2Infinite_prod_le_of_existing_ferromagnetic_high_temp
      hf hβJd_pos hβJd_lt
  refine ⟨K, M, hK_nn, hM_pos, ?_⟩
  intro x y
  have h_summand_eq : ∀ z : Fin d → ℤ,
      truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z *
      truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) y z =
      correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
      correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {y, z} := fun z => by
    rw [truncated2Infinite_latticeGraph_h_zero d J β x z,
        truncated2Infinite_latticeGraph_h_zero d J β y z]
  have h_tsum_eq : (∑' z : Fin d → ℤ,
      truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z *
      truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) y z) =
      ∑' z : Fin d → ℤ,
        correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
        correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {y, z} := by
    congr 1
    funext z
    exact h_summand_eq z
  rw [← h_tsum_eq]
  exact h_bound x y

/-- **`-log(β·J·(2d)) > 0` from strict high-temp**. -/
theorem neg_log_betaJ_two_d_pos_of_strict_high_temp
    {β J : ℝ} {d : ℕ}
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    0 < -Real.log (β * J * ↑(2 * d)) := by
  apply neg_pos.mpr
  have hβJd_cast : β * J * ↑(2 * d) = β * J * (2 * d) := by push_cast; ring
  rw [hβJd_cast] at hβJd_lt ⊢
  exact Real.log_neg hβJd_pos hβJd_lt

/-- **`1 / (1 - β·J·(2d)) > 0` from strict high-temp**. -/
theorem one_div_one_sub_pos_of_strict_high_temp
    {β J : ℝ} {d : ℕ}
    (hβJd_lt : β * J * (2 * d) < 1) :
    (0 : ℝ) < 1 / (1 - β * J * (2 * d)) := by
  have h_denom_pos : (0 : ℝ) < 1 - β * J * (2 * d) := by linarith
  exact div_pos zero_lt_one h_denom_pos

/-! ## Canonical entry points (full-rate / strongest) -/

/-- **Canonical substantive HLS sum bound** (full-rate, strongest,
ferromagnetic). -/
theorem hls_substantive_bound
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {y, z}
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ)) :=
  exists_tsum_correlationInfinite_pair_product_le_of_existing_ferromagnetic
    hf hβJd_pos hβJd_lt

/-- **Canonical cluster property** (ferromagnetic + strict high-temp). -/
theorem hls_cluster_property
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  have hα_pos := neg_log_betaJ_two_d_pos_of_strict_high_temp hβJd_pos hβJd_lt
  have h_decay :=
    hasExponentialDecay_of_high_temp (mul_nonneg hf.hβ.le hf.hJ) hβJd_lt
  clusterProperty_latticeGraph_of_HasExponentialDecay d
    (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) hα_pos h_decay

/-- **Canonical per-site cofinite tendsto** (truncated2 form). -/
theorem hls_tendsto_truncated2
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i : Fin d → ℤ) :
    Filter.Tendsto (fun j : Fin d → ℤ =>
        truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) i j) Filter.cofinite (nhds 0) :=
  hls_cluster_property hf hβJd_pos hβJd_lt i

/-- **Canonical per-site cofinite tendsto** (correlation form at h=0). -/
theorem hls_tendsto_correlation
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i : Fin d → ℤ) :
    Filter.Tendsto (fun j : Fin d → ℤ =>
        correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}) Filter.cofinite (nhds 0) :=
  by
    have h_t2 := hls_tendsto_truncated2 hf hβJd_pos hβJd_lt i
    have h_eq : (fun j : Fin d → ℤ =>
        truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) i j) =
        (fun j : Fin d → ℤ =>
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}) := by
      funext j
      exact truncated2Infinite_latticeGraph_h_zero d J β i j
    rw [h_eq] at h_t2
    exact h_t2

/-! ## HasExponentialDecay canonical -/

/-- **Canonical HasExponentialDecay** at the strongest rate `-log(β·J·(2d))`. -/
theorem hls_hasExponentialDecay
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    HasExponentialDecay d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) (-Real.log (β * J * ↑(2 * d))) :=
  hasExponentialDecay_of_high_temp (mul_nonneg hf.hβ.le hf.hJ) hβJd_lt

/-- **Canonical existential positive rate HasExponentialDecay witness**. -/
theorem hls_exists_pos_rate_decay
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ α : ℝ, 0 < α ∧
      HasExponentialDecay d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) α :=
  ⟨-Real.log (β * J * ↑(2 * d)),
    neg_log_betaJ_two_d_pos_of_strict_high_temp hβJd_pos hβJd_lt,
    hls_hasExponentialDecay hf hβJd_lt⟩

/-! ## Canonical positive rate accessor -/

/-- **Canonical positive rate `-log(β·J·(2d))`**. -/
theorem hls_canonical_rate_pos
    {β J : ℝ} {d : ℕ}
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (0 : ℝ) < -Real.log (β * J * ↑(2 * d)) :=
  neg_log_betaJ_two_d_pos_of_strict_high_temp hβJd_pos hβJd_lt

/-- **Canonical HLS tsum rate `-log(β·J·(2d))/4` positivity helper**. -/
theorem hls_canonical_tsum_rate_pos
    {β J : ℝ} {d : ℕ}
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (0 : ℝ) < -Real.log (β * J * ↑(2 * d)) / 4 := by
  have h := hls_canonical_rate_pos hβJd_pos hβJd_lt
  linarith

end Ambient
end IsingModel
