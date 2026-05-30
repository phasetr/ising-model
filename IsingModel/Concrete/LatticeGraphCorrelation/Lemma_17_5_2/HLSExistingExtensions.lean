import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSExistingHasExponentialDecayBridges

/-!
# HLS existing-rate substantive bundle extensions

GJ-proposition-unit bundle of anchor specializations and convenience
accessors for the existing-rate substantive HLS sum bound (#3202).

Mirror structure of #3200 (which was for the half-rate #3199 version)
adapted to the STRONGER full-rate `-log(β·J·(2d))` version.

**Reference:** Glimm-Jaffe §17.5 Lemma 17.5.2.
-/

namespace IsingModel
namespace Ambient

/-! ## Anchor specializations -/

/-- **Zero anchor `(0, 0)`**. -/
theorem exists_tsum_correlationInfinite_pair_product_zero_anchor_le_of_existing_ferromagnetic
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∑' z : Fin d → ℤ,
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {0, z} *
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {0, z}
      ≤ K * Real.exp (-M * (latticeDistance d 0 0 : ℝ)) := by
  obtain ⟨K, M, hK_nn, hM_pos, h_bound⟩ :=
    exists_tsum_correlationInfinite_pair_product_le_of_existing_ferromagnetic
      hf hβJd_pos hβJd_lt
  exact ⟨K, M, hK_nn, hM_pos, h_bound 0 0⟩

/-- **Diagonal anchor `(x₀, x₀)`**. -/
theorem exists_tsum_correlationInfinite_pair_product_diagonal_le_of_existing_ferromagnetic
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1)
    (x₀ : Fin d → ℤ) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∑' z : Fin d → ℤ,
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z}
      ≤ K * Real.exp (-M * (latticeDistance d x₀ x₀ : ℝ)) := by
  obtain ⟨K, M, hK_nn, hM_pos, h_bound⟩ :=
    exists_tsum_correlationInfinite_pair_product_le_of_existing_ferromagnetic
      hf hβJd_pos hβJd_lt
  exact ⟨K, M, hK_nn, hM_pos, h_bound x₀ x₀⟩

/-- **Swap anchor `(y₀, x₀)`**. -/
theorem exists_tsum_correlationInfinite_pair_product_swap_le_of_existing_ferromagnetic
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1)
    (x₀ y₀ : Fin d → ℤ) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∑' z : Fin d → ℤ,
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z} *
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z}
      ≤ K * Real.exp (-M * (latticeDistance d y₀ x₀ : ℝ)) := by
  obtain ⟨K, M, hK_nn, hM_pos, h_bound⟩ :=
    exists_tsum_correlationInfinite_pair_product_le_of_existing_ferromagnetic
      hf hβJd_pos hβJd_lt
  exact ⟨K, M, hK_nn, hM_pos, h_bound y₀ x₀⟩

/-- **Antipode anchor `(v, -v)`**. -/
theorem exists_tsum_correlationInfinite_pair_product_antipode_le_of_existing_ferromagnetic
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1)
    (v : Fin d → ℤ) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∑' z : Fin d → ℤ,
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {v, z} *
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {-v, z}
      ≤ K * Real.exp (-M * (latticeDistance d v (-v) : ℝ)) := by
  obtain ⟨K, M, hK_nn, hM_pos, h_bound⟩ :=
    exists_tsum_correlationInfinite_pair_product_le_of_existing_ferromagnetic
      hf hβJd_pos hβJd_lt
  exact ⟨K, M, hK_nn, hM_pos, h_bound v (-v)⟩

/-! ## K positivity / rate accessors -/

/-- **Existential `K ≥ 0`, `M > 0` extraction**. -/
theorem exists_K_nonneg_M_pos_existing_substantive_hls
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M :=
  let ⟨K, M, hK_nn, hM_pos, _⟩ :=
    exists_tsum_correlationInfinite_pair_product_le_of_existing_ferromagnetic
      hf hβJd_pos hβJd_lt
  ⟨K, M, hK_nn, hM_pos⟩

/-- **Existing-rate `M = -log(β·J·(2d))/4` is positive**. -/
theorem neg_log_betaJ_two_d_div_four_pos_of_strict_high_temp
    {β J : ℝ} {d : ℕ}
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (0 : ℝ) < -Real.log (β * J * ↑(2 * d)) / 4 := by
  have h := neg_log_betaJ_two_d_pos_of_strict_high_temp hβJd_pos hβJd_lt
  linarith

end Ambient
end IsingModel
