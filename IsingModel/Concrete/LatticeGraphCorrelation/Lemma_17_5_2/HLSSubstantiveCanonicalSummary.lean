import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSExistingHasExponentialDecayBridges
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundation

/-!
# Substantive HLS canonical summary API + short aliases

GJ-proposition-unit canonical summary API for the full-rate substantive HLS
sum bound chain.

Provides the simplest stable entry points for the strongest existing-rate path
(#3202, via existing `hasExponentialDecay_of_high_temp`). The older
Simon-Lieb half-rate path remains available by importing `HLSSubstantiveBundle`
directly, but it is no longer re-exported from this canonical summary.

**Reference:** Glimm-Jaffe §17.5 Lemma 17.5.2.
-/

namespace IsingModel
namespace Ambient

/-! ## Short canonical entry points (full-rate / strongest) -/

/-- **Canonical substantive HLS sum bound** (full-rate, strongest, ferromagnetic).
Short alias for `exists_tsum_correlationInfinite_pair_product_le_of_existing_ferromagnetic`. -/
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

/-! ## Anchor canonical entry points -/

/-- **Canonical zero-anchor substantive HLS bound** at `(0, 0)`. -/
theorem hls_substantive_bound_zero_anchor
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
    hls_substantive_bound hf hβJd_pos hβJd_lt
  exact ⟨K, M, hK_nn, hM_pos, h_bound 0 0⟩

/-- **Canonical diagonal substantive HLS bound** at `(x₀, x₀)`. -/
theorem hls_substantive_bound_diagonal
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
      ≤ K * Real.exp (-M * (latticeDistance d x₀ x₀ : ℝ)) :=
  by
    obtain ⟨K, M, hK_nn, hM_pos, h_bound⟩ :=
      hls_substantive_bound hf hβJd_pos hβJd_lt
    exact ⟨K, M, hK_nn, hM_pos, h_bound x₀ x₀⟩

/-- **Canonical swapped-anchor substantive HLS bound** at `(y₀, x₀)`. -/
theorem hls_substantive_bound_swap
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
    hls_substantive_bound hf hβJd_pos hβJd_lt
  exact ⟨K, M, hK_nn, hM_pos, h_bound y₀ x₀⟩

/-- **Canonical antipode-anchor substantive HLS bound** at `(v, -v)`. -/
theorem hls_substantive_bound_antipode
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
    hls_substantive_bound hf hβJd_pos hβJd_lt
  exact ⟨K, M, hK_nn, hM_pos, h_bound v (-v)⟩

/-! ## Witness canonical entry points -/

/-- **Canonical `K ≥ 0`, `M > 0` extraction** from the substantive HLS bound. -/
theorem hls_exists_K_M_substantive_bound
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M :=
  let ⟨K, M, hK_nn, hM_pos, _⟩ := hls_substantive_bound hf hβJd_pos hβJd_lt
  ⟨K, M, hK_nn, hM_pos⟩

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
