import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSExistingClusterBundle
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSSubstantiveClusterBundle

/-!
# Substantive HLS canonical summary API + short aliases

GJ-proposition-unit canonical summary API for the substantive HLS sum
bound chain.

Provides the simplest stable entry points covering both the half-rate
substantive bound (#3199, via Step 5.7h Simon-Lieb) and the full-rate
existing bound (#3202, via existing `hasExponentialDecay_of_high_temp`).

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

/-- **Canonical cluster property** (ferromagnetic + strict high-temp).
Short alias for
`clusterProperty_latticeGraph_of_existing_ferromagnetic_high_temp`. -/
theorem hls_cluster_property
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  clusterProperty_latticeGraph_of_existing_ferromagnetic_high_temp
    hf hβJd_pos hβJd_lt

/-- **Canonical per-site cofinite tendsto** (truncated2 form). -/
theorem hls_tendsto_truncated2
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i : Fin d → ℤ) :
    Filter.Tendsto (fun j : Fin d → ℤ =>
        truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) i j) Filter.cofinite (nhds 0) :=
  truncated2Infinite_tendsto_cofinite_zero_of_existing_ferromagnetic_high_temp
    hf hβJd_pos hβJd_lt i

/-- **Canonical per-site cofinite tendsto** (correlation form at h=0). -/
theorem hls_tendsto_correlation
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i : Fin d → ℤ) :
    Filter.Tendsto (fun j : Fin d → ℤ =>
        correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}) Filter.cofinite (nhds 0) :=
  correlationInfinite_tendsto_cofinite_zero_of_existing_ferromagnetic_high_temp
    hf hβJd_pos hβJd_lt i

/-! ## Diagonal canonical -/

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
  exists_tsum_correlationInfinite_pair_product_diagonal_le_of_existing_ferromagnetic
    hf hβJd_pos hβJd_lt x₀

/-! ## HasExponentialDecay canonical -/

/-- **Canonical HasExponentialDecay** at the strongest rate `-log(β·J·(2d))`. -/
theorem hls_hasExponentialDecay
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    HasExponentialDecay d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) (-Real.log (β * J * ↑(2 * d))) :=
  hasExponentialDecay_existing_rate_of_ferromagnetic_high_temp hf hβJd_lt

/-- **Canonical existential positive rate HasExponentialDecay witness**. -/
theorem hls_exists_pos_rate_decay
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ α : ℝ, 0 < α ∧
      HasExponentialDecay d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) α :=
  exists_pos_rate_hasExponentialDecay_of_existing_ferromagnetic_high_temp
    hf hβJd_pos hβJd_lt

/-! ## Canonical positive rate accessor -/

/-- **Canonical positive rate `-log(β·J·(2d))`**. -/
theorem hls_canonical_rate_pos
    {β J : ℝ} {d : ℕ}
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (0 : ℝ) < -Real.log (β * J * ↑(2 * d)) :=
  neg_log_betaJ_two_d_pos_of_strict_high_temp hβJd_pos hβJd_lt

end Ambient
end IsingModel
