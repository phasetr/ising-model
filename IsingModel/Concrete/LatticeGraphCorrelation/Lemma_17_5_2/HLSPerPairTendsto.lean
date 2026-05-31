import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSDirectTendsto

/-!
# Substantive HLS per-pair tendsto bundle

GJ-proposition-unit bundle of per-pair tendsto wrappers and pair-form
joint statements built on the substantive HLS chain.

**Reference:** Glimm-Jaffe §17.5 / §5.1.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Per-pair tendsto wrappers -/

/-- **Tendsto correlation at zero anchor** (i = 0). -/
theorem hls_tendsto_correlation_zero_anchor
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    Filter.Tendsto (fun j : Fin d → ℤ =>
        correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {0, j}) Filter.cofinite (nhds 0) :=
  hls_tendsto_correlation_zero_direct hd hf hβJ hβJd_lt 0

/-- **Tendsto truncated2 at zero anchor** (i = 0). -/
theorem hls_tendsto_truncated2_zero_anchor
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    Filter.Tendsto (fun j : Fin d → ℤ =>
        truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) 0 j) Filter.cofinite (nhds 0) :=
  hls_tendsto_truncated2_zero_direct hd hf hβJ hβJd_lt 0

/-! ## Pair-form joint statements -/

/-- **Joint: HLS sum + tendsto correlation form** from `0 < β·J`. -/
theorem hls_sum_and_tendsto_correlation
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {y, z}
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ))) ∧
    (∀ i : Fin d → ℤ,
      Filter.Tendsto (fun j : Fin d → ℤ =>
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}) Filter.cofinite (nhds 0)) :=
  ⟨hls_sum_bound hd hf hβJ hβJd_lt,
   hls_tendsto_correlation_form_direct hd hf hβJ hβJd_lt⟩

/-- **Joint: cluster + susceptibility + latticeMass** triple from `0 < β·J`. -/
theorem hls_cluster_susceptibility_latticeMass_triple
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    (∀ i : Fin d → ℤ,
      susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
        ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) ∧
    (0 < latticeMass d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  ⟨hls_cluster hd hf hβJ hβJd_lt,
   fun i => hls_susc hd hf hβJ hβJd_lt i,
   hls_latticeMass hd hf hβJ hβJd_lt⟩

/-! ## Witness summary -/

/-- **Witness summary**: existential decay rate + nonneg K. -/
theorem hls_witness_summary
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ α K : ℝ, 0 < α ∧ 0 ≤ K := by
  obtain ⟨K, M, hK_nn, hM_pos, _⟩ := hls_sum_bound hd hf hβJ hβJd_lt
  exact ⟨M, K, hM_pos, hK_nn⟩

end Ambient
end IsingModel
