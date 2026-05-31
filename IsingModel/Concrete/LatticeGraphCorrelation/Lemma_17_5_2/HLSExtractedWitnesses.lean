import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSMaster

/-!
# Substantive HLS — extracted normalized witness forms

GJ-proposition-unit bundle providing alternative witness shapes for the
substantive HLS sum bound (`K + 1 > 0`, `K + 1 ≥ 1`, `0 ≤ M` instead of
`0 < M`), existential susceptibility bound, and combined
mass+cluster / decay+cluster aggregates. Each declaration is a small
witness reformulation built on `hls_master_*`.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Extracted bound witness with `K > 0` -/

/-- **Sum bound with `K > 0`** (strict positivity). -/
theorem hls_sum_bound_pos
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K M : ℝ, 0 < K + 1 ∧ 0 < M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {y, z}
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ)) := by
  obtain ⟨K, M, hK_nn, hM_pos, h⟩ := hls_master_sum hd hf hβJ hβJd_lt
  refine ⟨K, M, ?_, hM_pos, h⟩
  linarith

/-! ## Extracted bound witness with nonneg M shifted upward -/

/-- **Sum bound with `K ≥ 1`** (raise K to at least 1). -/
theorem hls_sum_bound_K_ge_one
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K M : ℝ, 1 ≤ K + 1 ∧ 0 < M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {y, z}
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ)) := by
  obtain ⟨K, M, hK_nn, hM_pos, h⟩ := hls_master_sum hd hf hβJ hβJd_lt
  refine ⟨K, M, ?_, hM_pos, h⟩
  linarith

/-! ## Extracted `0 ≤ M` form -/

/-- **Sum bound with `0 ≤ M`** (relaxed positivity). -/
theorem hls_sum_bound_M_nonneg
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 ≤ M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {y, z}
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ)) := by
  obtain ⟨K, M, hK_nn, hM_pos, h⟩ := hls_master_sum hd hf hβJ hβJd_lt
  exact ⟨K, M, hK_nn, hM_pos.le, h⟩

/-! ## Extracted susceptibility bound as `∃ B` form -/

/-- **Bounded susceptibility (existential B)**. -/
theorem hls_susceptibility_exists_bound
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ B : ℝ, ∀ i : Fin d → ℤ,
      susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i ≤ B :=
  ⟨β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)),
   fun i => hls_master_susc hd hf hβJ hβJd_lt i⟩

/-! ## Combined: mass + cluster -/

/-- **Mass and cluster combined**. -/
theorem hls_mass_and_cluster
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (0 < latticeMass d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ)) ∧
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  ⟨hls_master_mass hd hf hβJ hβJd_lt, hls_master_cluster hd hf hβJ hβJd_lt⟩

/-! ## Combined: decay + cluster -/

/-- **Decay and cluster combined**. -/
theorem hls_decay_and_cluster
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    HasExponentialDecay d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) (-Real.log (β * J * ↑(2 * d))) ∧
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  ⟨hls_master_decay hd hf hβJ hβJd_lt, hls_master_cluster hd hf hβJ hβJd_lt⟩

end Ambient
end IsingModel
