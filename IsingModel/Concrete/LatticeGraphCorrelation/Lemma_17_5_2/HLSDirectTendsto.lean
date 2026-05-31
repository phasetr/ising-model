import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSDispatchAPI

/-!
# Substantive HLS direct tendsto bundle

GJ-proposition-unit bundle providing direct `Tendsto` accessor wrappers
combining `hls_cluster` with the standard `clusterProperty` unfolding.

**Reference:** Glimm-Jaffe §17.5 / §5.1.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Direct tendsto wrappers -/

/-- **Direct truncated2 tendsto cofinite zero** from `0 < β·J`. -/
theorem hls_tendsto_truncated2_zero_direct
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i : Fin d → ℤ) :
    Filter.Tendsto (fun j : Fin d → ℤ =>
        truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) i j) Filter.cofinite (nhds 0) :=
  hls_cluster hd hf hβJ hβJd_lt i

/-- **Direct correlationInfinite tendsto cofinite zero** at h=0 from `0 < β·J`. -/
theorem hls_tendsto_correlation_zero_direct
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i : Fin d → ℤ) :
    Filter.Tendsto (fun j : Fin d → ℤ =>
        correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}) Filter.cofinite (nhds 0) := by
  have h_t2 := hls_tendsto_truncated2_zero_direct hd hf hβJ hβJd_lt i
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

/-- **Direct latticeMass + tendsto joint** from `0 < β·J`. -/
theorem hls_latticeMass_and_tendsto_direct
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (0 < latticeMass d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ)) ∧
    (∀ i : Fin d → ℤ,
      Filter.Tendsto (fun j : Fin d → ℤ =>
          truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) i j) Filter.cofinite (nhds 0)) :=
  ⟨hls_latticeMass hd hf hβJ hβJd_lt,
   fun i => hls_tendsto_truncated2_zero_direct hd hf hβJ hβJd_lt i⟩

/-- **Direct: tendsto correlation form joint** from `0 < β·J`. -/
theorem hls_tendsto_correlation_form_direct
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∀ i : Fin d → ℤ,
      Filter.Tendsto (fun j : Fin d → ℤ =>
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}) Filter.cofinite (nhds 0) :=
  fun i => hls_tendsto_correlation_zero_direct hd hf hβJ hβJd_lt i

/-- **Direct: tendsto truncated2 form joint** from `0 < β·J`. -/
theorem hls_tendsto_truncated2_form_direct
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∀ i : Fin d → ℤ,
      Filter.Tendsto (fun j : Fin d → ℤ =>
          truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) i j) Filter.cofinite (nhds 0) :=
  fun i => hls_tendsto_truncated2_zero_direct hd hf hβJ hβJd_lt i

end Ambient
end IsingModel
