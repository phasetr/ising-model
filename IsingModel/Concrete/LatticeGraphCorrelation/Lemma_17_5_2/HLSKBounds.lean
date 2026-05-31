import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSFinalWitness

/-!
# Substantive HLS K bounds bundle

GJ-proposition-unit bundle of K (substantive HLS sum bound constant) related
inequality wrappers.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## K-bound wrappers -/

/-- **At fixed `(x, y)`: HLS sum ≤ K · exp(-M · dist)**. -/
theorem hls_sum_at_pair_le_K_exp
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {y, z}
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ)) :=
  hls_sum_bound hd hf hβJ hβJd_lt

/-- **HLS sum at fixed `(0, y)` ≤ K · exp(-M · dist(0, y))**. -/
theorem hls_sum_at_zero_anchor_le_K_exp
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∀ y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {0, z} *
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {y, z}
        ≤ K * Real.exp (-M * (latticeDistance d 0 y : ℝ)) := by
  obtain ⟨K, M, hK_nn, hM_pos, h_bound⟩ := hls_sum_bound hd hf hβJ hβJd_lt
  exact ⟨K, M, hK_nn, hM_pos, fun y => h_bound 0 y⟩

/-- **HLS sum at antipode `(v, -v)` ≤ K · exp(-M · dist(v, -v))**. -/
theorem hls_sum_at_antipode_le_K_exp
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∀ v : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {v, z} *
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {-v, z}
        ≤ K * Real.exp (-M * (latticeDistance d v (-v) : ℝ)) := by
  obtain ⟨K, M, hK_nn, hM_pos, h_bound⟩ := hls_sum_bound hd hf hβJ hβJd_lt
  exact ⟨K, M, hK_nn, hM_pos, fun v => h_bound v (-v)⟩

/-- **HLS sum at diagonal `(x, x)` ≤ K** (since exp(-M · 0) = 1). -/
theorem hls_sum_at_diagonal_le_K
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ x : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
        ≤ K := by
  obtain ⟨K, M, hK_nn, _hM_pos, h_bound⟩ := hls_sum_bound hd hf hβJ hβJd_lt
  refine ⟨K, hK_nn, fun x => ?_⟩
  have h := h_bound x x
  have h_dist_self : (latticeDistance d x x : ℝ) = 0 := by
    simp [latticeDistance_self]
  rw [h_dist_self] at h
  simp only [mul_zero, Real.exp_zero, mul_one] at h
  exact h

/-- **Existential `K` for diagonal HLS sum**. -/
theorem hls_sum_diagonal_K_witness
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K : ℝ, 0 ≤ K := by
  obtain ⟨K, _, _⟩ := hls_sum_at_diagonal_le_K hd hf hβJ hβJd_lt
  exact ⟨K, by aesop⟩

end Ambient
end IsingModel
