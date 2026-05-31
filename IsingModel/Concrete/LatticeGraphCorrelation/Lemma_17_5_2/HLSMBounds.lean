import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSKBounds

/-!
# Substantive HLS M bounds bundle

GJ-proposition-unit bundle of M-rate-related inequality wrappers.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## M-positivity wrappers -/

/-- **Existential `M > 0` from HLS sum bound**. -/
theorem hls_M_pos
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ M : ℝ, 0 < M :=
  hls_final_M_witness hd hf hβJ hβJd_lt

/-- **At fixed `M`, the substantive HLS sum bound holds**. -/
theorem hls_sum_bound_with_M_witness
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ M : ℝ, 0 < M ∧
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ x y : Fin d → ℤ,
          ∑' z : Fin d → ℤ,
              correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
              correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {y, z}
          ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ)) := by
  obtain ⟨K, M, hK_nn, hM_pos, h_bound⟩ := hls_sum_bound hd hf hβJ hβJd_lt
  exact ⟨M, hM_pos, K, hK_nn, h_bound⟩

/-- **HLS decay rate from `-log(β·J·(2d))`**. -/
theorem hls_M_canonical_eq
    {β J : ℝ} {d : ℕ}
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ M : ℝ, M = -Real.log (β * J * ↑(2 * d)) ∧ 0 < M := by
  refine ⟨-Real.log (β * J * ↑(2 * d)), rfl, ?_⟩
  exact neg_log_betaJ_two_d_pos_of_strict_high_temp hβJd_pos hβJd_lt

/-- **Joint M positivity + canonical rate identity**. -/
theorem hls_M_pos_and_canonical
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (∃ M : ℝ, 0 < M) ∧
    (0 < -Real.log (β * J * ↑(2 * d))) := by
  have hd_pos : 0 < d := hd
  have h2d_pos : (0 : ℝ) < 2 * d := by positivity
  have hβJd_pos : 0 < β * J * (2 * d) := mul_pos hβJ h2d_pos
  exact ⟨hls_M_pos hd hf hβJ hβJd_lt,
         neg_log_betaJ_two_d_pos_of_strict_high_temp hβJd_pos hβJd_lt⟩

/-- **HLS sum decay rate `M` is positive**. -/
theorem hls_M_strict_pos
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ M : ℝ, 0 < M := by
  obtain ⟨_, M, _, hM_pos, _⟩ := hls_sum_bound hd hf hβJ hβJd_lt
  exact ⟨M, hM_pos⟩

end Ambient
end IsingModel
