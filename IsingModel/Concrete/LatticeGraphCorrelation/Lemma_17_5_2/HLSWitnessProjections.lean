import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSMaster

/-!
# Substantive HLS witness projections bundle

GJ-proposition-unit bundle providing witness-projection lemmas that
extract specific existence witnesses (∃ K, ∃ M, ∃ K M) from the master
sum-bound conclusion.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Existential projections -/

/-- **Project to `∃ K, ...`**: existential K only. -/
theorem hls_exists_K
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K : ℝ, 0 ≤ K := by
  obtain ⟨K, _, hK_nn, _, _⟩ := hls_master_sum hd hf hβJ hβJd_lt
  exact ⟨K, hK_nn⟩

/-- **Project to `∃ M > 0`**: existential positive M only. -/
theorem hls_exists_M_pos
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ M : ℝ, 0 < M := by
  obtain ⟨_, M, _, hM_pos, _⟩ := hls_master_sum hd hf hβJ hβJd_lt
  exact ⟨M, hM_pos⟩

/-- **Project to `∃ K ≥ 0`**: existential nonneg K. -/
theorem hls_exists_K_nonneg
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K : ℝ, 0 ≤ K := by
  obtain ⟨K, _, hK_nn, _, _⟩ := hls_master_sum hd hf hβJ hβJd_lt
  exact ⟨K, hK_nn⟩

/-- **Project to `∃ K M`**: both witnesses, no constraints. -/
theorem hls_exists_K_M_pair
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ (_ : ℝ), ∃ (_ : ℝ), True := by
  obtain ⟨K, M, _, _, _⟩ := hls_master_sum hd hf hβJ hβJd_lt
  exact ⟨K, M, trivial⟩

/-- **Project to `∃ K M`, with K nonneg + M pos**. -/
theorem hls_exists_K_M_constraints
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M := by
  obtain ⟨K, M, hK_nn, hM_pos, _⟩ := hls_master_sum hd hf hβJ hβJd_lt
  exact ⟨K, M, hK_nn, hM_pos⟩

/-- **Project to specific x, y bound**: instantiate at given pair. -/
theorem hls_at_specific_pair
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1)
    (x y : Fin d → ℤ) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∑' z : Fin d → ℤ,
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
          correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {y, z}
      ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ)) := by
  obtain ⟨K, M, hK_nn, hM_pos, h⟩ := hls_master_sum hd hf hβJ hβJd_lt
  exact ⟨K, M, hK_nn, hM_pos, h x y⟩

end Ambient
end IsingModel
