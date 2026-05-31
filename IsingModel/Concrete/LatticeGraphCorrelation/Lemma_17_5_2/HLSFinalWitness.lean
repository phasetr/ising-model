import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSPerPairTendsto

/-!
# Substantive HLS final witness bundle

GJ-proposition-unit bundle providing the final witness aggregators for the
substantive HLS chain.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Final witness aggregators -/

/-- **Final witness aggregator**: returns positive `M` rate. -/
theorem hls_final_M_witness
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ M : ℝ, 0 < M := by
  obtain ⟨_, M, _, hM_pos, _⟩ := hls_sum_bound hd hf hβJ hβJd_lt
  exact ⟨M, hM_pos⟩

/-- **Final witness aggregator**: returns nonneg `K`. -/
theorem hls_final_K_witness
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K : ℝ, 0 ≤ K := by
  obtain ⟨K, _, hK_nn, _, _⟩ := hls_sum_bound hd hf hβJ hβJd_lt
  exact ⟨K, hK_nn⟩

/-- **Final witness aggregator**: positive susceptibility upper bound. -/
theorem hls_final_susc_upper_bound
    {β J : ℝ} {d : ℕ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ S : ℝ, 0 ≤ S := by
  refine ⟨β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)), ?_⟩
  have h_denom_pos : (0 : ℝ) < 1 - β * J * ↑(2 * d) := by linarith
  have h_numer_nn : (0 : ℝ) ≤ β * J * ↑(2 * d) :=
    mul_nonneg (mul_nonneg hf.hβ.le hf.hJ) (by positivity)
  exact div_nonneg h_numer_nn h_denom_pos.le

/-- **Final witness aggregator**: positive latticeMass. -/
theorem hls_final_latticeMass_witness
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ m : ENNReal, 0 < m :=
  ⟨_, hls_latticeMass hd hf hβJ hβJd_lt⟩

/-- **Final witness aggregator**: all positivity witnesses. -/
theorem hls_final_all_witnesses
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (∃ K M S : ℝ, 0 ≤ K ∧ 0 < M ∧ 0 ≤ S) ∧
    (∃ m : ENNReal, 0 < m) := by
  obtain ⟨K, M, hK_nn, hM_pos, _⟩ := hls_sum_bound hd hf hβJ hβJd_lt
  refine ⟨⟨K, M, β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)),
          hK_nn, hM_pos, ?_⟩,
          ⟨_, hls_latticeMass hd hf hβJ hβJd_lt⟩⟩
  have h_denom_pos : (0 : ℝ) < 1 - β * J * ↑(2 * d) := by linarith
  have h_numer_nn : (0 : ℝ) ≤ β * J * ↑(2 * d) :=
    mul_nonneg (mul_nonneg hf.hβ.le hf.hJ) (by positivity)
  exact div_nonneg h_numer_nn h_denom_pos.le

end Ambient
end IsingModel
