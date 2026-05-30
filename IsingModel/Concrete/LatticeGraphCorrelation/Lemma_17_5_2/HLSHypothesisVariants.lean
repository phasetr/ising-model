import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSCrossReference

/-!
# Substantive HLS alternative hypothesis variants

GJ-proposition-unit bundle exposing the substantive HLS conclusions under
various equivalent or stronger hypothesis sets.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Stronger-hypothesis variants -/

/-- **From explicit `0 < β·J`** (slightly stronger than ferromagnetic). -/
theorem hls_substantive_of_betaJ_pos
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
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ)) := by
  have hd_pos : 0 < d := hd
  have h2d_pos : (0 : ℝ) < 2 * d := by positivity
  have hβJd_pos : 0 < β * J * (2 * d) := mul_pos hβJ h2d_pos
  exact hls_final_main hd hf hβJd_pos hβJd_lt

/-- **From `Ferromagnetic` + `0 < J`** (then β·J > 0 since β > 0). -/
theorem hls_substantive_of_J_pos
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hJ_pos : 0 < J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {y, z}
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ)) := by
  have hβJ : 0 < β * J := mul_pos hf.hβ hJ_pos
  exact hls_substantive_of_betaJ_pos hd hf hβJ hβJd_lt

/-! ## Joint cluster + susceptibility from various hypothesis sets -/

/-- **Joint cluster + susceptibility from `0 < β·J`**. -/
theorem hls_cluster_susceptibility_of_betaJ_pos
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    (∀ i : Fin d → ℤ,
      susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
        ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) := by
  have hd_pos : 0 < d := hd
  have h2d_pos : (0 : ℝ) < 2 * d := by positivity
  have hβJd_pos : 0 < β * J * (2 * d) := mul_pos hβJ h2d_pos
  exact ⟨hls_final_cluster hd hf hβJd_pos hβJd_lt,
         fun i => hls_final_susceptibility hd hf hβJd_pos hβJd_lt i⟩

/-! ## latticeMass + all from `0 < β·J` -/

/-- **All-in-one from `0 < β·J`** (single-hypothesis variant). -/
theorem hls_all_in_one_of_betaJ_pos
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (0 < latticeMass d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ)) ∧
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    (∀ i : Fin d → ℤ,
      susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
        ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) ∧
    (∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {y, z}
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ))) ∧
    HasExponentialDecay d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) (-Real.log (β * J * ↑(2 * d))) := by
  have hd_pos : 0 < d := hd
  have h2d_pos : (0 : ℝ) < 2 * d := by positivity
  have hβJd_pos : 0 < β * J * (2 * d) := mul_pos hβJ h2d_pos
  exact hls_final_all_in_one hd hf hβJd_pos hβJd_lt

end Ambient
end IsingModel
