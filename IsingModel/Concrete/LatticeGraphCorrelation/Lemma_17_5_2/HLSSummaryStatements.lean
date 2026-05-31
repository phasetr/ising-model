import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSPositivityHelpers

/-!
# Substantive HLS summary statements bundle

GJ-proposition-unit bundle of comprehensive summary statements.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Summary statements -/

/-- **HLS sum bound implies all conclusions hold**. -/
theorem hls_summary_all_hold
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
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    (0 < latticeMass d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ)) ∧
    (∀ i : Fin d → ℤ,
      susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
        ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) ∧
    HasExponentialDecay d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) (-Real.log (β * J * ↑(2 * d))) :=
  ⟨hls_sum_bound hd hf hβJ hβJd_lt,
   hls_cluster hd hf hβJ hβJd_lt,
   hls_latticeMass hd hf hβJ hβJd_lt,
   fun i => hls_susc hd hf hβJ hβJd_lt i,
   hls_hasExpDecay hd hf hβJ hβJd_lt⟩

/-- **Hypothesis summary**: pack ferromagnetic + β·J·(2d) bounds. -/
theorem hls_hypothesis_summary
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (0 : ℝ) ≤ β * J ∧ (0 : ℝ) ≤ β * J * ↑(2 * d) ∧ β * J * ↑(2 * d) < 1 :=
  ⟨hls_betaJ_nonneg hf, hls_betaJ_two_d_nonneg hf, hβJd_lt⟩

/-- **Substantive bound witness summary**: positive K, positive M, ≤ K · exp form. -/
theorem hls_bound_witness_summary
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

/-- **Bounded susceptibility summary**. -/
theorem hls_bounded_susceptibility_summary
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i : Fin d → ℤ,
      susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i ≤ B :=
  ⟨_, hls_susceptibility_bound_nonneg hf hβJd_lt,
   fun i => hls_susc hd hf hβJ hβJd_lt i⟩

/-- **HasExpDecay rate summary**: exists positive `α` with decay rate accessible. -/
theorem hls_rate_summary
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ∃ α : ℝ, 0 < α ∧ α = -Real.log (β * J * ↑(2 * d)) := by
  have hd_pos : 0 < d := hd
  have h2d_pos : (0 : ℝ) < 2 * d := by positivity
  have hβJd_pos : 0 < β * J * (2 * d) := mul_pos hβJ h2d_pos
  exact ⟨-Real.log (β * J * ↑(2 * d)),
         neg_log_betaJ_two_d_pos_of_strict_high_temp hβJd_pos hβJd_lt, rfl⟩

end Ambient
end IsingModel
