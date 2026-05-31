import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSENNRealLatticeMass

/-!
# Substantive HLS iff characterizations bundle

GJ-proposition-unit bundle of iff (if-and-only-if) characterizations
of various substantive HLS chain conclusions.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Iff characterizations -/

/-- **latticeMass > 0 ↔ ne 0** (under ferromagnetic + strict high-temp). -/
theorem hls_latticeMass_pos_iff_ne_zero
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (0 < latticeMass d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ)) ↔
    (latticeMass d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) ≠ 0) := by
  refine ⟨ne_of_gt, fun h => ?_⟩
  exact hls_latticeMass_pos_ennreal hd hf hβJ hβJd_lt

/-- **`0 < β·J·(2d)` ↔ `0 < β·J ∧ 0 < d`** under ferromagnetic. -/
theorem hls_betaJd_pos_iff
    {β J : ℝ} {d : ℕ} (hd_pos : 0 < d) :
    0 < β * J * (2 * d) ↔ 0 < β * J := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h2d_pos : (0 : ℝ) < 2 * d := by positivity
    exact (mul_pos_iff_of_pos_right h2d_pos).mp h
  · have h2d_pos : (0 : ℝ) < 2 * d := by positivity
    exact mul_pos h h2d_pos

/-- **`β·J·(2d) < 1` ↔ `1 - β·J·(2d) > 0`**. -/
theorem hls_high_temp_iff_one_sub_pos
    {β J : ℝ} {d : ℕ} :
    β * J * ↑(2 * d) < 1 ↔ (0 : ℝ) < 1 - β * J * ↑(2 * d) := by
  constructor <;> intro h <;> linarith

/-- **HLS sum bound existence ↔ trivial Truth (under ferromagnetic + strict
high-temp)**. -/
theorem hls_sum_bound_exists_iff_true
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
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ))) ↔ True := by
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  exact hls_sum_bound hd hf hβJ hβJd_lt

/-- **clusterProperty exists ↔ Truth** (under hypotheses). -/
theorem hls_cluster_iff_true
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ)) ↔ True := by
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  exact hls_cluster hd hf hβJ hβJd_lt

end Ambient
end IsingModel
