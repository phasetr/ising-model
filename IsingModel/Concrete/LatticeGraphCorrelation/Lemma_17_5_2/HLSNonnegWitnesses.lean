import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSMaster

/-!
# Substantive HLS nonneg witness bundle

GJ-proposition-unit bundle providing nonneg/positivity witness extractions
and algebraic positivity statements derived from the master HLS conclusions.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Positivity witnesses -/

/-- **`latticeMass` nonneg** (from positivity). -/
theorem hls_mass_nonneg
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    0 ≤ latticeMass d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  (hls_master_mass hd hf hβJ hβJd_lt).le

/-- **`latticeMass` ne zero** (from positivity). -/
theorem hls_mass_ne_zero
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    latticeMass d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) ≠ 0 :=
  (hls_master_mass hd hf hβJ hβJd_lt).ne'

/-- **`susceptibility` nonneg upper bound** from the master susc bound. -/
theorem hls_susc_le_nonneg_bound
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i : Fin d → ℤ) :
    0 ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) ∧
    susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
      ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) := by
  refine ⟨?_, hls_master_susc hd hf hβJ hβJd_lt i⟩
  apply div_nonneg
  · positivity
  · linarith

/-- **Log rate positivity**: `-log(β·J·(2d)) > 0`. -/
theorem hls_log_rate_pos
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    0 < -Real.log (β * J * ↑(2 * d)) := by
  have hd_pos : 0 < d := hd
  have h2d_pos : (0 : ℝ) < 2 * d := by positivity
  have hβJd_pos : 0 < β * J * ↑(2 * d) := by
    push_cast
    exact mul_pos hβJ h2d_pos
  have h_log : Real.log (β * J * ↑(2 * d)) < 0 :=
    Real.log_neg hβJd_pos hβJd_lt
  linarith

/-- **Log rate nonneg**. -/
theorem hls_log_rate_nonneg
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    0 ≤ -Real.log (β * J * ↑(2 * d)) :=
  (hls_log_rate_pos hd hβJ hβJd_lt).le

/-- **Susc bound + log rate positive** combined. -/
theorem hls_susc_bound_and_log_rate_pos
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i : Fin d → ℤ) :
    (susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
      ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) ∧
    0 < -Real.log (β * J * ↑(2 * d)) :=
  ⟨hls_master_susc hd hf hβJ hβJd_lt i, hls_log_rate_pos hd hβJ hβJd_lt⟩

end Ambient
end IsingModel
