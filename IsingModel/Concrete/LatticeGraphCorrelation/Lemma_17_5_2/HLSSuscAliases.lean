import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSMaster

/-!
# Substantive HLS susc aliases bundle

GJ-proposition-unit bundle providing susceptibility-focused alias
combinations.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Susc-focused aliases -/

/-- **Susc bound from hypotheses**. -/
theorem hls_susc_from_hyps
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i : Fin d → ℤ) :
    susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
      ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) :=
  hls_master_susc hd hf hβJ hβJd_lt i

/-- **Susc + ferromag pair**. -/
theorem hls_susc_with_ferromag
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i : Fin d → ℤ) :
    (susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
      ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) ∧
    IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ) :=
  ⟨hls_master_susc hd hf hβJ hβJd_lt i, hf⟩

/-- **Susc + βJ positivity**. -/
theorem hls_susc_with_betaJ_pos
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i : Fin d → ℤ) :
    (susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
      ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) ∧
    0 < β * J :=
  ⟨hls_master_susc hd hf hβJ hβJd_lt i, hβJ⟩

/-- **Susc at two indices**. -/
theorem hls_susc_at_two_indices
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i j : Fin d → ℤ) :
    (susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
      ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) ∧
    (susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ j
      ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) :=
  ⟨hls_master_susc hd hf hβJ hβJd_lt i, hls_master_susc hd hf hβJ hβJd_lt j⟩

/-- **Susc + cluster pair**. -/
theorem hls_susc_with_cluster
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i : Fin d → ℤ) :
    (susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
      ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) ∧
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  ⟨hls_master_susc hd hf hβJ hβJd_lt i, hls_master_cluster hd hf hβJ hβJd_lt⟩

/-- **Susc + mass pair**. -/
theorem hls_susc_with_mass
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i : Fin d → ℤ) :
    (susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
      ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) ∧
    (0 < latticeMass d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  ⟨hls_master_susc hd hf hβJ hβJd_lt i, hls_master_mass hd hf hβJ hβJd_lt⟩

end Ambient
end IsingModel
