import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSMaster

/-!
# Substantive HLS high-temp pack bundle

GJ-proposition-unit bundle providing high-temperature-input-pack alias
combinations focused on the `β·J·(2d) < 1` constraint.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## High-temp pack aliases -/

/-- **High-temp pack triple**: ferromag + βJ pos + βJd lt 1. -/
theorem hls_high_temp_pack_triple
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ) ∧
    (0 < β * J) ∧
    (β * J * ↑(2 * d) < 1) :=
  ⟨hf, hβJ, hβJd_lt⟩

/-- **High-temp + cluster**. -/
theorem hls_high_temp_cluster
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (β * J * ↑(2 * d) < 1) ∧
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  ⟨hβJd_lt, hls_master_cluster hd hf hβJ hβJd_lt⟩

/-- **High-temp + mass**. -/
theorem hls_high_temp_mass
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (β * J * ↑(2 * d) < 1) ∧
    (0 < latticeMass d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  ⟨hβJd_lt, hls_master_mass hd hf hβJ hβJd_lt⟩

/-- **High-temp + decay**. -/
theorem hls_high_temp_decay
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (β * J * ↑(2 * d) < 1) ∧
    HasExponentialDecay d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) (-Real.log (β * J * ↑(2 * d))) :=
  ⟨hβJd_lt, hls_master_decay hd hf hβJ hβJd_lt⟩

/-- **High-temp + susc**. -/
theorem hls_high_temp_susc
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i : Fin d → ℤ) :
    (β * J * ↑(2 * d) < 1) ∧
    susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
      ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) :=
  ⟨hβJd_lt, hls_master_susc hd hf hβJ hβJd_lt i⟩

/-- **High-temp + sum bound**. -/
theorem hls_high_temp_sum
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (β * J * ↑(2 * d) < 1) ∧
    (∃ K M : ℝ, 0 ≤ K ∧ 0 < M ∧
      ∀ x y : Fin d → ℤ,
        ∑' z : Fin d → ℤ,
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} *
            correlationInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {y, z}
        ≤ K * Real.exp (-M * (latticeDistance d x y : ℝ))) :=
  ⟨hβJd_lt, hls_master_sum hd hf hβJ hβJd_lt⟩

end Ambient
end IsingModel
