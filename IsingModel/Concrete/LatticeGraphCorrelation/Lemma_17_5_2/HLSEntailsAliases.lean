import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSMaster

/-!
# Substantive HLS entails aliases bundle

GJ-proposition-unit bundle providing `entails_*` style aliases.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Entails-style aliases -/

/-- **Entails: HLS cluster**. -/
theorem entails_hls_cluster
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  hls_master_cluster hd hf hβJ hβJd_lt

/-- **Entails: HLS mass positive**. -/
theorem entails_hls_mass_positive
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    0 < latticeMass d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  hls_master_mass hd hf hβJ hβJd_lt

/-- **Entails: HLS decay**. -/
theorem entails_hls_decay
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    HasExponentialDecay d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) (-Real.log (β * J * ↑(2 * d))) :=
  hls_master_decay hd hf hβJ hβJd_lt

/-- **Entails: HLS susc**. -/
theorem entails_hls_susc
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i : Fin d → ℤ) :
    susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
      ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) :=
  hls_master_susc hd hf hβJ hβJd_lt i

/-- **Entails: HLS sum**. -/
theorem entails_hls_sum
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
  hls_master_sum hd hf hβJ hβJd_lt

/-- **Entails: HLS master**. -/
theorem entails_hls_master
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
  hls_master hd hf hβJ hβJd_lt

end Ambient
end IsingModel
