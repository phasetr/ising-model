import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSMaster

/-!
# Substantive HLS cluster aliases bundle

GJ-proposition-unit bundle providing cluster-property-focused alias
combinations of the substantive HLS conclusions.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Cluster-focused aliases -/

/-- **Cluster from high-temp + ferromag**: simplest exposure. -/
theorem hls_cluster_from_hyps
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  hls_master_cluster hd hf hβJ hβJd_lt

/-- **Cluster + ferromag pair**. -/
theorem hls_cluster_with_ferromag
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ) :=
  ⟨hls_master_cluster hd hf hβJ hβJd_lt, hf⟩

/-- **Cluster + βJ positivity**. -/
theorem hls_cluster_with_betaJ_pos
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    0 < β * J :=
  ⟨hls_master_cluster hd hf hβJ hβJd_lt, hβJ⟩

/-- **Cluster + βJ·(2d) < 1**. -/
theorem hls_cluster_with_betaJd_lt
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    β * J * ↑(2 * d) < 1 :=
  ⟨hls_master_cluster hd hf hβJ hβJd_lt, hβJd_lt⟩

/-- **Cluster + mass + βJd<1 triple**. -/
theorem hls_cluster_mass_betaJd_lt
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    (0 < latticeMass d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ)) ∧
    β * J * ↑(2 * d) < 1 :=
  ⟨hls_master_cluster hd hf hβJ hβJd_lt,
   hls_master_mass hd hf hβJ hβJd_lt,
   hβJd_lt⟩

/-- **Cluster + decay + ferromag triple**. -/
theorem hls_cluster_decay_ferromag
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    HasExponentialDecay d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) (-Real.log (β * J * ↑(2 * d))) ∧
    IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ) :=
  ⟨hls_master_cluster hd hf hβJ hβJd_lt,
   hls_master_decay hd hf hβJ hβJd_lt,
   hf⟩

end Ambient
end IsingModel
