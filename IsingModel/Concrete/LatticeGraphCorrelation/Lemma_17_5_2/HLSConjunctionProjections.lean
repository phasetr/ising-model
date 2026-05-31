import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSConjunctions

/-!
# Substantive HLS conjunction projections bundle

GJ-proposition-unit bundle providing conjunction-projection lemmas
extracting from the various aggregate conjunction theorems.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Projections from `mass_cluster_susc` -/

/-- **From `mass_cluster_susc`: extract mass**. -/
theorem hls_mcs_mass
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    0 < latticeMass d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  (hls_mass_cluster_susc hd hf hβJ hβJd_lt).1

/-- **From `mass_cluster_susc`: extract cluster**. -/
theorem hls_mcs_cluster
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  (hls_mass_cluster_susc hd hf hβJ hβJd_lt).2.1

/-- **From `mass_cluster_susc`: extract susc**. -/
theorem hls_mcs_susc
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i : Fin d → ℤ) :
    susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
      ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) :=
  (hls_mass_cluster_susc hd hf hβJ hβJd_lt).2.2 i

/-! ## Projections from `cluster_decay_susc` -/

/-- **From `cluster_decay_susc`: extract cluster**. -/
theorem hls_cds_cluster
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  (hls_cluster_decay_susc hd hf hβJ hβJd_lt).1

/-- **From `cluster_decay_susc`: extract decay**. -/
theorem hls_cds_decay
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    HasExponentialDecay d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) (-Real.log (β * J * ↑(2 * d))) :=
  (hls_cluster_decay_susc hd hf hβJ hβJd_lt).2.1

/-- **From `cluster_decay_susc`: extract susc**. -/
theorem hls_cds_susc
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i : Fin d → ℤ) :
    susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
      ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) :=
  (hls_cluster_decay_susc hd hf hβJ hβJd_lt).2.2 i

end Ambient
end IsingModel
