import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSMaster

/-!
# Substantive HLS named tag bundle

GJ-proposition-unit bundle providing named-tag aliases (`gj_*` prefix)
denoting GJ §17.5 references.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## GJ-tagged accessors -/

/-- **GJ §17.5 cluster property statement**. -/
theorem gj_17_5_cluster
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  hls_master_cluster hd hf hβJ hβJd_lt

/-- **GJ §17.5 positive mass**. -/
theorem gj_17_5_mass_positive
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    0 < latticeMass d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  hls_master_mass hd hf hβJ hβJd_lt

/-- **GJ §17.5 exponential decay**. -/
theorem gj_17_5_exp_decay
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    HasExponentialDecay d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) (-Real.log (β * J * ↑(2 * d))) :=
  hls_master_decay hd hf hβJ hβJd_lt

/-- **GJ §17.5 finite susceptibility**. -/
theorem gj_17_5_susc_finite
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i : Fin d → ℤ) :
    susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
      ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) :=
  hls_master_susc hd hf hβJ hβJd_lt i

/-- **GJ §17.5 HLS sum bound**. -/
theorem gj_17_5_hls_sum_bound
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

/-- **GJ §17.5 master statement**. -/
theorem gj_17_5_master
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
