import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSMaster

/-!
# Substantive HLS iff-form bundle

GJ-proposition-unit bundle providing iff-form characterizations: under the
standard hypotheses, certain conditions hold *iff* `True` (since they are
all provable). These are trivial-but-distinct phrasings useful for
tactic-driven proof flows.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Iff-form characterizations -/

/-- **Cluster iff True**. -/
theorem hls_cluster_iff_true_v2
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) ↔ True :=
  ⟨fun _ => trivial, fun _ => hls_master_cluster hd hf hβJ hβJd_lt⟩

/-- **Mass positive iff True**. -/
theorem hls_mass_pos_iff_true
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (0 < latticeMass d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ)) ↔ True :=
  ⟨fun _ => trivial, fun _ => hls_master_mass hd hf hβJ hβJd_lt⟩

/-- **Decay iff True**. -/
theorem hls_decay_iff_true
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    HasExponentialDecay d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) (-Real.log (β * J * ↑(2 * d))) ↔ True :=
  ⟨fun _ => trivial, fun _ => hls_master_decay hd hf hβJ hβJd_lt⟩

/-- **Susc bound iff True (parameterized)**. -/
theorem hls_susc_iff_true
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1)
    (i : Fin d → ℤ) :
    (susceptibilityInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ i
      ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) ↔ True :=
  ⟨fun _ => trivial, fun _ => hls_master_susc hd hf hβJ hβJd_lt i⟩

/-- **Combined `mass+cluster` iff True**. -/
theorem hls_mass_and_cluster_iff_true
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    ((0 < latticeMass d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ)) ∧
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ)) ↔ True :=
  ⟨fun _ => trivial,
   fun _ => ⟨hls_master_mass hd hf hβJ hβJd_lt,
             hls_master_cluster hd hf hβJ hβJd_lt⟩⟩

/-- **Combined `decay+cluster` iff True**. -/
theorem hls_decay_and_cluster_iff_true
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (HasExponentialDecay d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) (-Real.log (β * J * ↑(2 * d))) ∧
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ)) ↔ True :=
  ⟨fun _ => trivial,
   fun _ => ⟨hls_master_decay hd hf hβJ hβJd_lt,
             hls_master_cluster hd hf hβJ hβJd_lt⟩⟩

end Ambient
end IsingModel
