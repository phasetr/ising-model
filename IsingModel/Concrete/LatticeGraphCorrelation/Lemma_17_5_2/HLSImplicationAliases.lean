import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSMaster

/-!
# Substantive HLS implication aliases bundle

GJ-proposition-unit bundle providing arrow-shape implication aliases.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Implication aliases -/

/-- **`ferromag → β·J pos → high-temp → cluster`**. -/
theorem hls_implication_to_cluster
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ} :
    IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ) →
    0 < β * J →
    β * J * ↑(2 * d) < 1 →
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  fun hf hβJ hβJd_lt => hls_master_cluster hd hf hβJ hβJd_lt

/-- **`ferromag → β·J pos → high-temp → mass`**. -/
theorem hls_implication_to_mass
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ} :
    IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ) →
    0 < β * J →
    β * J * ↑(2 * d) < 1 →
    0 < latticeMass d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  fun hf hβJ hβJd_lt => hls_master_mass hd hf hβJ hβJd_lt

/-- **`ferromag → β·J pos → high-temp → decay`**. -/
theorem hls_implication_to_decay
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ} :
    IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ) →
    0 < β * J →
    β * J * ↑(2 * d) < 1 →
    HasExponentialDecay d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) (-Real.log (β * J * ↑(2 * d))) :=
  fun hf hβJ hβJd_lt => hls_master_decay hd hf hβJ hβJd_lt

/-- **`(hf ∧ hβJ ∧ hβJd_lt) → cluster`** packed-arrow version. -/
theorem hls_packed_implication_to_cluster
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ} :
    (IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ) ∧
     (0 < β * J) ∧
     (β * J * ↑(2 * d) < 1)) →
    clusterProperty (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  fun ⟨hf, hβJ, hβJd_lt⟩ => hls_master_cluster hd hf hβJ hβJd_lt

/-- **`(hf ∧ hβJ ∧ hβJd_lt) → mass`** packed-arrow. -/
theorem hls_packed_implication_to_mass
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ} :
    (IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ) ∧
     (0 < β * J) ∧
     (β * J * ↑(2 * d) < 1)) →
    0 < latticeMass d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  fun ⟨hf, hβJ, hβJd_lt⟩ => hls_master_mass hd hf hβJ hβJd_lt

/-- **`(hf ∧ hβJ ∧ hβJd_lt) → decay`** packed-arrow. -/
theorem hls_packed_implication_to_decay
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ} :
    (IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ) ∧
     (0 < β * J) ∧
     (β * J * ↑(2 * d) < 1)) →
    HasExponentialDecay d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) (-Real.log (β * J * ↑(2 * d))) :=
  fun ⟨hf, hβJ, hβJd_lt⟩ => hls_master_decay hd hf hβJ hβJd_lt

end Ambient
end IsingModel
