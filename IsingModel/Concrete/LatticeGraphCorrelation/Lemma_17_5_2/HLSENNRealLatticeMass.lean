import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSMBounds

/-!
# Substantive HLS ENNReal latticeMass wrappers

GJ-proposition-unit bundle of ENNReal-form latticeMass wrappers.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## ENNReal latticeMass wrappers -/

/-- **latticeMass > 0 in ENNReal**. -/
theorem hls_latticeMass_pos_ennreal
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (0 : ENNReal) < latticeMass d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  hls_latticeMass hd hf hβJ hβJd_lt

/-- **latticeMass ≠ 0 in ENNReal**. -/
theorem hls_latticeMass_ne_zero_ennreal
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    latticeMass d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) ≠ 0 :=
  ne_of_gt (hls_latticeMass_pos_ennreal hd hf hβJ hβJd_lt)

/-- **latticeMass > ⊥** trivially from latticeMass > 0. -/
theorem hls_latticeMass_gt_bot
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (⊥ : ENNReal) < latticeMass d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) := by
  have h := hls_latticeMass_pos_ennreal hd hf hβJ hβJd_lt
  simpa using h

/-- **0 ≤ latticeMass in ENNReal** (trivial). -/
theorem hls_latticeMass_nonneg_ennreal
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β J : ℝ} :
    (0 : ENNReal) ≤ latticeMass d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) := bot_le

/-- **latticeMass for any exhaustion is > 0** (gen variant). -/
theorem hls_latticeMass_pos_ennreal_gen
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (0 : ENNReal) < latticeMass d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  hls_latticeMass_pos_gen hd Λ hf hβJ hβJd_lt

end Ambient
end IsingModel
