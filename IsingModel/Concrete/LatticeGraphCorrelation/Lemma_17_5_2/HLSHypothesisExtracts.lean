import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSMaster

/-!
# Substantive HLS hypothesis extracts bundle

GJ-proposition-unit bundle providing extraction lemmas that derive
elementary properties from the master hypothesis set (ferromagnetic,
high-temperature bounds).

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Hypothesis extractions -/

/-- **Extract `0 ≤ J`** from ferromagnetic. -/
theorem hls_extract_J_nonneg
    {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ)) :
    0 ≤ J :=
  hf.hJ

/-- **Extract `0 < β`** from ferromagnetic. -/
theorem hls_extract_beta_pos
    {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ)) :
    0 < β :=
  hf.hβ

/-- **Extract `0 ≤ β`** from ferromagnetic. -/
theorem hls_extract_beta_nonneg
    {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ)) :
    0 ≤ β :=
  hf.hβ.le

/-- **Extract `β ≠ 0`** from ferromagnetic. -/
theorem hls_extract_beta_ne_zero
    {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ)) :
    β ≠ 0 :=
  hf.hβ.ne'

/-- **Extract `0 ≤ β·J`** from ferromagnetic. -/
theorem hls_extract_betaJ_nonneg
    {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ)) :
    0 ≤ β * J :=
  mul_nonneg hf.hβ.le hf.hJ

/-- **Extract `0 ≤ β·J·(2d)`** from ferromagnetic. -/
theorem hls_extract_betaJd_nonneg
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ)) :
    0 ≤ β * J * ↑(2 * d) :=
  mul_nonneg (hls_extract_betaJ_nonneg hf) (by positivity)

/-- **Combined hypothesis triple**: J ≥ 0, β > 0, β·J ≥ 0. -/
theorem hls_extract_hypothesis_triple
    {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ)) :
    0 ≤ J ∧ 0 < β ∧ 0 ≤ β * J :=
  ⟨hf.hJ, hf.hβ, hls_extract_betaJ_nonneg hf⟩

end Ambient
end IsingModel
