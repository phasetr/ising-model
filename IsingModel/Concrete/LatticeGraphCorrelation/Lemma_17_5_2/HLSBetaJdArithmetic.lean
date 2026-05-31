import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSHypothesisExtracts

/-!
# Substantive HLS βJ·(2d) arithmetic bundle

GJ-proposition-unit bundle providing arithmetic properties of
`β·J·(2d)` and its complement `1 - β·J·(2d)` in the high-temperature
regime `β·J·(2d) < 1`.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## βJ·2d arithmetic -/

/-- **`1 - β·J·(2d) > 0`** from high temp. -/
theorem hls_one_sub_betaJd_pos
    {d : ℕ} {β J : ℝ}
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    0 < 1 - β * J * ↑(2 * d) := by linarith

/-- **`1 - β·J·(2d) ≠ 0`**. -/
theorem hls_one_sub_betaJd_ne_zero
    {d : ℕ} {β J : ℝ}
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    1 - β * J * ↑(2 * d) ≠ 0 :=
  (hls_one_sub_betaJd_pos hβJd_lt).ne'

/-- **`1 - β·J·(2d) ≥ 0`**. -/
theorem hls_one_sub_betaJd_nonneg
    {d : ℕ} {β J : ℝ}
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    0 ≤ 1 - β * J * ↑(2 * d) :=
  (hls_one_sub_betaJd_pos hβJd_lt).le

/-- **`β·J·(2d) < 1` ↔ `0 < 1 - β·J·(2d)`**. -/
theorem hls_betaJd_lt_one_iff
    {d : ℕ} {β J : ℝ} :
    β * J * ↑(2 * d) < 1 ↔ 0 < 1 - β * J * ↑(2 * d) := by
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **Ratio positivity**: `β·J·(2d) / (1 - β·J·(2d)) ≥ 0` under high-temp and ferromag. -/
theorem hls_betaJd_ratio_nonneg
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    0 ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) :=
  div_nonneg (hls_extract_betaJd_nonneg hf)
    (hls_one_sub_betaJd_nonneg hβJd_lt)

/-- **βJ·2d ≤ 1**. -/
theorem hls_betaJd_le_one
    {d : ℕ} {β J : ℝ}
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    β * J * ↑(2 * d) ≤ 1 :=
  hβJd_lt.le

/-- **Complement triple**: `0 < 1-βJ·2d ∧ βJ·2d ≤ 1 ∧ 1-βJ·2d ≠ 0`. -/
theorem hls_complement_triple
    {d : ℕ} {β J : ℝ}
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (0 < 1 - β * J * ↑(2 * d)) ∧
    (β * J * ↑(2 * d) ≤ 1) ∧
    (1 - β * J * ↑(2 * d) ≠ 0) :=
  ⟨hls_one_sub_betaJd_pos hβJd_lt,
   hls_betaJd_le_one hβJd_lt,
   hls_one_sub_betaJd_ne_zero hβJd_lt⟩

end Ambient
end IsingModel
