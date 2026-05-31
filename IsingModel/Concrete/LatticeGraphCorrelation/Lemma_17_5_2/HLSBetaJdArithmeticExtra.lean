import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBetaJdArithmetic

/-!
# Substantive HLS βJ·(2d) arithmetic extra bundle

GJ-proposition-unit bundle providing extra arithmetic identities for
`β·J·(2d)` and its complement.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Extra βJd arithmetic -/

/-- **`1 - β·J·(2d) ≤ 1`** (since βJd ≥ 0 in ferromag). -/
theorem hls_one_sub_betaJd_le_one
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ)) :
    1 - β * J * ↑(2 * d) ≤ 1 := by
  have hβJd_nn : 0 ≤ β * J * ↑(2 * d) :=
    mul_nonneg (mul_nonneg hf.hβ.le hf.hJ) (by positivity)
  linarith

/-- **`1 - β·J·(2d) ∈ (0, 1]`** combined. -/
theorem hls_one_sub_betaJd_mem_Ioc
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    1 - β * J * ↑(2 * d) ∈ Set.Ioc (0 : ℝ) 1 :=
  ⟨hls_one_sub_betaJd_pos hβJd_lt, hls_one_sub_betaJd_le_one hf⟩

/-- **β·J·(2d) ∈ [0, 1)** combined. -/
theorem hls_betaJd_mem_Ico
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    β * J * ↑(2 * d) ∈ Set.Ico (0 : ℝ) 1 :=
  ⟨mul_nonneg (mul_nonneg hf.hβ.le hf.hJ) (by positivity), hβJd_lt⟩

/-- **βJd squared**: `0 ≤ (β·J·(2d))^2 < 1` under high-temp. -/
theorem hls_betaJd_sq_bounds
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    0 ≤ (β * J * ↑(2 * d)) ^ 2 ∧ (β * J * ↑(2 * d)) ^ 2 < 1 := by
  refine ⟨sq_nonneg _, ?_⟩
  have hβJd_nn : 0 ≤ β * J * ↑(2 * d) :=
    mul_nonneg (mul_nonneg hf.hβ.le hf.hJ) (by positivity)
  calc (β * J * ↑(2 * d)) ^ 2 = β * J * ↑(2 * d) * (β * J * ↑(2 * d)) := sq (β * J * ↑(2 * d)) ▸ rfl
    _ < 1 * 1 := by
      apply mul_lt_mul' hβJd_lt.le hβJd_lt hβJd_nn (by linarith)
    _ = 1 := by ring

/-- **Ratio bound**: `β·J·(2d)/(1 - β·J·(2d)) ≤ β·J·(2d)/0⁺` — needs the denominator > 0. -/
theorem hls_betaJd_ratio_pos_iff
    {d : ℕ} {β J : ℝ}
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (0 ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) ↔
      (0 ≤ β * J * ↑(2 * d)) := by
  rw [div_nonneg_iff]
  refine ⟨?_, ?_⟩
  · rintro (⟨h1, _⟩ | ⟨h1, h2⟩)
    · exact h1
    · linarith [hls_one_sub_betaJd_pos hβJd_lt]
  · intro h
    left
    exact ⟨h, hls_one_sub_betaJd_nonneg hβJd_lt⟩

/-- **βJd-form ratio at zero**: ratio = 0 iff numerator = 0. -/
theorem hls_betaJd_ratio_zero_iff
    {d : ℕ} {β J : ℝ}
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) = 0 ↔
      β * J * ↑(2 * d) = 0 := by
  rw [div_eq_zero_iff]
  refine ⟨?_, ?_⟩
  · rintro (h | h)
    · exact h
    · exfalso; exact (hls_one_sub_betaJd_ne_zero hβJd_lt) h
  · intro h; left; exact h

end Ambient
end IsingModel
