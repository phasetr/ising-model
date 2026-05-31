import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBetaJdArithmetic

/-!
# Substantive HLS hypothesis strengthenings bundle

GJ-proposition-unit bundle providing strengthened hypothesis statements
that consolidate multiple input conditions for master theorem invocation.

**Reference:** Glimm-Jaffe §17.5.
-/

namespace IsingModel
namespace Ambient

open IsingModel

/-! ## Strengthened hypotheses -/

/-- **Strengthened ferromagnetic + high temp**: package full input set. -/
theorem hls_hypothesis_package
    {d : ℕ} {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ)) ∧
    (0 < β * J) ∧
    (β * J * ↑(2 * d) < 1) ∧
    (0 ≤ J) ∧
    (0 < β) ∧
    (0 ≤ β * J) ∧
    (0 < 1 - β * J * ↑(2 * d)) :=
  ⟨hf, hβJ, hβJd_lt, hf.hJ, hf.hβ, mul_nonneg hf.hβ.le hf.hJ,
   hls_one_sub_betaJd_pos hβJd_lt⟩

/-- **Strict strengthening to βJ > 0**: from `0 < β` and `0 < β·J`. -/
theorem hls_betaJ_pos_implies_J_pos
    {β J : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ : 0 < β * J) :
    0 < J := by
  have hβ_pos : (0 : ℝ) < β := hf.hβ
  have hJ_nn : (0 : ℝ) ≤ J := hf.hJ
  rcases lt_or_eq_of_le hJ_nn with hJ_pos | hJ_zero
  · exact hJ_pos
  · exfalso
    have : β * J = 0 := by rw [← hJ_zero]; ring
    linarith

/-- **βJ ≠ 0** from `0 < β·J`. -/
theorem hls_betaJ_ne_zero
    {β J : ℝ}
    (hβJ : 0 < β * J) :
    β * J ≠ 0 :=
  hβJ.ne'

/-- **βJ·(2d) ne zero** under high-temp + ferromag + d ≥ 1. -/
theorem hls_betaJd_ne_zero
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hβJ : 0 < β * J) :
    β * J * ↑(2 * d) ≠ 0 := by
  have hd_pos : 0 < d := hd
  have h2d_pos : (0 : ℝ) < ↑(2 * d) := by
    push_cast
    positivity
  exact (mul_pos hβJ h2d_pos).ne'

/-- **βJ·(2d) positive** under high-temp + ferromag + d ≥ 1. -/
theorem hls_betaJd_pos
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hβJ : 0 < β * J) :
    0 < β * J * ↑(2 * d) := by
  have hd_pos : 0 < d := hd
  have h2d_pos : (0 : ℝ) < ↑(2 * d) := by
    push_cast
    positivity
  exact mul_pos hβJ h2d_pos

/-- **Strict bounds package**: `0 < β·J·(2d) < 1` combined. -/
theorem hls_strict_bounds_pair
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ}
    (hβJ : 0 < β * J)
    (hβJd_lt : β * J * ↑(2 * d) < 1) :
    (0 < β * J * ↑(2 * d)) ∧ (β * J * ↑(2 * d) < 1) :=
  ⟨hls_betaJd_pos hd hβJ, hβJd_lt⟩

end Ambient
end IsingModel
