import IsingModel.Conditioning.CorrelationRates.Summaries

/-!
# Correlation rates split — high-temperature parameter and its lower bound

Part of the split high-temperature correlation-rates layer (Issue #1850).
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **High-temperature parameter**: `t = tanh(βJ)`.
For `βJ ≥ 0`, `t ∈ [0, 1)`, and the high-temperature expansion
converges when `t` is small. -/
noncomputable def highTempParam (β J : ℝ) : ℝ := Real.tanh (β * J)

/-- The high-temperature parameter satisfies `|t| < 1` for all finite `βJ`. -/
theorem abs_highTempParam_lt_one (β J : ℝ) :
    |highTempParam β J| < 1 := by
  unfold highTempParam
  exact abs_tanh_lt_one (β * J)

/-- The high-temperature parameter is strictly less than 1. -/
theorem highTempParam_lt_one (β J : ℝ) :
    highTempParam β J < 1 := by
  unfold highTempParam
  exact tanh_lt_one (β * J)

/-- **`highTempParam` is nonneg under `0 ≤ β·J`**: `0 ≤ tanh(β·J)`. -/
theorem highTempParam_nonneg {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 ≤ highTempParam β J := by
  unfold highTempParam
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le

/-- **`highTempParam` is strictly positive under `0 < β·J`**: `0 < tanh(β·J)`. -/
theorem highTempParam_pos {β J : ℝ} (hβJ : 0 < β * J) :
    0 < highTempParam β J := by
  unfold highTempParam
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hβJ) (Real.cosh_pos _)

/-- **`highTempParam` vanishes at `β = 0`**: `highTempParam 0 J = 0`. -/
@[simp] theorem highTempParam_at_beta_zero (J : ℝ) :
    highTempParam 0 J = 0 := by
  unfold highTempParam; rw [zero_mul]; exact Real.tanh_zero

/-- **`highTempParam` vanishes at `J = 0`**: `highTempParam β 0 = 0`. -/
@[simp] theorem highTempParam_at_J_zero (β : ℝ) :
    highTempParam β 0 = 0 := by
  unfold highTempParam; rw [mul_zero]; exact Real.tanh_zero

/-- **Pair correlation single-edge `highTempParam` lower bound**:
restatement of Step 386 in terms of `highTempParam`. Under `0 ≤ β·J`
and an edge `s(i, j) ∈ G.edgeSet`,
`⟨σ_iσ_j⟩^{⟨J,0,β⟩} ≥ highTempParam β J / 2^|E|`. -/
theorem correlation_high_temp_h_zero_at_pair_ge_highTempParam_div_two_pow_edges
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J)
    (i j : ι) (hij : i ≠ j) (he : s(i, j) ∈ G.edgeSet) :
    highTempParam β J / (2 : ℝ) ^ G.edgeFinset.card
      ≤ correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) := by
  unfold highTempParam
  exact correlation_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    G J β hβJ i j hij he


end IsingModel
