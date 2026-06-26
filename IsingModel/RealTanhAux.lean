import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Real hyperbolic-tangent sign helpers (shared low-level)

Mathlib does not export `Real.tanh_nonneg` / `Real.tanh_pos` as named lemmas.
These trivial sign facts are needed across three otherwise-disjoint `IsingModel`
hierarchies (`ClusterExpansion`, `Dobrushin`, `TransferMatrix`), so they live here
in a mathlib-only base module that all three can import without an import cycle
(this module imports nothing from `IsingModel`, so no cycle is possible).

See issue #4306 (cross-hierarchy generic-lemma de-duplication).
-/

namespace IsingModel

/-- **`Real.tanh` is non-negative for a non-negative argument**: `0 ≤ x → 0 ≤ Real.tanh x`.
Proved from `tanh = sinh / cosh` with `cosh > 0` and `sinh` non-negative on `[0, ∞)`. -/
theorem real_tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hx) (Real.cosh_pos x).le

/-- **`Real.tanh` is strictly positive for a positive argument**: `0 < x → 0 < Real.tanh x`.
Proved from `tanh = sinh / cosh` with `cosh > 0` and `sinh` strictly positive on `(0, ∞)`. -/
theorem real_tanh_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hx) (Real.cosh_pos x)

end IsingModel
