import IsingModel.PseudoMass.FromParamsHZero.HZeroTruncatedBounds

/-!
# Pseudo-mass J-zero value cases

Closed-form value wrappers for `pseudoMassFromParamsAtPair` on the `J = 0`
slice.

## Umbrella-reachable via its cluster head

This module has no importers outside its own cluster.  The cluster head is
registered in the root umbrella `IsingModel.lean`, so this module too lies
inside the transitive import closure of `import IsingModel` — the prerequisite
for the capstone axiom audit (`scripts/audit_gate.py`, check V3) to reach it.
Note that V3 inspects only the names listed in `scripts/audit/capstones.txt`,
and no declaration of this module is currently listed there.  It is
genuine formalization — non-trivial closed-form value results for the `J = 0` /
`h = 0` slices of `pseudoMassFromParamsAtPair`, built on the
`PseudoMass/FromParamsBasic` results.
-/

namespace IsingModel

open Set Real Filter

/-- **At `J = 0` distinct pair, `pseudoMassFromParamsAtPair` equals
the typed `pseudoMass(tanh(β·h)^2)`** when `0 < h` and `0 < β`
(ferromagnetic with strict positivity): `tanh(β·h) ∈ (0, 1)`, so
`tanh(β·h)^2 ∈ Ioo 0 1 ⊂ Ioo 0 2`, hence the totalisation collapses
to the typed `pseudoMass`. Combines `_at_J_zero_distinct_eq` (gives
`pseudoMassExt(tanh(β·h)^2)`) with `pseudoMassExt_of_mem`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    ∃ hmem : Real.tanh (β * h) ^ 2 ∈ Set.Ioo (0 : ℝ) 2,
      pseudoMassFromParamsAtPair hα hr d Λ
          (⟨0, h, β⟩ : IsingParams ℝ) x z = pseudoMass hα hr hmem := by
  have hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) :=
    ⟨le_refl 0, hh.le, hβ⟩
  have habs : |Real.tanh (β * h)| < 1 := Real.abs_tanh_lt_one _
  have hlt_one : Real.tanh (β * h) < 1 := lt_of_abs_lt habs
  have hgt_neg_one : -1 < Real.tanh (β * h) := neg_lt_of_abs_lt habs
  have htanh_pos : 0 < Real.tanh (β * h) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hβ hh)) (Real.cosh_pos _)
  have hmem : Real.tanh (β * h) ^ 2 ∈ Set.Ioo (0 : ℝ) 2 := by
    refine ⟨by positivity, ?_⟩
    nlinarith
  refine ⟨hmem, ?_⟩
  rw [pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ hf hxz]
  exact pseudoMassExt_of_mem hα hr hmem

/-- **At `J = 0, h = 0` for ANY pair `(x, z)` (diag + distinct), the
bridge = 0**: combines `_diag_h_zero` (covers `x = z`, any J, β, h=0)
with `_at_J_zero_h_zero_eq_zero` (covers `x ≠ z` under `0 < β`).
At `J = h = 0`, the system is independent uniform spins for any β > 0,
so all 2-point correlations vanish identically. -/
theorem pseudoMassFromParamsAtPair_J_zero_h_zero_any_pair
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) x z = 0 := by
  by_cases hxz : x = z
  · subst hxz
    exact pseudoMassFromParamsAtPair_diag_h_zero hα hr d Λ 0 β x
  · exact pseudoMassFromParamsAtPair_at_J_zero_h_zero_eq_zero hα hr d Λ hβ hxz

end IsingModel
