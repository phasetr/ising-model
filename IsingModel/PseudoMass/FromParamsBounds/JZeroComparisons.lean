import IsingModel.PseudoMass.FromParamsBounds.HZeroComparisons

/-!
# Pseudo-Mass J = 0 Comparisons

This module is part of the split `IsingModel.PseudoMass.FromParamsBounds` development.

## Umbrella-registered cluster head

No other library module imports this one, so it is registered directly in the
root umbrella `IsingModel.lean`; it is the head of a self-contained cluster
(its sibling modules import one another in a chain), and registering the head
brings the whole cluster into the transitive import closure of
`import IsingModel` — the prerequisite for the capstone axiom audit
(`scripts/audit_gate.py`, check V3) to reach it.  Note that V3 inspects only the
names listed in `scripts/audit/capstones.txt`, and no declaration of this
cluster is currently listed there.  The cluster is genuine
formalization: non-trivial comparison / sandwich / log-bound results for the
`J = 0` / `h = 0` slices of `pseudoMassFromParamsAtPair`, built on the
`PseudoMass/FromParamsBasic` results.
-/

namespace IsingModel

open Set Real Filter

/-- **`pseudoMassFromParamsAtPair_at_J_zero_distinct < pseudoMass(c) ↔
c < tanh(β·h)^2`**: J=0 analog of `_at_h_zero_lt_pseudoMass_iff_lt_truncated2`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_lt_pseudoMass_iff_lt_tanh_sq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z <
      pseudoMass hα hr hc ↔
    c < Real.tanh (β * h) ^ 2 := by
  obtain ⟨hmem, heq⟩ :=
    pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass
      hα hr d Λ hh hβ hxz
  rw [heq]
  refine ⟨?_, fun hlt => pseudoMass_strictAnti hα hr hc hmem hlt⟩
  intro hlt
  by_contra h_neg
  have h_neg' : Real.tanh (β * h) ^ 2 ≤ c := not_lt.mp h_neg
  exact absurd hlt (not_lt.mpr (pseudoMass_antitone hα hr hmem hc h_neg'))

/-- **`pseudoMass(c) < pseudoMassFromParamsAtPair_at_J_zero_distinct ↔
tanh(β·h)^2 < c`**. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_gt_pseudoMass_iff_gt_tanh_sq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMass hα hr hc <
      pseudoMassFromParamsAtPair hα hr d Λ
        (⟨0, h, β⟩ : IsingParams ℝ) x z ↔
    Real.tanh (β * h) ^ 2 < c := by
  obtain ⟨hmem, heq⟩ :=
    pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass
      hα hr d Λ hh hβ hxz
  rw [heq]
  refine ⟨?_, fun hlt => pseudoMass_strictAnti hα hr hmem hc hlt⟩
  intro hlt
  by_contra h_neg
  have h_neg' : c ≤ Real.tanh (β * h) ^ 2 := not_lt.mp h_neg
  exact absurd hlt (not_lt.mpr (pseudoMass_antitone hα hr hc hmem h_neg'))

/-- **`pseudoMassFromParamsAtPair_at_J_zero_distinct ≤ pseudoMass(c) ↔
c ≤ tanh(β·h)^2`**: non-strict version of `_lt_pseudoMass_iff_lt_tanh_sq`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_le_pseudoMass_iff_le_tanh_sq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z ≤
      pseudoMass hα hr hc ↔
    c ≤ Real.tanh (β * h) ^ 2 := by
  obtain ⟨hmem, heq⟩ :=
    pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass
      hα hr d Λ hh hβ hxz
  rw [heq]
  refine ⟨?_, fun hle => pseudoMass_antitone hα hr hc hmem hle⟩
  intro hle
  by_contra h_neg
  have h_neg' : Real.tanh (β * h) ^ 2 < c := not_le.mp h_neg
  have := pseudoMass_strictAnti hα hr hmem hc h_neg'
  linarith

/-- **`pseudoMass(c) ≤ pseudoMassFromParamsAtPair_at_J_zero_distinct ↔
tanh(β·h)^2 ≤ c`**: companion non-strict iff. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_ge_pseudoMass_iff_ge_tanh_sq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMass hα hr hc ≤
      pseudoMassFromParamsAtPair hα hr d Λ
        (⟨0, h, β⟩ : IsingParams ℝ) x z ↔
    Real.tanh (β * h) ^ 2 ≤ c := by
  obtain ⟨hmem, heq⟩ :=
    pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass
      hα hr d Λ hh hβ hxz
  rw [heq]
  refine ⟨?_, fun hle => pseudoMass_antitone hα hr hmem hc hle⟩
  intro hle
  by_contra h_neg
  have h_neg' : c < Real.tanh (β * h) ^ 2 := not_le.mp h_neg
  have := pseudoMass_strictAnti hα hr hc hmem h_neg'
  linarith

/-- **`pseudoMassFromParamsAtPair_at_J_zero_distinct = pseudoMass(c) ↔
tanh(β·h)^2 = c`**: equality iff via antisymmetry of le/ge iff
characterizations (PR #1739). -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass_iff_tanh_sq_eq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z =
      pseudoMass hα hr hc ↔
    Real.tanh (β * h) ^ 2 = c := by
  refine ⟨?_, ?_⟩
  · intro heq
    have h1 := (pseudoMassFromParamsAtPair_at_J_zero_distinct_le_pseudoMass_iff_le_tanh_sq
                  hα hr d Λ hh hβ hxz hc).mp heq.le
    have h2 := (pseudoMassFromParamsAtPair_at_J_zero_distinct_ge_pseudoMass_iff_ge_tanh_sq
                  hα hr d Λ hh hβ hxz hc).mp heq.ge
    linarith
  · intro heq_t
    obtain ⟨hmem, h_eq_pm⟩ :=
      pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass
        hα hr d Λ hh hβ hxz
    rw [h_eq_pm]
    congr 1

end IsingModel
