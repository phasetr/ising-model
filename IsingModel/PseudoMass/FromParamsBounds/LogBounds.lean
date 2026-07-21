import IsingModel.PseudoMass.FromParamsHZero

/-!
# Pseudo-Mass Parameter Log Bounds

This module is part of the split `IsingModel.PseudoMass.FromParamsBounds` development.

## Umbrella-reachable via its cluster head

This module has no importers outside its own cluster.  The cluster head is
registered in the root umbrella `IsingModel.lean`, so this module too lies
inside the transitive import closure of `import IsingModel` — the prerequisite
for the capstone axiom audit (`scripts/audit_gate.py`, check V3) to reach it.
Note that V3 inspects only the names listed in `scripts/audit/capstones.txt`,
and no declaration of this module is currently listed there.  It is
genuine formalization — non-trivial log-bound results for the `J = 0` / `h = 0`
slices of `pseudoMassFromParamsAtPair`, built on the
`PseudoMass/FromParamsBasic` results.
-/

namespace IsingModel

open Set Real Filter

/-- **At `J = 0` distinct pair with `0 < h, 0 < β`,
`pseudoMassFromParamsAtPair < log(2/tanh(β·h)^2)/r`**: strict version of
`_le_log_two_div_tanh_sq` (PR #1708). Combines
`_at_J_zero_distinct_eq_pseudoMass` (PR #1681) with
`pseudoMass_lt_log_two_div` (PR #1705). -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_lt_log_two_div_tanh_sq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z <
      Real.log (2 / Real.tanh (β * h) ^ 2) / r := by
  obtain ⟨hmem, heq⟩ :=
    pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass
      hα hr d Λ hh hβ hxz
  rw [heq]
  exact pseudoMass_lt_log_two_div hα hr hmem

/-- **At `J = 0` distinct pair with `0 < h, 0 < β`,
`pseudoMassFromParamsAtPair ≤ log(2/tanh(β·h)^2)/r`**: explicit
quantitative upper bound on the J=0 reference slice. Combines
`_at_J_zero_distinct_eq_pseudoMass` (PR #1681, identifies bridge with
typed `pseudoMass(tanh(β·h)^2)`) with `pseudoMass_le_log_two_div`
(PR #1702). -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_le_log_two_div_tanh_sq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z ≤
      Real.log (2 / Real.tanh (β * h) ^ 2) / r := by
  obtain ⟨hmem, heq⟩ :=
    pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass
      hα hr d Λ hh hβ hxz
  rw [heq]
  exact pseudoMass_le_log_two_div hα hr hmem

/-- **At `h = 0` with `truncated2 ∈ Ioo 0 2`,
`pseudoMassFromParamsAtPair < log(2/truncated2)/r`**: strict version
of `_at_h_zero_le_log_two_div_truncated2` (below). Combines
`_at_h_zero_eq_pseudoMass_of_truncated2_mem` (PR #1672) with
`pseudoMass_lt_log_two_div` (PR #1705). -/
theorem pseudoMassFromParamsAtPair_at_h_zero_lt_log_two_div_truncated2
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z <
      Real.log (2 / Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                       (⟨J, 0, β⟩ : IsingParams ℝ) x z) / r := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
        hα hr d Λ J β x z htrunc]
  exact pseudoMass_lt_log_two_div hα hr htrunc

/-- **At `h = 0` with `truncated2 ∈ Ioo 0 2`,
`pseudoMassFromParamsAtPair ≤ log(2/truncated2)/r`**: explicit
quantitative upper bound on the bridge in terms of the truncated
2-point function. Combines `_at_h_zero_eq_pseudoMass_of_truncated2_mem`
(PR #1672, identifies bridge with typed `pseudoMass`) with
`pseudoMass_le_log_two_div` (PR #1702). The bound goes to 0 as
truncated2 → 2- and diverges as truncated2 → 0+, capturing the
expected qualitative behaviour. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_le_log_two_div_truncated2
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤
      Real.log (2 / Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                       (⟨J, 0, β⟩ : IsingParams ℝ) x z) / r := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
        hα hr d Λ J β x z htrunc]
  exact pseudoMass_le_log_two_div hα hr htrunc

/-- **Multiplied form: `pseudoMassFromParamsAtPair_at_h_zero · r ≤ log(2/truncated2)`**.
Direct multiplication of `_at_h_zero_le_log_two_div_truncated2` (PR #1704)
through by `r > 0`. Useful when `pm·d(x,z)` decay rates appear. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_mul_r_le_log_two_div_truncated2
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z * r ≤
      Real.log (2 / Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                       (⟨J, 0, β⟩ : IsingParams ℝ) x z) := by
  have h := pseudoMassFromParamsAtPair_at_h_zero_le_log_two_div_truncated2
              hα hr d Λ J β x z htrunc
  rw [le_div_iff₀ hr] at h
  exact h

/-- **`pseudoMassFromParamsAtPair_at_h_zero ∈ Ioo 0 (log(2/truncated2)/r)`**
when `truncated2 ∈ Ioo 0 2`: bundles `_pos_of_truncated2_mem` (PR #1679,
strict positivity) with `_lt_log_two_div_truncated2` (PR #1707, strict
upper bound) into a single membership statement. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_mem_Ioo_log_two_div
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈
      Set.Ioo (0 : ℝ)
        (Real.log (2 / Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                         (⟨J, 0, β⟩ : IsingParams ℝ) x z) / r) :=
  ⟨pseudoMassFromParamsAtPair_at_h_zero_pos_of_truncated2_mem
      hα hr d Λ J β x z htrunc,
   pseudoMassFromParamsAtPair_at_h_zero_lt_log_two_div_truncated2
      hα hr d Λ J β x z htrunc⟩

/-- **At `h = 0`, `pseudoMassFromParamsAtPair ≤ (2 - truncated2)/(truncated2 · r)`**:
sharper bound near `truncated2 = 2`, lifted from
`pseudoMass_le_two_sub_div_mul_r` (PR #1715) via bridge identity. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_le_two_sub_div_mul_r
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤
      (2 - Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z) /
        (Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z * r) := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
        hα hr d Λ J β x z htrunc]
  exact pseudoMass_le_two_sub_div_mul_r hα hr htrunc

/-- **Strict version**: same as above with `<`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_lt_two_sub_div_mul_r
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z <
      (2 - Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z) /
        (Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z * r) := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
        hα hr d Λ J β x z htrunc]
  exact pseudoMass_lt_two_sub_div_mul_r hα hr htrunc

/-- **Strict multiplied form**: `pseudoMassFromParamsAtPair_at_h_zero · r < log(2/truncated2)`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_mul_r_lt_log_two_div_truncated2
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z * r <
      Real.log (2 / Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                       (⟨J, 0, β⟩ : IsingParams ℝ) x z) := by
  have h := pseudoMassFromParamsAtPair_at_h_zero_lt_log_two_div_truncated2
              hα hr d Λ J β x z htrunc
  rw [lt_div_iff₀ hr] at h
  exact h

/-- **At `J = 0` distinct, `pseudoMassFromParamsAtPair ≤
(2 - tanh(β·h)^2)/(tanh(β·h)^2 · r)`**: sharper bound near
`tanh(β·h)^2 = 1` (which never occurs since `tanh^2 < 1` strictly,
but this captures the linearly-vanishing-with-tanh^2 ↑ regime).
Combines `_at_J_zero_distinct_eq_pseudoMass` with
`pseudoMass_le_two_sub_div_mul_r` (PR #1715). -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_le_two_sub_tanh_sq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z ≤
      (2 - Real.tanh (β * h) ^ 2) / (Real.tanh (β * h) ^ 2 * r) := by
  obtain ⟨hmem, heq⟩ :=
    pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass
      hα hr d Λ hh hβ hxz
  rw [heq]
  exact pseudoMass_le_two_sub_div_mul_r hα hr hmem

/-- **Strict version** of `_le_two_sub_tanh_sq`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_lt_two_sub_tanh_sq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z <
      (2 - Real.tanh (β * h) ^ 2) / (Real.tanh (β * h) ^ 2 * r) := by
  obtain ⟨hmem, heq⟩ :=
    pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass
      hα hr d Λ hh hβ hxz
  rw [heq]
  exact pseudoMass_lt_two_sub_div_mul_r hα hr hmem

/-- **Multiplied J=0 form**: `pseudoMassFromParamsAtPair_at_J_zero · r ≤ log(2/tanh^2)`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_mul_r_le_log_two_div_tanh_sq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z * r ≤
      Real.log (2 / Real.tanh (β * h) ^ 2) := by
  have hbnd := pseudoMassFromParamsAtPair_at_J_zero_distinct_le_log_two_div_tanh_sq
                  hα hr d Λ hh hβ hxz
  rw [le_div_iff₀ hr] at hbnd
  exact hbnd

/-- **`pseudoMassFromParamsAtPair_at_J_zero_distinct ∈ Ioo 0 (log(2/tanh^2)/r)`**
when `0 < h, 0 < β`: bundles `_pos_at_J_zero` with `_lt_log_two_div_tanh_sq`
(PR #1709) into one Ioo membership statement. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_mem_Ioo_log_two_div
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z ∈
      Set.Ioo (0 : ℝ) (Real.log (2 / Real.tanh (β * h) ^ 2) / r) :=
  ⟨pseudoMassFromParamsAtPair_pos_at_J_zero hα hr d Λ hh hβ hxz,
   pseudoMassFromParamsAtPair_at_J_zero_distinct_lt_log_two_div_tanh_sq
      hα hr d Λ hh hβ hxz⟩

/-- **Strict multiplied J=0 form**: `pseudoMassFromParamsAtPair_at_J_zero · r < log(2/tanh^2)`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_mul_r_lt_log_two_div_tanh_sq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z * r <
      Real.log (2 / Real.tanh (β * h) ^ 2) := by
  have hbnd := pseudoMassFromParamsAtPair_at_J_zero_distinct_lt_log_two_div_tanh_sq
                  hα hr d Λ hh hβ hxz
  rw [lt_div_iff₀ hr] at hbnd
  exact hbnd

end IsingModel
