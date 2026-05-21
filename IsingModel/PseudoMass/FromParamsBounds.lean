import IsingModel.PseudoMass.FromParamsHZero

/-!
# Pseudo-Mass Parameter Bounds

This module is part of the split `IsingModel.PseudoMass` development.
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

/-- **`pseudoMassExt` tends to 0 as `c → 2` within `Ioo 0 2`**: squeeze
between `0` (lower bound, `pseudoMassExt_nonneg`) and
`(2 - c) / (c · r)` (upper bound, `pseudoMass_le_two_sub_div_mul_r`,
PR #1715), where the upper bound tends to `0/(2·r) = 0`. -/
theorem pseudoMassExt_tendsto_zero_at_two
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) :
    Filter.Tendsto (pseudoMassExt hα hr) (nhdsWithin 2 (Set.Ioo (0 : ℝ) 2))
      (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (g := fun _ : ℝ => (0 : ℝ))
        (h := fun c : ℝ => (2 - c) / (c * r))
  · exact tendsto_const_nhds
  · -- (2 - c)/(c · r) → 0 as c → 2 within Ioo 0 2
    have hcont : ContinuousAt (fun c : ℝ => (2 - c) / (c * r)) 2 := by
      apply ContinuousAt.div
      · exact (continuous_const.sub continuous_id).continuousAt
      · exact (continuous_id.mul continuous_const).continuousAt
      · change (2 : ℝ) * r ≠ 0
        exact (mul_pos (by norm_num : (0 : ℝ) < 2) hr).ne'
    have hval : (2 - 2) / (2 * r) = (0 : ℝ) := by simp
    have htnd : Filter.Tendsto (fun c : ℝ => (2 - c) / (c * r)) (nhds 2) (nhds 0) := by
      rw [← hval]
      exact hcont.tendsto
    exact htnd.mono_left nhdsWithin_le_nhds
  · -- 0 ≤ pseudoMassExt(c) (eventually)
    refine Filter.Eventually.of_forall ?_
    intro c
    exact pseudoMassExt_nonneg hα hr c
  · -- pseudoMassExt(c) ≤ (2-c)/(c·r) (eventually within Ioo 0 2)
    rw [Filter.eventually_iff]
    rw [mem_nhdsWithin]
    refine ⟨Set.univ, isOpen_univ, ⟨⟩, ?_⟩
    intro c hc_pair
    have hc : c ∈ Set.Ioo (0 : ℝ) 2 := hc_pair.2
    change pseudoMassExt hα hr c ≤ (2 - c) / (c * r)
    rw [pseudoMassExt_of_mem hα hr hc]
    exact pseudoMass_le_two_sub_div_mul_r hα hr hc

/-- **At `h = 0` ferromagnetic, `pseudoMassFromParamsAtPair ≥ pseudoMass(1)`**
when `0 < truncated2`: combines `_at_h_zero_ge_pseudoMass_of_truncated2_le`
(PR #1677) with `truncated2Infinite_le_one` (ferromagnetic) to get a
uniform lower bound `pseudoMass(1)` on the bridge.

`pseudoMass(1)` here means `pseudoMass hα hr ⟨zero_lt_one, one_lt_two⟩`.

Useful uniform-in-(β, J) lower bound: as long as truncated2 is
strictly positive and bounded by 1 (ferromagnetic), the bridge is
at least `pseudoMass(1)`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_ge_pseudoMass_one
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (x z : Fin d → ℤ)
    (htrunc_pos : 0 < Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                        (⟨J, 0, β⟩ : IsingParams ℝ) x z) :
    pseudoMass hα hr (show (1 : ℝ) ∈ Set.Ioo 0 2 from
        ⟨zero_lt_one, one_lt_two⟩) ≤
      pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
    ⟨hJ, le_refl 0, hβ⟩
  have htrunc_le_one : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                          (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ 1 :=
    Ambient.truncated2Infinite_le_one (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) hf x z
  have htrunc_mem : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2 :=
    ⟨htrunc_pos, by linarith⟩
  have hone_mem : (1 : ℝ) ∈ Set.Ioo (0 : ℝ) 2 := ⟨zero_lt_one, one_lt_two⟩
  exact pseudoMassFromParamsAtPair_at_h_zero_ge_pseudoMass_of_truncated2_le
            hα hr d Λ J β x z hone_mem htrunc_mem htrunc_le_one

/-- **At `h = 0` ferromagnetic, `0 < pseudoMassFromParamsAtPair`**
when `0 < truncated2`: avoids the explicit `Ioo 0 2` membership
hypothesis by combining `truncated2Infinite_le_one` (ferromagnetic
→ truncated2 ≤ 1 < 2) to derive membership. Useful when only
strict positivity of truncated2 is known. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_pos_of_truncated2_pos
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (x z : Fin d → ℤ)
    (htrunc_pos : 0 < Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                        (⟨J, 0, β⟩ : IsingParams ℝ) x z) :
    0 < pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
    ⟨hJ, le_refl 0, hβ⟩
  have htrunc_le_one : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                          (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ 1 :=
    Ambient.truncated2Infinite_le_one (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) hf x z
  have htrunc_mem : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2 :=
    ⟨htrunc_pos, by linarith⟩
  exact pseudoMassFromParamsAtPair_at_h_zero_pos_of_truncated2_mem
            hα hr d Λ J β x z htrunc_mem

/-- **At `J = 0` distinct, `pseudoMassFromParamsAtPair ≥ pseudoMass(1)`**
when `0 < h, 0 < β`: J=0 reference slice analog of
`_at_h_zero_ge_pseudoMass_one` (PR #1725). Uses
`pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass` (PR #1681)
+ `pseudoMass_antitone` (PR #1714) with the bound `tanh(β·h)^2 ≤ 1`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_ge_pseudoMass_one
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMass hα hr (show (1 : ℝ) ∈ Set.Ioo 0 2 from
        ⟨zero_lt_one, one_lt_two⟩) ≤
      pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z := by
  obtain ⟨hmem, heq⟩ :=
    pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_pseudoMass
      hα hr d Λ hh hβ hxz
  have habs : |Real.tanh (β * h)| < 1 := Real.abs_tanh_lt_one _
  have htanh_lt : Real.tanh (β * h) < 1 := lt_of_abs_lt habs
  have htanh_gt_neg : -1 < Real.tanh (β * h) := neg_lt_of_abs_lt habs
  have htanh_sq_le_one : Real.tanh (β * h) ^ 2 ≤ 1 := by nlinarith
  have hone_mem : (1 : ℝ) ∈ Set.Ioo (0 : ℝ) 2 := ⟨zero_lt_one, one_lt_two⟩
  have hge : pseudoMass hα hr hone_mem ≤ pseudoMass hα hr hmem :=
    pseudoMass_antitone hα hr hmem hone_mem htanh_sq_le_one
  rw [heq]
  exact hge

/-- **`pseudoMassFromParamsAtPair_at_h_zero ≠ 0`** when truncated2 ∈ Ioo 0 2:
trivial corollary of `_pos_of_truncated2_mem` (PR #1679). -/
theorem pseudoMassFromParamsAtPair_at_h_zero_ne_zero_of_truncated2_mem
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z ≠ 0 :=
  (pseudoMassFromParamsAtPair_at_h_zero_pos_of_truncated2_mem
      hα hr d Λ J β x z htrunc).ne'

/-- **`pseudoMassFromParamsAtPair_at_h_zero ≠ 0`** when truncated2 > 0
under ferromagnetic: companion of `_ne_zero_of_truncated2_mem` using
the simpler positivity hypothesis. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_ne_zero_of_truncated2_pos
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (x z : Fin d → ℤ)
    (htrunc_pos : 0 < Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                        (⟨J, 0, β⟩ : IsingParams ℝ) x z) :
    pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z ≠ 0 :=
  (pseudoMassFromParamsAtPair_at_h_zero_pos_of_truncated2_pos
      hα hr d Λ hJ hβ x z htrunc_pos).ne'

/-- **`pseudoMassFromParamsAtPair_at_J_zero_distinct ≠ 0`** for
ferromagnetic, h>0, β>0, distinct pair: trivial from
`pseudoMassFromParamsAtPair_pos_at_J_zero`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_ne_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ
        (⟨0, h, β⟩ : IsingParams ℝ) x z ≠ 0 :=
  (pseudoMassFromParamsAtPair_pos_at_J_zero hα hr d Λ hh hβ hxz).ne'

/-- **`pseudoMassFromParamsAtPair_at_h_zero < pseudoMass(c) ↔ c < truncated2`**
when both `c, truncated2 ∈ Ioo 0 2`: pseudoMass strict anti reverses the
inequality. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_lt_pseudoMass_iff_lt_truncated2
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z <
      pseudoMass hα hr hc ↔
    c < Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
        hα hr d Λ J β x z htrunc]
  refine ⟨?_, fun hlt => pseudoMass_strictAnti hα hr hc htrunc hlt⟩
  intro hlt
  by_contra h_neg
  have h_neg' : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ c := not_lt.mp h_neg
  exact absurd hlt (not_lt.mpr (pseudoMass_antitone hα hr htrunc hc h_neg'))

/-- **`pseudoMass(c) < pseudoMassFromParamsAtPair_at_h_zero ↔ truncated2 < c`**:
companion of `_lt_pseudoMass_iff_lt_truncated2`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_gt_pseudoMass_iff_gt_truncated2
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMass hα hr hc <
      pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z ↔
    Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z < c := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
        hα hr d Λ J β x z htrunc]
  refine ⟨?_, fun hlt => pseudoMass_strictAnti hα hr htrunc hc hlt⟩
  intro hlt
  by_contra h_neg
  have h_neg' : c ≤ Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) x z := not_lt.mp h_neg
  exact absurd hlt (not_lt.mpr (pseudoMass_antitone hα hr hc htrunc h_neg'))

/-- **`pseudoMassFromParamsAtPair_at_h_zero ≤ pseudoMass(c) ↔ c ≤ truncated2`**:
non-strict version of `_lt_pseudoMass_iff_lt_truncated2`. Uses
`pseudoMass_antitone` for both directions. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_le_pseudoMass_iff_le_truncated2
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤
      pseudoMass hα hr hc ↔
    c ≤ Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
        hα hr d Λ J β x z htrunc]
  refine ⟨?_, fun hle => pseudoMass_antitone hα hr hc htrunc hle⟩
  intro hle
  by_contra h_neg
  have h_neg' : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) x z < c := not_le.mp h_neg
  have := pseudoMass_strictAnti hα hr htrunc hc h_neg'
  linarith

/-- **`pseudoMass(c) ≤ pseudoMassFromParamsAtPair_at_h_zero ↔ truncated2 ≤ c`**:
companion non-strict iff. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_ge_pseudoMass_iff_ge_truncated2
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMass hα hr hc ≤
      pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z ↔
    Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ c := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
        hα hr d Λ J β x z htrunc]
  refine ⟨?_, fun hle => pseudoMass_antitone hα hr htrunc hc hle⟩
  intro hle
  by_contra h_neg
  have h_neg' : c < Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) x z := not_le.mp h_neg
  have := pseudoMass_strictAnti hα hr hc htrunc h_neg'
  linarith

/-- **`pseudoMassFromParamsAtPair_at_h_zero = pseudoMass(c) ↔ truncated2 = c`**:
combines the `_le_iff` and `_ge_iff` non-strict iff characterizations
via antisymmetry. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_iff_truncated2_eq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z =
      pseudoMass hα hr hc ↔
    Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z = c := by
  refine ⟨?_, ?_⟩
  · intro heq
    have hle : pseudoMassFromParamsAtPair hα hr d Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ pseudoMass hα hr hc := heq.le
    have hge : pseudoMass hα hr hc ≤ pseudoMassFromParamsAtPair hα hr d Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z := heq.ge
    have h1 := (pseudoMassFromParamsAtPair_at_h_zero_le_pseudoMass_iff_le_truncated2
                  hα hr d Λ J β x z hc htrunc).mp hle
    have h2 := (pseudoMassFromParamsAtPair_at_h_zero_ge_pseudoMass_iff_ge_truncated2
                  hα hr d Λ J β x z hc htrunc).mp hge
    linarith
  · intro heq_t
    rw [pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
          hα hr d Λ J β x z htrunc]
    congr 1

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

/-- **`pseudoMassFromParamsAtPair_at_h_zero pos iff truncated2 ≠ 0`**:
combines `_at_h_zero_pos_iff` (PR #1670, pos iff truncated2 > 0) with
`truncated2Infinite_pos_iff_ne_zero` (PR #1748). -/
theorem pseudoMassFromParamsAtPair_at_h_zero_pos_iff_ne_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (x z : Fin d → ℤ) :
    0 < pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z ↔
    Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z ≠ 0 := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
    ⟨hJ, le_refl 0, hβ⟩
  rw [pseudoMassFromParamsAtPair_at_h_zero_pos_iff hα hr d Λ hJ hβ x z]
  exact Ambient.truncated2Infinite_pos_iff_ne_zero
            (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf x z

/-- **`0 < pseudoMassFromParamsAtPair ↔ pseudoMassFromParamsAtPair ≠ 0`**:
trivial via `pseudoMassFromParamsAtPair_nonneg`. -/
theorem pseudoMassFromParamsAtPair_pos_iff_ne_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ) :
    0 < pseudoMassFromParamsAtPair hα hr d Λ p x z ↔
    pseudoMassFromParamsAtPair hα hr d Λ p x z ≠ 0 :=
  (pseudoMassFromParamsAtPair_nonneg hα hr d Λ p x z).lt_iff_ne.trans
    ⟨fun h => h.symm, fun h => h.symm⟩

/-- **At `h = 0`, `pseudoMassFromParamsAtPair ∈ Ioo 0 ((2-truncated2)/(truncated2·r))`**:
sharper Ioo membership at h=0 using `(2-c)/(c·r)`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_mem_Ioo_zero_two_sub_div
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈
      Set.Ioo (0 : ℝ)
        ((2 - Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) x z) /
         (Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) x z * r)) :=
  ⟨pseudoMassFromParamsAtPair_at_h_zero_pos_of_truncated2_mem
      hα hr d Λ J β x z htrunc,
   pseudoMassFromParamsAtPair_at_h_zero_lt_two_sub_div_mul_r
      hα hr d Λ J β x z htrunc⟩

/-- **At `J = 0` distinct, `pseudoMassFromParamsAtPair ∈ Ioo 0 ((2-tanh^2)/(tanh^2·r))`**. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_mem_Ioo_zero_two_sub_div
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z ∈
      Set.Ioo (0 : ℝ) ((2 - Real.tanh (β * h) ^ 2) / (Real.tanh (β * h) ^ 2 * r)) :=
  ⟨pseudoMassFromParamsAtPair_pos_at_J_zero hα hr d Λ hh hβ hxz,
   pseudoMassFromParamsAtPair_at_J_zero_distinct_lt_two_sub_tanh_sq
      hα hr d Λ hh hβ hxz⟩

/-- **`¬(pseudoMassFromParamsAtPair < 0)`**: trivial via nonneg. -/
theorem pseudoMassFromParamsAtPair_not_lt_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ) :
    ¬ (pseudoMassFromParamsAtPair hα hr d Λ p x z < 0) :=
  not_lt.mpr (pseudoMassFromParamsAtPair_nonneg hα hr d Λ p x z)

/-- **`pseudoMassFromParamsAtPair ≤ 0 ↔ pseudoMassFromParamsAtPair = 0`**:
trivial via nonneg + antisymmetry. -/
theorem pseudoMassFromParamsAtPair_le_zero_iff_eq_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z ≤ 0 ↔
    pseudoMassFromParamsAtPair hα hr d Λ p x z = 0 := by
  refine ⟨?_, fun h => le_of_eq h⟩
  intro hle
  exact le_antisymm hle (pseudoMassFromParamsAtPair_nonneg hα hr d Λ p x z)

/-- **`pseudoMassFromParamsAtPair < pseudoMassExt(c) ↔ c < correlation`** when both
in `Ioo 0 2`: iff form using the bridge identity. -/
theorem pseudoMassFromParamsAtPair_lt_pseudoMassExt_iff_lt_corr
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z <
      pseudoMassExt hα hr c ↔
    c < Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} := by
  unfold pseudoMassFromParamsAtPair
  exact pseudoMassExt_lt_iff hα hr hc hcorr

/-- **`pseudoMassExt(c) < pseudoMassFromParamsAtPair ↔ correlation < c`**: companion. -/
theorem pseudoMassFromParamsAtPair_gt_pseudoMassExt_iff_corr_lt
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassExt hα hr c <
      pseudoMassFromParamsAtPair hα hr d Λ p x z ↔
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} < c := by
  unfold pseudoMassFromParamsAtPair
  exact pseudoMassExt_lt_iff hα hr hcorr hc

/-- **`pseudoMassFromParamsAtPair ≤ pseudoMassExt(c) ↔ c ≤ correlation`**:
non-strict iff form. -/
theorem pseudoMassFromParamsAtPair_le_pseudoMassExt_iff_le_corr
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z ≤
      pseudoMassExt hα hr c ↔
    c ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} := by
  unfold pseudoMassFromParamsAtPair
  exact pseudoMassExt_le_iff hα hr hc hcorr

/-- **`pseudoMassExt(c) ≤ pseudoMassFromParamsAtPair ↔ correlation ≤ c`**. -/
theorem pseudoMassFromParamsAtPair_ge_pseudoMassExt_iff_corr_le
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassExt hα hr c ≤
      pseudoMassFromParamsAtPair hα hr d Λ p x z ↔
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} ≤ c := by
  unfold pseudoMassFromParamsAtPair
  exact pseudoMassExt_le_iff hα hr hcorr hc

/-- **`pseudoMassFromParamsAtPair = pseudoMassExt(c) ↔ correlation = c`**:
equality iff. -/
theorem pseudoMassFromParamsAtPair_eq_pseudoMassExt_iff_corr_eq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z =
      pseudoMassExt hα hr c ↔
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} = c := by
  unfold pseudoMassFromParamsAtPair
  rw [pseudoMassExt_eq_iff_of_mem hα hr hc hcorr]
  exact eq_comm

/-- **Λ-uniform `pseudoMass(1)` lower bound at h=0**: combines
`_at_h_zero_ge_pseudoMass_one` (PR #1725) with `_indep_exhaustion`
(PR #1666) to make the lower bound explicitly Λ-independent. For any
two exhaustions Λ, Λ', the bridge values are equal (under ferromagnetic),
and both bounded below by `pseudoMass(1)`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_ge_pseudoMass_one_uniform
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ'.volume n)).edgeSet]
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (x z : Fin d → ℤ)
    (htrunc_pos : 0 < Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                        (⟨J, 0, β⟩ : IsingParams ℝ) x z) :
    pseudoMass hα hr (show (1 : ℝ) ∈ Set.Ioo 0 2 from
        ⟨zero_lt_one, one_lt_two⟩) ≤
      pseudoMassFromParamsAtPair hα hr d Λ' (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
    ⟨hJ, le_refl 0, hβ⟩
  rw [← pseudoMassFromParamsAtPair_indep_exhaustion hα hr d Λ Λ'
        (⟨J, 0, β⟩ : IsingParams ℝ) hf x z]
  exact pseudoMassFromParamsAtPair_at_h_zero_ge_pseudoMass_one
            hα hr d Λ hJ hβ x z htrunc_pos

/-- **`pseudoMassFromParamsAtPair ∈ Ici 0`** (always): direct from
nonneg. -/
theorem pseudoMassFromParamsAtPair_mem_Ici_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z ∈ Set.Ici (0 : ℝ) :=
  pseudoMassFromParamsAtPair_nonneg hα hr d Λ p x z

/-- **At `J = 0` distinct, `pseudoMassFromParamsAtPair ∈ Ioo 0 (log(2/tanh^2)/r)`**:
J=0 analog of `_at_h_zero_mem_Ioo_log_two_div`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_mem_Ioo_zero_log_two_div
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

/-- **At `h = 0` with `truncated2 ∈ Ioo 0 2`,
`pseudoMassFromParamsAtPair_at_h_zero ∈ Ioo 0 (log(2/truncated2)/r)`**:
bundles `_pos_of_truncated2_mem` (PR #1679) + `_lt_log_two_div_truncated2`
(PR #1707). -/
theorem pseudoMassFromParamsAtPair_at_h_zero_mem_Ioo_zero_log_two_div
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

/-- **At `h = 0` with `truncated2 ∈ Ioo 0 2`,
`pseudoMassFromParamsAtPair_at_h_zero ∈ Iio (log(2/truncated2)/r)`**. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_mem_Iio_log_two_div
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈
      Set.Iio (Real.log (2 / Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                              (⟨J, 0, β⟩ : IsingParams ℝ) x z) / r) :=
  pseudoMassFromParamsAtPair_at_h_zero_lt_log_two_div_truncated2
      hα hr d Λ J β x z htrunc

/-- **At `h = 0`, `pseudoMassFromParamsAtPair ∈ Ici 0`**: trivial. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_mem_Ici_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈
      Set.Ici (0 : ℝ) :=
  pseudoMassFromParamsAtPair_nonneg hα hr d Λ _ x z

/-- **At `J = 0` distinct, `pseudoMassFromParamsAtPair ∈ Iio (log(2/tanh^2)/r)`**. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_mem_Iio_log_two_div
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z ∈
      Set.Iio (Real.log (2 / Real.tanh (β * h) ^ 2) / r) :=
  pseudoMassFromParamsAtPair_at_J_zero_distinct_lt_log_two_div_tanh_sq
      hα hr d Λ hh hβ hxz

/-- **At `J = 0` distinct, `pseudoMassFromParamsAtPair ∈ Iio ((2-tanh^2)/(tanh^2·r))`**. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_mem_Iio_two_sub_tanh_sq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z ∈
      Set.Iio ((2 - Real.tanh (β * h) ^ 2) / (Real.tanh (β * h) ^ 2 * r)) :=
  pseudoMassFromParamsAtPair_at_J_zero_distinct_lt_two_sub_tanh_sq
      hα hr d Λ hh hβ hxz

/-- **`pseudoMassFromParamsAtPair ∈ Ioi 0`** when corr ∈ Ioo 0 2: -/
theorem pseudoMassFromParamsAtPair_mem_Ioi_zero_of_corr_mem
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z ∈ Set.Ioi (0 : ℝ) :=
  pseudoMassFromParamsAtPair_pos_of_corr_mem hα hr d Λ p x z hcorr

/-- **`pseudoMassFromParamsAtPair ∉ Iio 0`**: trivial. -/
theorem pseudoMassFromParamsAtPair_not_mem_Iio_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z ∉ Set.Iio (0 : ℝ) :=
  not_lt.mpr (pseudoMassFromParamsAtPair_nonneg hα hr d Λ p x z)


end IsingModel
