import IsingModel.PseudoMass.FromParamsBounds.LogBounds

/-!
# Pseudo-Mass Parameter Tendsto and Lower Bounds

This module is part of the split `IsingModel.PseudoMass.FromParamsBounds` development.

## Umbrella-reachable via its cluster head

This module has no importers outside its own cluster.  The cluster head is
registered in the root umbrella `IsingModel.lean`, so this module lies inside
the transitive import closure of `import IsingModel` and is therefore covered by
the capstone axiom audit (`scripts/audit_gate.py`, check V3).  It is
genuine formalization — non-trivial limit / lower-bound results for the
`J = 0` / `h = 0` slices of `pseudoMassFromParamsAtPair`, built on the live
`PseudoMass/FromParamsBasic` results.
-/

namespace IsingModel

open Set Real Filter

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

end IsingModel
