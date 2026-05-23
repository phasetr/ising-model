import IsingModel.PseudoMass.FromParamsBounds.JZeroComparisons

/-!
# Pseudo-Mass Parameter Intervals

This module is part of the split `IsingModel.PseudoMass.FromParamsBounds` development.
-/

namespace IsingModel

open Set Real Filter

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
