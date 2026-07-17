import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempContinuousAt
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempZeroBoundary

/-!
# correlationInfinite ContinuousOn on closed [0, b]

Narrow child module for two ℤ^d
`correlationInfinite_continuousOn_{beta,J}_of_high_temp_zero_closed`
wrappers extracted from `LatticeMassHighTempZeroBoundary.lean`:

* `correlationInfinite_continuousOn_beta_of_high_temp_zero_closed` (Step 177),
* `correlationInfinite_continuousOn_J_of_high_temp_zero_closed` (Step 231).
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ContinuousOn of corr_∞ on closed interval [0, b]** (Step 177):
For `1 ≤ d`, `0 < J`, `0 < b`, `bJ·2d < 1`: `β ↦ corr_∞(r, s, β)` is continuous on `[0, b]`,
extending Step 169 to include β = 0.

Proof: For β > 0 use Step 175 ContinuousAt. For β = 0, use Step 176 squeeze
`0 ≤ corr_∞(β) ≤ C·β` for β ∈ (0, b]. -/
theorem correlationInfinite_continuousOn_beta_of_high_temp_zero_closed
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * J * ↑(2 * d) < 1) :
    ContinuousOn
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc 0 b) := by
  have h2d_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
    exact_mod_cast this
  have hJ2d_pos : 0 < J * ↑(2 * d) := mul_pos hJ_pos h2d_pos
  have hb_lt_βc : b < 1 / (J * ↑(2 * d)) := by
    rw [lt_div_iff₀ hJ2d_pos]; linarith
  intro β hβ
  rcases eq_or_lt_of_le hβ.1 with hβ0 | hβ_pos
  · -- β = 0: right-continuity from Step 176 squeeze
    subst hβ0
    set M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d)) with hM_def
    set C : ℝ := J * M ^ 2 + J * (4 * ↑d) with hC_def
    have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
    have hM_nn : 0 ≤ M :=
      div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hJ_pos.le) (Nat.cast_nonneg _)) hdenom_b.le
    have hC_nn : 0 ≤ C :=
      add_nonneg (mul_nonneg hJ_pos.le (pow_nonneg hM_nn 2))
                 (mul_nonneg hJ_pos.le (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
    have h_corr_at_zero : correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) {r_val, s_val} = 0 :=
      correlationInfinite_eq_zero_at_beta_zero Λ r_val s_val J
    rw [ContinuousWithinAt]
    show Filter.Tendsto _ _ (nhds _)
    rw [h_corr_at_zero]
    -- Need: Tendsto (fun β => corr_∞(β)) (𝓝[Icc 0 b] 0) (𝓝 0)
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    refine ⟨ε / (C + 1), div_pos hε (by linarith), ?_⟩
    intro x hx_in hx_dist
    have hx_nn : 0 ≤ x := hx_in.1
    have hx_le_b : x ≤ b := hx_in.2
    have hcorr_x_nn : 0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, x⟩ : IsingParams ℝ) {r_val, s_val} := by
      rcases eq_or_lt_of_le hx_nn with hx0 | hx_pos
      · rw [← hx0, correlationInfinite_eq_zero_at_beta_zero]
      · exact correlationInfinite_nonneg _ _ _ ⟨hJ_pos.le, le_refl 0, hx_pos⟩ _
    have hcorr_x_le_Cx : correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, x⟩ : IsingParams ℝ) {r_val, s_val} ≤ C * x := by
      rcases eq_or_lt_of_le hx_nn with hx0 | hx_pos
      · rw [← hx0, correlationInfinite_eq_zero_at_beta_zero, mul_zero]
      · have hbound := correlationInfinite_le_const_mul_beta_of_high_temp
          Λ r_val s_val hrs J hJ_pos.le b hb_pos hlt x hx_pos hx_le_b
        have heq_M : M = b * J * (2 * ↑d) / (1 - b * J * (2 * ↑d)) := by
          rw [hM_def]; push_cast; ring
        have heq_C : C = J * (b * J * (2 * ↑d) / (1 - b * J * (2 * ↑d))) ^ 2 + J * (4 * ↑d) := by
          rw [hC_def, heq_M]
        rw [heq_C]
        simpa using hbound
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hcorr_x_nn]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hx_nn] at hx_dist
    calc correlationInfinite _ _ _ _ ≤ C * x := hcorr_x_le_Cx
      _ ≤ (C + 1) * x := by nlinarith
      _ < (C + 1) * (ε / (C + 1)) := by
        apply (mul_lt_mul_iff_of_pos_left (by linarith)).mpr hx_dist
      _ = ε := by field_simp
  · -- β > 0: from Step 175
    have hβ_lt_βc : β < 1 / (J * ↑(2 * d)) := lt_of_le_of_lt hβ.2 hb_lt_βc
    have hβ_in_open : β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) := ⟨hβ_pos, hβ_lt_βc⟩
    exact (correlationInfinite_continuousAt_beta_of_high_temp
      hd Λ r_val s_val hrs J hJ_pos β hβ_in_open).continuousWithinAt

/-- **Helper: corr_∞ vanishes at J = 0 for r ≠ s** (Step 231 helper):
At J = h = 0 (any β), every Boltzmann weight = exp(0) = 1, so the correlation
sum reduces to the spin-product sum which vanishes for nonempty A. Hence
each `corr_n(J=0) = 0` and `corr_∞(J=0) = ⨆_n 0 = 0`. -/
lemma correlationInfinite_eq_zero_at_J_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (β : ℝ) :
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      {r_val, s_val} = 0 := by
  rw [correlationInfinite_eq_ciSup]
  apply le_antisymm
  · apply ciSup_le
    intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      have heq : correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨0, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n =
                 IsingModel.correlation
                    (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                    (⟨0, 0, β⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                  ⟨s_val, hsn⟩} := by
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
      rw [heq]
      rw [IsingModel.correlation_zero_params_vanish_of_nonempty_A _ β _
            (Finset.insert_nonempty _ _)]
    · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
  · apply le_ciSup_of_le _ 0
    · by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume 0
      · have hrn : r_val ∈ Λ.volume 0 := Finset.insert_subset_iff.mp h_sub |>.1
        have hsn : s_val ∈ Λ.volume 0 :=
          Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
        have heq : correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                      (⟨0, 0, β⟩ : IsingParams ℝ) {r_val, s_val} 0 =
                   IsingModel.correlation
                      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume 0))
                      (⟨0, 0, β⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume 0)),
                                                    ⟨s_val, hsn⟩} := by
          rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
          congr 1
          ext u; rw [mem_liftFinset]
          simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
        rw [heq]
        rw [IsingModel.correlation_zero_params_vanish_of_nonempty_A _ β _
              (Finset.insert_nonempty _ _)]
      · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
    · -- BddAbove of range
      by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume 0
      · exact ⟨1, fun y hy => by
          obtain ⟨n, rfl⟩ := hy
          exact correlationAlongExhaustion_le_one (IsingModel.latticeGraph d) Λ _ _ _⟩
      · exact ⟨1, fun y hy => by
          obtain ⟨n, rfl⟩ := hy
          exact correlationAlongExhaustion_le_one (IsingModel.latticeGraph d) Λ _ _ _⟩

/-- **ContinuousOn of corr_∞ on closed interval [0, b] in J** (Step 231):
For `0 < β`, `0 < b`, `bβ·2d < 1`: `J ↦ corr_∞(r, s, J)` is continuous on `[0, b]`,
extending Step 223 to include J = 0.

Direct J-direction analogue of Step 177. Proof: For J > 0 use Step 229 ContinuousAt.
For J = 0, use Step 230 squeeze `0 ≤ corr_∞(J) ≤ C·J` for J ∈ (0, b]. -/
theorem correlationInfinite_continuousOn_J_of_high_temp_zero_closed
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * β * ↑(2 * d) < 1) :
    ContinuousOn
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc 0 b) := by
  have h2d_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
    exact_mod_cast this
  have hβ2d_pos : 0 < β * ↑(2 * d) := mul_pos hβ_pos h2d_pos
  have hb_lt_Jc : b < 1 / (β * ↑(2 * d)) := by
    rw [lt_div_iff₀ hβ2d_pos]; linarith
  intro J hJ
  rcases eq_or_lt_of_le hJ.1 with hJ0 | hJ_pos
  · subst hJ0
    set M : ℝ := b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d)) with hM_def
    set C : ℝ := β * M ^ 2 + β * (4 * ↑d) with hC_def
    have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
    have hM_nn : 0 ≤ M :=
      div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hβ_pos.le) (Nat.cast_nonneg _)) hdenom_b.le
    have hC_nn : 0 ≤ C :=
      add_nonneg (mul_nonneg hβ_pos.le (pow_nonneg hM_nn 2))
                 (mul_nonneg hβ_pos.le (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
    have h_corr_at_zero : correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) {r_val, s_val} = 0 :=
      correlationInfinite_eq_zero_at_J_zero Λ r_val s_val β
    rw [ContinuousWithinAt]
    show Filter.Tendsto _ _ (nhds _)
    rw [h_corr_at_zero]
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    refine ⟨ε / (C + 1), div_pos hε (by linarith), ?_⟩
    intro x hx_in hx_dist
    have hx_nn : 0 ≤ x := hx_in.1
    have hx_le_b : x ≤ b := hx_in.2
    have hcorr_x_nn : 0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨x, 0, β⟩ : IsingParams ℝ) {r_val, s_val} := by
      rcases eq_or_lt_of_le hx_nn with hx0 | hx_pos
      · rw [← hx0, correlationInfinite_eq_zero_at_J_zero]
      · exact correlationInfinite_nonneg _ _ _ ⟨hx_pos.le, le_refl 0, hβ_pos⟩ _
    have hcorr_x_le_Cx : correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨x, 0, β⟩ : IsingParams ℝ) {r_val, s_val} ≤ C * x := by
      rcases eq_or_lt_of_le hx_nn with hx0 | hx_pos
      · rw [← hx0, correlationInfinite_eq_zero_at_J_zero, mul_zero]
      · have hbound := correlationInfinite_le_const_mul_J_of_high_temp
          Λ r_val s_val hrs β hβ_pos b hb_pos hlt x hx_pos hx_le_b
        have heq_M : M = b * β * (2 * ↑d) / (1 - b * β * (2 * ↑d)) := by
          rw [hM_def]; push_cast; ring
        have heq_C : C = β * (b * β * (2 * ↑d) / (1 - b * β * (2 * ↑d))) ^ 2 + β * (4 * ↑d) := by
          rw [hC_def, heq_M]
        rw [heq_C]
        simpa using hbound
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hcorr_x_nn]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hx_nn] at hx_dist
    calc correlationInfinite _ _ _ _ ≤ C * x := hcorr_x_le_Cx
      _ ≤ (C + 1) * x := by nlinarith
      _ < (C + 1) * (ε / (C + 1)) := by
        apply (mul_lt_mul_iff_of_pos_left (by linarith)).mpr hx_dist
      _ = ε := by field_simp
  · have hJ_lt_Jc : J < 1 / (β * ↑(2 * d)) := lt_of_le_of_lt hJ.2 hb_lt_Jc
    have hJ_in_open : J ∈ Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d))) := ⟨hJ_pos, hJ_lt_Jc⟩
    exact (correlationInfinite_continuousAt_J_of_high_temp
      hd Λ r_val s_val hrs β hβ_pos J hJ_in_open).continuousWithinAt

end Ambient

end IsingModel
