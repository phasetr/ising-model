import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempLipschitz.NormSub

/-!
# High-temp Lipschitz split — infinite-volume correlation Lipschitz bounds

Part of the split high-temperature Lipschitz layer (Issue #1850).
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **Infinite-volume two-point function is Lipschitz in β** (Step 168, GJ §17.5):
For any exhaustion `Λ`, vertices `r_val ≠ s_val`, `0 ≤ J`, `0 < a ≤ b`, `bJ·2d < 1`,
`β ↦ correlationInfinite (latticeGraph d) Λ ⟨J,0,β⟩ {r_val,s_val}`
is `C`-Lipschitz on `[a, b]`, with `C = J·M² + J·4d`, `M = bJ·2d/(1-bJ·2d)`.

Proof: for β₁ ≤ β₂ in `[a,b]`:
- Monotonicity: `corr_∞(β₁) ≤ corr_∞(β₂)`.
- Upper bound: for each stage `n`, either `corr_n(β₂) ≤ corr_n(β₁) + C·(β₂-β₁)` (Step 167)
  or `corr_n(β₂) = 0 ≤ corr_∞(β₁) + C·(β₂-β₁)`. Taking `ciSup_le` gives
  `corr_∞(β₂) ≤ corr_∞(β₁) + C·(β₂-β₁)`.
  So `|corr_∞(β₂) - corr_∞(β₁)| = corr_∞(β₂) - corr_∞(β₁) ≤ C·|β₂-β₁|`.

Reference: Glimm–Jaffe §17.5 p.~312. -/
theorem correlationInfinite_lipschitzOnWith_beta_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1) :
    let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
    LipschitzOnWith ⟨J * M ^ 2 + J * (4 * ↑d), by
        have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
        have hM_nn : 0 ≤ b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d)) :=
          div_nonneg (mul_nonneg (mul_nonneg (le_of_lt (ha.trans_le hab)) hJ)
                       (Nat.cast_nonneg _)) hdenom_b.le
        exact add_nonneg (mul_nonneg hJ (pow_nonneg hM_nn 2))
               (mul_nonneg hJ (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))⟩
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc a b) := by
  intro M
  have hb_pos : 0 < b := ha.trans_le hab
  have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
  have hM_nn : 0 ≤ M :=
    div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hJ) (Nat.cast_nonneg _)) hdenom_b.le
  have hC_nn : 0 ≤ J * M ^ 2 + J * (4 * ↑d) :=
    add_nonneg (mul_nonneg hJ (pow_nonneg hM_nn 2))
               (mul_nonneg hJ (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
  apply LipschitzOnWith.of_dist_le_mul
  intro β₁ h₁ β₂ h₂
  simp only [Real.dist_eq, NNReal.coe_mk]
  rcases le_total β₁ β₂ with hβ | hβ
  · -- Case β₁ ≤ β₂
    have hmono_inf := IsingModel.Ambient.correlationInfinite_monotone_beta
        (IsingModel.latticeGraph d) Λ hJ (le_refl 0) {r_val, s_val}
        (Set.mem_Ioi.mpr (ha.trans_le h₁.1)) (Set.mem_Ioi.mpr (ha.trans_le h₂.1)) hβ
    rw [abs_of_nonpos (sub_nonpos_of_le hmono_inf), neg_sub,
        abs_of_nonpos (sub_nonpos.mpr hβ), neg_sub]
    simp only [correlationInfinite_eq_ciSup]
    apply sub_le_iff_le_add.mpr
    apply ciSup_le; intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      set r : ↑(Λ.volume n) := ⟨r_val, hrn⟩ with hr_def
      set s : ↑(Λ.volume n) := ⟨s_val, hsn⟩ with hs_def
      have hrs' : r ≠ s := fun h => hrs (congrArg Subtype.val h)
      have heq : ∀ (p : IsingParams ℝ),
          correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {r_val, s_val} n =
          IsingModel.correlation
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) p {r, s} := by
        intro p
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
        exact Iff.rfl
      rw [heq]
      have hnorm := inducedLatticeGraph_correlation_norm_sub_le Λ J hJ a b ha hab hlt
                     n r s hrs' β₁ β₂ h₁ h₂
      have hmono_n := IsingModel.correlation_monotoneOn_beta
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) J hJ {r, s}
          (Set.mem_Ici.mpr (ha.trans_le h₁.1).le)
          (Set.mem_Ici.mpr (ha.trans_le h₂.1).le) hβ
      simp only [Real.norm_of_nonneg (sub_nonneg_of_le hmono_n),
                 Real.norm_of_nonneg (sub_nonneg.mpr hβ)] at hnorm
      have hcn_le_inf :
          IsingModel.correlation
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
              (⟨J, 0, β₁⟩ : IsingParams ℝ) {r, s} ≤
          ⨆ m, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β₁⟩ : IsingParams ℝ) {r_val, s_val} m := by
        rw [← heq (⟨J, 0, β₁⟩ : IsingParams ℝ)]
        exact le_ciSup (correlationAlongExhaustion_bddAbove _ Λ _ _) n
      linarith
    · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      have hnn : 0 ≤ ⨆ m, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β₁⟩ : IsingParams ℝ) {r_val, s_val} m :=
        Real.iSup_nonneg (fun m => correlationAlongExhaustion_nonneg
          (IsingModel.latticeGraph d) Λ (⟨J, 0, β₁⟩ : IsingParams ℝ)
          ⟨hJ, le_refl 0, ha.trans_le h₁.1⟩ {r_val, s_val} m)
      linarith [mul_nonneg hC_nn (sub_nonneg.mpr hβ)]
  · -- Case β₂ ≤ β₁: symmetric
    have hmono_inf := IsingModel.Ambient.correlationInfinite_monotone_beta
        (IsingModel.latticeGraph d) Λ hJ (le_refl 0) {r_val, s_val}
        (Set.mem_Ioi.mpr (ha.trans_le h₂.1)) (Set.mem_Ioi.mpr (ha.trans_le h₁.1)) hβ
    rw [abs_of_nonneg (sub_nonneg_of_le hmono_inf),
        abs_of_nonneg (sub_nonneg.mpr hβ)]
    simp only [correlationInfinite_eq_ciSup]
    apply sub_le_iff_le_add.mpr
    apply ciSup_le; intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      set r : ↑(Λ.volume n) := ⟨r_val, hrn⟩ with hr_def
      set s : ↑(Λ.volume n) := ⟨s_val, hsn⟩ with hs_def
      have hrs' : r ≠ s := fun h => hrs (congrArg Subtype.val h)
      have heq : ∀ (p : IsingParams ℝ),
          correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {r_val, s_val} n =
          IsingModel.correlation
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) p {r, s} := by
        intro p
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
        exact Iff.rfl
      rw [heq]
      have hnorm := inducedLatticeGraph_correlation_norm_sub_le Λ J hJ a b ha hab hlt
                     n r s hrs' β₂ β₁ h₂ h₁
      have hmono_n := IsingModel.correlation_monotoneOn_beta
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) J hJ {r, s}
          (Set.mem_Ici.mpr (ha.trans_le h₂.1).le)
          (Set.mem_Ici.mpr (ha.trans_le h₁.1).le) hβ
      simp only [Real.norm_of_nonneg (sub_nonneg_of_le hmono_n),
                 Real.norm_of_nonneg (sub_nonneg.mpr hβ)] at hnorm
      have hcn_le_inf :
          IsingModel.correlation
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
              (⟨J, 0, β₂⟩ : IsingParams ℝ) {r, s} ≤
          ⨆ m, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) {r_val, s_val} m := by
        rw [← heq (⟨J, 0, β₂⟩ : IsingParams ℝ)]
        exact le_ciSup (correlationAlongExhaustion_bddAbove _ Λ _ _) n
      linarith
    · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      have hnn : 0 ≤ ⨆ m, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) {r_val, s_val} m :=
        Real.iSup_nonneg (fun m => correlationAlongExhaustion_nonneg
          (IsingModel.latticeGraph d) Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
          ⟨hJ, le_refl 0, ha.trans_le h₂.1⟩ {r_val, s_val} m)
      linarith [mul_nonneg hC_nn (sub_nonneg.mpr hβ)]

/-- **Infinite-volume two-point function is Lipschitz in J** (Step 222):
For any exhaustion `Λ`, vertices `r_val ≠ s_val`, `0 < β`, `0 < a ≤ b`, `bβ·2d < 1`,
`J ↦ correlationInfinite (latticeGraph d) Λ ⟨J,0,β⟩ {r_val,s_val}`
is `C`-Lipschitz on `[a, b]`, with `C = β·M² + β·4d`, `M = bβ·2d/(1-bβ·2d)`.

Direct J-direction analogue of Step 168. Proof: for J₁ ≤ J₂ in `[a,b]`:
- Monotonicity in J: `corr_∞(J₁) ≤ corr_∞(J₂)`.
- For each stage `n`, either `corr_n(J₂) ≤ corr_n(J₁) + C·(J₂-J₁)` (Step 221)
  or `corr_n(J₂) = 0 ≤ corr_∞(J₁) + C·(J₂-J₁)`. Take `ciSup_le`. -/
theorem correlationInfinite_lipschitzOnWith_J_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * β * ↑(2 * d) < 1) :
    let M : ℝ := b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d))
    LipschitzOnWith ⟨β * M ^ 2 + β * (4 * ↑d), by
        have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
        have hM_nn : 0 ≤ b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d)) :=
          div_nonneg (mul_nonneg (mul_nonneg (le_of_lt (ha.trans_le hab)) hβ.le)
                       (Nat.cast_nonneg _)) hdenom_b.le
        exact add_nonneg (mul_nonneg hβ.le (pow_nonneg hM_nn 2))
               (mul_nonneg hβ.le (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))⟩
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc a b) := by
  intro M
  have hb_pos : 0 < b := ha.trans_le hab
  have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
  have hM_nn : 0 ≤ M :=
    div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hβ.le) (Nat.cast_nonneg _)) hdenom_b.le
  have hC_nn : 0 ≤ β * M ^ 2 + β * (4 * ↑d) :=
    add_nonneg (mul_nonneg hβ.le (pow_nonneg hM_nn 2))
               (mul_nonneg hβ.le (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
  apply LipschitzOnWith.of_dist_le_mul
  intro J₁ h₁ J₂ h₂
  simp only [Real.dist_eq, NNReal.coe_mk]
  rcases le_total J₁ J₂ with hJ_le | hJ_le
  · have hmono_inf := IsingModel.Ambient.correlationInfinite_monotone_J
        (IsingModel.latticeGraph d) Λ (le_refl 0) hβ {r_val, s_val}
        (Set.mem_Ici.mpr (le_of_lt (ha.trans_le h₁.1)))
        (Set.mem_Ici.mpr (le_of_lt (ha.trans_le h₂.1))) hJ_le
    rw [abs_of_nonpos (sub_nonpos_of_le hmono_inf), neg_sub,
        abs_of_nonpos (sub_nonpos.mpr hJ_le), neg_sub]
    simp only [correlationInfinite_eq_ciSup]
    apply sub_le_iff_le_add.mpr
    apply ciSup_le; intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      set r : ↑(Λ.volume n) := ⟨r_val, hrn⟩ with hr_def
      set s : ↑(Λ.volume n) := ⟨s_val, hsn⟩ with hs_def
      have hrs' : r ≠ s := fun h => hrs (congrArg Subtype.val h)
      have heq : ∀ (p : IsingParams ℝ),
          correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {r_val, s_val} n =
          IsingModel.correlation
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) p {r, s} := by
        intro p
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
        exact Iff.rfl
      rw [heq]
      have hnorm := inducedLatticeGraph_correlation_norm_sub_le_J Λ β hβ a b ha hab hlt
                     n r s hrs' J₁ J₂ h₁ h₂
      have hmono_n := IsingModel.correlation_monotone_J
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 0 (le_refl 0) β hβ {r, s}
          (Set.mem_Ici.mpr (le_of_lt (ha.trans_le h₁.1)))
          (Set.mem_Ici.mpr (le_of_lt (ha.trans_le h₂.1))) hJ_le
      simp only [correlationJ] at hmono_n
      simp only [Real.norm_of_nonneg (sub_nonneg_of_le hmono_n),
                 Real.norm_of_nonneg (sub_nonneg.mpr hJ_le)] at hnorm
      have hcn_le_inf :
          IsingModel.correlation
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
              (⟨J₁, 0, β⟩ : IsingParams ℝ) {r, s} ≤
          ⨆ m, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J₁, 0, β⟩ : IsingParams ℝ) {r_val, s_val} m := by
        rw [← heq (⟨J₁, 0, β⟩ : IsingParams ℝ)]
        exact le_ciSup (correlationAlongExhaustion_bddAbove _ Λ _ _) n
      linarith
    · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      have hnn : 0 ≤ ⨆ m, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J₁, 0, β⟩ : IsingParams ℝ) {r_val, s_val} m :=
        Real.iSup_nonneg (fun m => correlationAlongExhaustion_nonneg
          (IsingModel.latticeGraph d) Λ (⟨J₁, 0, β⟩ : IsingParams ℝ)
          ⟨le_of_lt (ha.trans_le h₁.1), le_refl 0, hβ⟩ {r_val, s_val} m)
      linarith [mul_nonneg hC_nn (sub_nonneg.mpr hJ_le)]
  · -- Case J₂ ≤ J₁: symmetric
    have hmono_inf := IsingModel.Ambient.correlationInfinite_monotone_J
        (IsingModel.latticeGraph d) Λ (le_refl 0) hβ {r_val, s_val}
        (Set.mem_Ici.mpr (le_of_lt (ha.trans_le h₂.1)))
        (Set.mem_Ici.mpr (le_of_lt (ha.trans_le h₁.1))) hJ_le
    rw [abs_of_nonneg (sub_nonneg_of_le hmono_inf),
        abs_of_nonneg (sub_nonneg.mpr hJ_le)]
    simp only [correlationInfinite_eq_ciSup]
    apply sub_le_iff_le_add.mpr
    apply ciSup_le; intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      set r : ↑(Λ.volume n) := ⟨r_val, hrn⟩ with hr_def
      set s : ↑(Λ.volume n) := ⟨s_val, hsn⟩ with hs_def
      have hrs' : r ≠ s := fun h => hrs (congrArg Subtype.val h)
      have heq : ∀ (p : IsingParams ℝ),
          correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {r_val, s_val} n =
          IsingModel.correlation
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) p {r, s} := by
        intro p
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
        exact Iff.rfl
      rw [heq]
      have hnorm := inducedLatticeGraph_correlation_norm_sub_le_J Λ β hβ a b ha hab hlt
                     n r s hrs' J₂ J₁ h₂ h₁
      have hmono_n := IsingModel.correlation_monotone_J
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 0 (le_refl 0) β hβ {r, s}
          (Set.mem_Ici.mpr (le_of_lt (ha.trans_le h₂.1)))
          (Set.mem_Ici.mpr (le_of_lt (ha.trans_le h₁.1))) hJ_le
      simp only [correlationJ] at hmono_n
      simp only [Real.norm_of_nonneg (sub_nonneg_of_le hmono_n),
                 Real.norm_of_nonneg (sub_nonneg.mpr hJ_le)] at hnorm
      have hcn_le_inf :
          IsingModel.correlation
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
              (⟨J₂, 0, β⟩ : IsingParams ℝ) {r, s} ≤
          ⨆ m, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J₂, 0, β⟩ : IsingParams ℝ) {r_val, s_val} m := by
        rw [← heq (⟨J₂, 0, β⟩ : IsingParams ℝ)]
        exact le_ciSup (correlationAlongExhaustion_bddAbove _ Λ _ _) n
      linarith
    · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      have hnn : 0 ≤ ⨆ m, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J₂, 0, β⟩ : IsingParams ℝ) {r_val, s_val} m :=
        Real.iSup_nonneg (fun m => correlationAlongExhaustion_nonneg
          (IsingModel.latticeGraph d) Λ (⟨J₂, 0, β⟩ : IsingParams ℝ)
          ⟨le_of_lt (ha.trans_le h₂.1), le_refl 0, hβ⟩ {r_val, s_val} m)
      linarith [mul_nonneg hC_nn (sub_nonneg.mpr hJ_le)]


end Ambient
end IsingModel
