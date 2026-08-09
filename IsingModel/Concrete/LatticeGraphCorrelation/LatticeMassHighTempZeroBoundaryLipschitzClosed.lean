import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempZeroBoundary
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempZeroBoundaryContinuousOnClosed
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempZeroBoundaryMonotoneClosed

/-!
# ℤ^d Lipschitz bound on the two-point function up to the zero boundary

Instantiates at `IsingModel.latticeGraph d`, for an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ` and two distinct sites at zero external field, the Lipschitz property of the
infinite-volume correlation on the closed interval `Set.Icc 0 b`, with the explicit constant
built from `b`, the parameter held fixed and the dimension. The statement is given in the
inverse-temperature direction, under `0 ≤ J`, and in the coupling direction, under `0 < β`;
each also assumes `0 < b` and that `b` times the parameter held fixed times `2 * d` is below
one. Behind each of them sits a private ordered increment bound carrying the same hypotheses
together with the ordering of the two arguments, non-negativity of the smaller one and the
bound `b` on the larger one.
-/

namespace IsingModel
namespace Ambient

/-- **Helper for Step 180**: ordered Lipschitz bound on [0, b] (closed including β = 0).
For `0 ≤ β₁ ≤ β₂` with `β₂ ≤ b` and `bJ·2d < 1`:
`corr_∞(β₂) - corr_∞(β₁) ≤ C · (β₂ - β₁)` where `C = J·M² + J·4d`. -/
private lemma correlationInfinite_diff_le_const_mul_diff
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * J * ↑(2 * d) < 1)
    (β₁ β₂ : ℝ) (hβ₁_nn : 0 ≤ β₁) (hβ : β₁ ≤ β₂) (hβ₂_le_b : β₂ ≤ b) :
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      {r_val, s_val} -
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β₁⟩ : IsingParams ℝ)
      {r_val, s_val} ≤
    (J * (b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))) ^ 2 + J * (4 * ↑d)) *
      (β₂ - β₁) := by
  rcases eq_or_lt_of_le hβ₁_nn with hβ₁0 | hβ₁_pos
  · -- β₁ = 0
    rw [← hβ₁0, correlationInfinite_eq_zero_at_beta_zero, sub_zero, sub_zero]
    rcases eq_or_lt_of_le (hβ₁0.le.trans hβ) with hβ₂0 | hβ₂_pos
    · rw [← hβ₂0, correlationInfinite_eq_zero_at_beta_zero]
      have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
      have hM_nn : 0 ≤ b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d)) :=
        div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hJ) (Nat.cast_nonneg _)) hdenom_b.le
      positivity
    · -- β₂ > 0: use Step 176
      have hbound := correlationInfinite_le_const_mul_beta_of_high_temp
        Λ r_val s_val hrs J hJ b hb_pos hlt β₂ hβ₂_pos hβ₂_le_b
      -- hbound has let M = b*J*↑(2*d)/(1-b*J*↑(2*d)), so we directly get the bound
      simpa using hbound
  · -- β₁ > 0: use Step 168 (LipschitzOnWith on [β₁, b])
    -- Step 168's `let M` wrapper requires explicit type ascription below
    have hlip_let := correlationInfinite_lipschitzOnWith_beta_of_high_temp
      Λ r_val s_val hrs J hJ β₁ b hβ₁_pos (hβ.trans hβ₂_le_b) hlt
    -- Extract the underlying LipschitzOnWith (the `let M :=` is just notation)
    have hlip : LipschitzOnWith
        ⟨J * (b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))) ^ 2 + J * (4 * ↑d), by
          have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
          have hM_nn : 0 ≤ b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d)) :=
            div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hJ)
                         (Nat.cast_nonneg _)) hdenom_b.le
          positivity⟩
        (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val})
        (Set.Icc β₁ b) := hlip_let
    have hβ₁_in : β₁ ∈ Set.Icc β₁ b := Set.mem_Icc.mpr ⟨le_refl _, hβ.trans hβ₂_le_b⟩
    have hβ₂_in : β₂ ∈ Set.Icc β₁ b := Set.mem_Icc.mpr ⟨hβ, hβ₂_le_b⟩
    have hdist := hlip.dist_le_mul β₁ hβ₁_in β₂ hβ₂_in
    have hcorr_nn :
        0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) {r_val, s_val} -
            correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β₁⟩ : IsingParams ℝ) {r_val, s_val} := by
      have hmono := correlationInfinite_monotoneOn_beta_zero_closed Λ r_val s_val J hJ b
      have h1 : β₁ ∈ Set.Icc (0 : ℝ) b := Set.mem_Icc.mpr ⟨hβ₁_pos.le, hβ.trans hβ₂_le_b⟩
      have h2 : β₂ ∈ Set.Icc (0 : ℝ) b := Set.mem_Icc.mpr ⟨hβ₁_pos.le.trans hβ, hβ₂_le_b⟩
      linarith [hmono h1 h2 hβ]
    have hβ_nn : 0 ≤ β₂ - β₁ := by linarith
    simp only [Real.dist_eq] at hdist
    rw [abs_sub_comm β₁ β₂, abs_of_nonneg hβ_nn,
        abs_sub_comm
          (correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β₁⟩ : IsingParams ℝ) {r_val, s_val})
          (correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) {r_val, s_val}),
        abs_of_nonneg hcorr_nn] at hdist
    push_cast at hdist
    -- Convert ↑(2*d) ↔ 2 * ↑d for matching
    convert hdist using 2
    push_cast; ring

/-- **LipschitzOnWith of corr_∞ on closed [0, b] (including β = 0)** (Step 180):
For `0 ≤ J`, `0 < b`, `bJ·2d < 1`: `β ↦ corr_∞(β)` is `C`-Lipschitz on `[0, b]`
with the same constant `C = J·M² + J·4d` as Step 168.

Strengthens Step 168 from `[a, b]` (a > 0) to closed `[0, b]`. -/
theorem correlationInfinite_lipschitzOnWith_beta_zero_closed
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * J * ↑(2 * d) < 1) :
    LipschitzOnWith ⟨J * (b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))) ^ 2 + J * (4 * ↑d), by
        have hdenom_b : 0 < 1 - b * J * ↑(2 * d) := by linarith
        have hM_nn : 0 ≤ b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d)) :=
          div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hJ)
                       (Nat.cast_nonneg _)) hdenom_b.le
        have := hM_nn
        positivity⟩
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc 0 b) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro β₁ hβ₁ β₂ hβ₂
  -- Generic argument: the bound depends on min/max of β₁, β₂
  rcases le_total β₁ β₂ with hβ | hβ
  · -- β₁ ≤ β₂: |f β₁ - f β₂| ≤ K * |β₁ - β₂|
    have hcorr_nn :
        0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) {r_val, s_val} -
            correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β₁⟩ : IsingParams ℝ) {r_val, s_val} := by
      have hmono := correlationInfinite_monotoneOn_beta_zero_closed Λ r_val s_val J hJ b
      linarith [hmono hβ₁ hβ₂ hβ]
    have hβ_nn : 0 ≤ β₂ - β₁ := by linarith
    rw [Real.dist_eq, Real.dist_eq, abs_sub_comm β₁ β₂,
        abs_sub_comm
          ((fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) β₁)
          ((fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) β₂),
        abs_of_nonneg hcorr_nn, abs_of_nonneg hβ_nn]
    have hbound := correlationInfinite_diff_le_const_mul_diff Λ r_val s_val hrs J hJ b hb_pos hlt
      β₁ β₂ hβ₁.1 hβ hβ₂.2
    push_cast
    push_cast at hbound
    exact hbound
  · -- β₂ ≤ β₁: similar with roles swapped
    have hcorr_nn :
        0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β₁⟩ : IsingParams ℝ) {r_val, s_val} -
            correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) {r_val, s_val} := by
      have hmono := correlationInfinite_monotoneOn_beta_zero_closed Λ r_val s_val J hJ b
      linarith [hmono hβ₂ hβ₁ hβ]
    have hβ_nn : 0 ≤ β₁ - β₂ := by linarith
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg hcorr_nn, abs_of_nonneg hβ_nn]
    have hbound := correlationInfinite_diff_le_const_mul_diff Λ r_val s_val hrs J hJ b hb_pos hlt
      β₂ β₁ hβ₂.1 hβ hβ₁.2
    push_cast
    push_cast at hbound
    exact hbound

/-- **Helper for Step 234**: ordered Lipschitz bound on [0, b] in J (closed including J = 0).
For `0 ≤ J₁ ≤ J₂` with `J₂ ≤ b`, `0 < β`, `bβ·2d < 1`:
`corr_∞(J₂) - corr_∞(J₁) ≤ C · (J₂ - J₁)` where `C = β·M² + β·4d`. -/
private lemma correlationInfinite_diff_le_const_mul_diff_J
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * β * ↑(2 * d) < 1)
    (J₁ J₂ : ℝ) (hJ₁_nn : 0 ≤ J₁) (hJ : J₁ ≤ J₂) (hJ₂_le_b : J₂ ≤ b) :
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J₂, 0, β⟩ : IsingParams ℝ)
      {r_val, s_val} -
    correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J₁, 0, β⟩ : IsingParams ℝ)
      {r_val, s_val} ≤
    (β * (b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d))) ^ 2 + β * (4 * ↑d)) *
      (J₂ - J₁) := by
  rcases eq_or_lt_of_le hJ₁_nn with hJ₁0 | hJ₁_pos
  · rw [← hJ₁0, correlationInfinite_eq_zero_at_J_zero, sub_zero, sub_zero]
    rcases eq_or_lt_of_le (hJ₁0.le.trans hJ) with hJ₂0 | hJ₂_pos
    · rw [← hJ₂0, correlationInfinite_eq_zero_at_J_zero]
      have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
      have hM_nn : 0 ≤ b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d)) :=
        div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hβ.le) (Nat.cast_nonneg _)) hdenom_b.le
      positivity
    · have hbound := correlationInfinite_le_const_mul_J_of_high_temp
        Λ r_val s_val hrs β hβ b hb_pos hlt J₂ hJ₂_pos hJ₂_le_b
      simpa using hbound
  · have hlip_let := correlationInfinite_lipschitzOnWith_J_of_high_temp
      Λ r_val s_val hrs β hβ J₁ b hJ₁_pos (hJ.trans hJ₂_le_b) hlt
    have hlip : LipschitzOnWith
        ⟨β * (b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d))) ^ 2 + β * (4 * ↑d), by
          have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
          have hM_nn : 0 ≤ b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d)) :=
            div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hβ.le)
                         (Nat.cast_nonneg _)) hdenom_b.le
          positivity⟩
        (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val})
        (Set.Icc J₁ b) := hlip_let
    have hJ₁_in : J₁ ∈ Set.Icc J₁ b := Set.mem_Icc.mpr ⟨le_refl _, hJ.trans hJ₂_le_b⟩
    have hJ₂_in : J₂ ∈ Set.Icc J₁ b := Set.mem_Icc.mpr ⟨hJ, hJ₂_le_b⟩
    have hdist := hlip.dist_le_mul J₁ hJ₁_in J₂ hJ₂_in
    have hcorr_nn :
        0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J₂, 0, β⟩ : IsingParams ℝ) {r_val, s_val} -
            correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J₁, 0, β⟩ : IsingParams ℝ) {r_val, s_val} := by
      have hmono := correlationInfinite_monotoneOn_J_zero_closed Λ r_val s_val β hβ b
      have h1 : J₁ ∈ Set.Icc (0 : ℝ) b := Set.mem_Icc.mpr ⟨hJ₁_pos.le, hJ.trans hJ₂_le_b⟩
      have h2 : J₂ ∈ Set.Icc (0 : ℝ) b := Set.mem_Icc.mpr ⟨hJ₁_pos.le.trans hJ, hJ₂_le_b⟩
      linarith [hmono h1 h2 hJ]
    have hJ_nn : 0 ≤ J₂ - J₁ := by linarith
    simp only [Real.dist_eq] at hdist
    rw [abs_sub_comm J₁ J₂, abs_of_nonneg hJ_nn,
        abs_sub_comm
          (correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J₁, 0, β⟩ : IsingParams ℝ) {r_val, s_val})
          (correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J₂, 0, β⟩ : IsingParams ℝ) {r_val, s_val}),
        abs_of_nonneg hcorr_nn] at hdist
    push_cast at hdist
    convert hdist using 2
    push_cast; ring

/-- **LipschitzOnWith of corr_∞ on closed [0, b] (including J = 0) in J** (Step 234):
For `0 < β`, `0 < b`, `bβ·2d < 1`: `J ↦ corr_∞(J)` is `C`-Lipschitz on `[0, b]` in J
with the same constant `C = β·M² + β·4d` as Step 222.

Direct J-direction analogue of Step 180. Strengthens Step 222 from `[a, b]` (a > 0)
to closed `[0, b]`. -/
theorem correlationInfinite_lipschitzOnWith_J_zero_closed
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * β * ↑(2 * d) < 1) :
    LipschitzOnWith ⟨β * (b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d))) ^ 2 + β * (4 * ↑d), by
        have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
        have hM_nn : 0 ≤ b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d)) :=
          div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hβ.le)
                       (Nat.cast_nonneg _)) hdenom_b.le
        have := hM_nn
        positivity⟩
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc 0 b) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro J₁ hJ₁ J₂ hJ₂
  rcases le_total J₁ J₂ with hJ_le | hJ_le
  · have hcorr_nn :
        0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J₂, 0, β⟩ : IsingParams ℝ) {r_val, s_val} -
            correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J₁, 0, β⟩ : IsingParams ℝ) {r_val, s_val} := by
      have hmono := correlationInfinite_monotoneOn_J_zero_closed Λ r_val s_val β hβ b
      linarith [hmono hJ₁ hJ₂ hJ_le]
    have hJ_nn : 0 ≤ J₂ - J₁ := by linarith
    rw [Real.dist_eq, Real.dist_eq, abs_sub_comm J₁ J₂,
        abs_sub_comm
          ((fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) J₁)
          ((fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) J₂),
        abs_of_nonneg hcorr_nn, abs_of_nonneg hJ_nn]
    have hbound := correlationInfinite_diff_le_const_mul_diff_J Λ r_val s_val hrs β hβ b hb_pos hlt
      J₁ J₂ hJ₁.1 hJ_le hJ₂.2
    push_cast
    push_cast at hbound
    exact hbound
  · have hcorr_nn :
        0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J₁, 0, β⟩ : IsingParams ℝ) {r_val, s_val} -
            correlationInfinite (IsingModel.latticeGraph d) Λ
              (⟨J₂, 0, β⟩ : IsingParams ℝ) {r_val, s_val} := by
      have hmono := correlationInfinite_monotoneOn_J_zero_closed Λ r_val s_val β hβ b
      linarith [hmono hJ₂ hJ₁ hJ_le]
    have hJ_nn : 0 ≤ J₁ - J₂ := by linarith
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg hcorr_nn, abs_of_nonneg hJ_nn]
    have hbound := correlationInfinite_diff_le_const_mul_diff_J Λ r_val s_val hrs β hβ b hb_pos hlt
      J₂ J₁ hJ₂.1 hJ_le hJ₁.2
    push_cast
    push_cast at hbound
    exact hbound

end Ambient
end IsingModel
