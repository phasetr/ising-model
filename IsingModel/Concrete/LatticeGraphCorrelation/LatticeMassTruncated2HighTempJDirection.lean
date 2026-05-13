import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempZeroBoundary
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempIciZero
import IsingModel.AmbientLattice.TruncatedFunctions

/-!
# Truncated two-point high-temperature J-direction wrappers at ℤ^d

Narrow child module for four ℤ^d `truncated2Infinite` J-direction wrappers
(Step 240) extracted from `LatticeMassTruncated2HighTemp.lean`:
`LipschitzOnWith` on `Icc a b` and on `Icc 0 b`, almost-everywhere
`DifferentiableWithinAt` on `Ici 0`, and `MonotoneOn` on `Ici 0`. Each is a
thin pass-through to the corresponding `correlationInfinite {r, s}` lemma
via `truncated2Infinite_h_zero`.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ## Step 240: truncated2Infinite J-direction Lipschitz/ae diff/MonotoneOn -/

/-- **truncated2Infinite LipschitzOnWith J on [a, b] at h = 0** (Step 240).
J-direction analogue of Step 186 (Icc a b). Wrapper of Step 222. -/
theorem truncated2Infinite_lipschitzOnWith_J_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * β * ↑(2 * d) < 1) :
    let M : ℝ := b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d))
    LipschitzOnWith ⟨β * M ^ 2 + β * (4 * ↑d), by
        have hdenom_b : 0 < 1 - b * β * ↑(2 * d) := by linarith
        have hb_pos : 0 < b := ha.trans_le hab
        have hM_nn : 0 ≤ b * β * ↑(2 * d) / (1 - b * β * ↑(2 * d)) :=
          div_nonneg (mul_nonneg (mul_nonneg hb_pos.le hβ.le)
                       (Nat.cast_nonneg _)) hdenom_b.le
        exact add_nonneg (mul_nonneg hβ.le (pow_nonneg hM_nn 2))
               (mul_nonneg hβ.le (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))⟩
      (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Icc a b) := by
  intro M
  have heq : (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext J
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_lipschitzOnWith_J_of_high_temp Λ r_val s_val hrs β hβ a b ha hab hlt

/-- **truncated2Infinite LipschitzOnWith J on closed [0, b] at h = 0** (Step 240).
J-direction analogue of Step 186 (Icc 0 b). Wrapper of Step 234. -/
theorem truncated2Infinite_lipschitzOnWith_J_zero_closed
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
      (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Icc 0 b) := by
  have heq : (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext J
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_lipschitzOnWith_J_zero_closed Λ r_val s_val hrs β hβ b hb_pos hlt

/-- **truncated2Infinite ae DifferentiableWithinAt on Ici 0 in J at h = 0** (Step 240).
J-direction analogue of Step 186 (ae version). Wrapper of Step 237. -/
theorem truncated2Infinite_ae_differentiableWithinAt_J_Ici_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (β : ℝ) (hβ : 0 < β) :
    ∀ᵐ J ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ici (0 : ℝ)),
    DifferentiableWithinAt ℝ
      (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Ici (0 : ℝ)) J := by
  have heq : (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext J
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_ae_differentiableWithinAt_J_Ici_zero Λ r_val s_val β hβ

/-- **truncated2Infinite MonotoneOn J on Ici 0 at h = 0** (Step 240).
J-direction analogue of Step 187. Wrapper of Step 237. -/
theorem truncated2Infinite_monotoneOn_J_Ici_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (β : ℝ) (hβ : 0 < β) :
    MonotoneOn
      (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Ici (0 : ℝ)) := by
  have heq : (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext J
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_monotoneOn_J_Ici_zero Λ r_val s_val β hβ

end Ambient
end IsingModel
