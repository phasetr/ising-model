import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempZeroBoundary
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempZeroBoundaryContinuousOnClosed
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempZeroBoundaryContinuousOnIco
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempLipschitzContinuousOnOpen
import IsingModel.AmbientLattice.TruncatedFunctions

/-!
# ℤ^d continuity of the truncated two-point function at high temperature (§17.5)

Instantiates at `IsingModel.latticeGraph d`, for an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ` and two distinct sites at zero external field, the continuity of the
infinite-volume truncated two-point function, in the inverse-temperature direction and in the
coupling direction, on the open interval `Set.Ioo 0 c`, on the closed interval `Set.Icc 0 b`
and on the half-open interval `Set.Ico 0 c`, where `c` is the reciprocal of `2 * d` times the
parameter held fixed. Every statement assumes `1 ≤ d`, distinctness of the two sites and
strict positivity of the parameter held fixed; the statements on `Set.Icc 0 b` assume in
addition `0 < b` and that `b` times the parameter held fixed times `2 * d` is below one.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **truncated2Infinite ContinuousOn β at h = 0 on Ioo 0 β_c** (Step 185, GJ §17.5):
For `0 < J`, `1 ≤ d`, `r ≠ s`: the infinite-volume Ursell 2-point function is continuous
in β on the open high-temperature interval.

Proof: at h = 0, `truncated2Infinite = correlationInfinite {r, s}` (`truncated2Infinite_h_zero`).
Apply Step 173. -/
theorem truncated2Infinite_continuousOn_beta_of_high_temp_open
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J) :
    ContinuousOn
      (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  have heq : (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext β
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_continuousOn_beta_of_high_temp_open hd Λ r_val s_val hrs J hJ_pos

/-- **truncated2Infinite ContinuousOn β on closed [0, b]** (Step 185 closed variant). -/
theorem truncated2Infinite_continuousOn_beta_of_high_temp_zero_closed
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * J * ↑(2 * d) < 1) :
    ContinuousOn
      (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Icc (0 : ℝ) b) := by
  have heq : (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext β
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_continuousOn_beta_of_high_temp_zero_closed
    hd Λ r_val s_val hrs J hJ_pos b hb_pos hlt

/-- **truncated2Infinite ContinuousOn β on Ico 0 β_c (half-open)** (Step 185 Ico variant). -/
theorem truncated2Infinite_continuousOn_beta_of_high_temp_Ico
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J) :
    ContinuousOn
      (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Ico (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  have heq : (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext β
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_continuousOn_beta_of_high_temp_Ico hd Λ r_val s_val hrs J hJ_pos

/-- **truncated2Infinite ContinuousOn J on Ioo 0 J_c at h = 0** (Step 239):
J-direction analogue of Step 185 (Ioo variant). At h = 0, truncated2Infinite is
correlationInfinite {r, s}, so the result reduces to Step 227. -/
theorem truncated2Infinite_continuousOn_J_of_high_temp_open
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β) :
    ContinuousOn
      (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d)))) := by
  have heq : (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext J
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_continuousOn_J_of_high_temp_open hd Λ r_val s_val hrs β hβ_pos

/-- **truncated2Infinite ContinuousOn J on closed [0, b] at h = 0** (Step 239 closed variant).
J-direction analogue of Step 185 closed variant. -/
theorem truncated2Infinite_continuousOn_J_of_high_temp_zero_closed
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * β * ↑(2 * d) < 1) :
    ContinuousOn
      (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Icc (0 : ℝ) b) := by
  have heq : (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext J
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_continuousOn_J_of_high_temp_zero_closed
    hd Λ r_val s_val hrs β hβ_pos b hb_pos hlt

/-- **truncated2Infinite ContinuousOn J on Ico 0 J_c (half-open)** (Step 239 Ico variant). -/
theorem truncated2Infinite_continuousOn_J_of_high_temp_Ico
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β) :
    ContinuousOn
      (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      (Set.Ico (0 : ℝ) (1 / (β * ↑(2 * d)))) := by
  have heq : (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext J
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_continuousOn_J_of_high_temp_Ico hd Λ r_val s_val hrs β hβ_pos

end Ambient

end IsingModel
