import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempZeroBoundary
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempZeroBoundaryContinuousOnClosed
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempZeroBoundaryContinuousOnIco
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempLipschitzContinuousOnOpen
import IsingModel.AmbientLattice.TruncatedFunctions

/-!
# Truncated two-point high-temperature wrappers at ℤ^d

This module contains the concrete high-temperature regularity wrappers for the
infinite-volume Ursell two-point function `truncated2Infinite` at `h = 0`,
split from the original `Inequalities` module. Every wrapper reduces to the
corresponding `correlationInfinite {r, s}` statement via
`truncated2Infinite_h_zero`:

* Step 185 (β-direction): `ContinuousOn` on `Ioo 0 β_c`, on closed `Icc 0 b`,
  and on half-open `Ico 0 β_c`.
* Step 239 (J-direction analogue of Step 185): `ContinuousOn` on `Ioo 0 J_c`,
  on closed `Icc 0 b`, and on half-open `Ico 0 J_c`.
* Step 186 (β-direction): `LipschitzOnWith` on `Icc a b` and on `Icc 0 b`,
  almost-everywhere `DifferentiableWithinAt` on `Ici 0`.
* Step 187 (β-direction): `MonotoneOn` on `Ici 0`.
* Step 240 (J-direction analogue of Step 186 / 187): `LipschitzOnWith` on
  `Icc a b` and on `Icc 0 b`, almost-everywhere `DifferentiableWithinAt` on
  `Ici 0`, and `MonotoneOn` on `Ici 0`.
* Step 241: `ContinuousAt` at every interior point of `Ioo 0 β_c` /
  `Ioo 0 J_c` (full neighborhood, not just within-set).
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

/-! ## Moved: truncated2Infinite β-direction Lipschitz/ae-diff/MonotoneOn

The four β-direction wrappers
`truncated2Infinite_lipschitzOnWith_beta_of_high_temp`,
`truncated2Infinite_lipschitzOnWith_beta_zero_closed`,
`truncated2Infinite_ae_differentiableWithinAt_beta_Ici_zero`,
`truncated2Infinite_monotoneOn_beta_Ici_zero` now live in
`LatticeMassTruncated2HighTempBetaLipschitz.lean`. -/

/-! ## Moved: truncated2Infinite J-direction Lipschitz/ae diff/MonotoneOn

The four wrappers
`truncated2Infinite_lipschitzOnWith_J_of_high_temp`,
`truncated2Infinite_lipschitzOnWith_J_zero_closed`,
`truncated2Infinite_ae_differentiableWithinAt_J_Ici_zero`,
`truncated2Infinite_monotoneOn_J_Ici_zero` now live in
`LatticeMassTruncated2HighTempJDirection.lean`. -/


/-! ## Moved: truncated2Infinite continuousAt pair

The two wrappers
`truncated2Infinite_continuousAt_{beta,J}_of_high_temp` now live in
`LatticeMassTruncated2HighTempContinuousAt.lean`. -/


end Ambient

end IsingModel
