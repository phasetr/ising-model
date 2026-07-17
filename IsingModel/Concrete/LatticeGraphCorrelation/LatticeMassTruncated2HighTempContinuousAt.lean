import IsingModel.AmbientLattice.TruncatedFunctions
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempContinuousAt

/-!
# truncated2Infinite ContinuousAt at every interior point in β / J

Narrow child module for two ℤ^d
`truncated2Infinite_continuousAt_{beta,J}_of_high_temp` wrappers. Each
wrapper promotes the corresponding `_continuousOn_*_open` to
`ContinuousAt` at an interior point of `Ioo 0 _c`.
-/

namespace IsingModel
namespace Ambient

/-! ## Step 241: truncated2Infinite ContinuousAt at every interior point in β + J -/

/-- **truncated2Infinite ContinuousAt every β ∈ Ioo 0 β_c at h = 0** (Step 241).
For any β₀ ∈ Ioo 0 (1/(J·2d)): truncated2Infinite is ContinuousAt at β₀
(full neighborhood, not just within-set). Wrapper of Step 175. -/
theorem truncated2Infinite_continuousAt_beta_of_high_temp
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J)
    (β₀ : ℝ) (hβ₀ : β₀ ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) :
    ContinuousAt
      (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      β₀ := by
  have heq : (fun β => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext β
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_continuousAt_beta_of_high_temp hd Λ r_val s_val hrs J hJ_pos β₀ hβ₀

/-- **truncated2Infinite ContinuousAt every J ∈ Ioo 0 J_c at h = 0** (Step 241).
For any J₀ ∈ Ioo 0 (1/(β·2d)): truncated2Infinite is ContinuousAt at J₀
(full neighborhood, not just within-set). Wrapper of Step 229. -/
theorem truncated2Infinite_continuousAt_J_of_high_temp
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β)
    (J₀ : ℝ) (hJ₀ : J₀ ∈ Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d)))) :
    ContinuousAt
      (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val)
      J₀ := by
  have heq : (fun J => truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) r_val s_val) =
             (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val}) := by
    funext J
    exact truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β r_val s_val
  rw [heq]
  exact correlationInfinite_continuousAt_J_of_high_temp hd Λ r_val s_val hrs β hβ_pos J₀ hJ₀

end Ambient
end IsingModel
