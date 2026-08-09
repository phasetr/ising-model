import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempZeroBoundary
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempContinuousAt
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempZeroBoundaryContinuousOnClosed

/-!
# ℤ^d continuity of the two-point function on the half-open high-temperature interval

Instantiates at `IsingModel.latticeGraph d`, for an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ` and two distinct sites at zero external field, the continuity of the
infinite-volume correlation on the half-open interval `Set.Ico 0 c`, closed at the origin
and open at the endpoint `c`, the reciprocal of `2 * d` times the parameter held fixed. The
statement is given in the inverse-temperature direction and in the coupling direction, and
each assumes `1 ≤ d`, distinctness of the two sites, and strict positivity of the parameter
held fixed.
-/

namespace IsingModel
namespace Ambient

/-- **ContinuousOn corr_∞ on Ico 0 β_c (half-open high-temperature interval)** (Step 182):
For `0 < J`, `1 ≤ d`: `β ↦ corr_∞(β)` is continuous on `Ico 0 (1/(J·2d))`
(closed at 0, open at β_c).

Combines Step 173 (continuity on Ioo 0 β_c) with Step 177 (continuity on Icc 0 b).

Proof: for each β₀ in the interval:
- β₀ > 0: use Step 175 ContinuousAt
- β₀ = 0: use Step 177 with b = (β_c)/2 (which is < β_c). -/
theorem correlationInfinite_continuousOn_beta_of_high_temp_Ico
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J) :
    ContinuousOn
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ico (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  have h2d_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
    exact_mod_cast this
  have hJ2d_pos : 0 < J * ↑(2 * d) := mul_pos hJ_pos h2d_pos
  have hβc_pos : 0 < 1 / (J * ↑(2 * d)) := one_div_pos.mpr hJ2d_pos
  intro β₀ hβ₀
  rcases eq_or_lt_of_le hβ₀.1 with hβ₀0 | hβ₀_pos
  · -- β₀ = 0: use Step 177 with b = β_c/2
    subst hβ₀0
    set b' : ℝ := (1 / (J * ↑(2 * d))) / 2 with hb'_def
    have hb'_pos : 0 < b' := by positivity
    have hb'_lt_βc : b' < 1 / (J * ↑(2 * d)) := by
      have : b' = (1 / (J * ↑(2 * d))) / 2 := rfl
      linarith
    have hlt : b' * J * ↑(2 * d) < 1 := by
      have h1 : b' * (J * ↑(2 * d)) < 1 := by
        have := (lt_div_iff₀ hJ2d_pos).mp hb'_lt_βc
        linarith [this]
      linarith [h1]
    have hcont_closed := correlationInfinite_continuousOn_beta_of_high_temp_zero_closed
      hd Λ r_val s_val hrs J hJ_pos b' hb'_pos hlt
    -- ContinuousOn [0, b'] ⇒ ContinuousWithinAt at 0 within [0, b']
    have hcwa := hcont_closed 0 (Set.mem_Icc.mpr ⟨le_refl _, hb'_pos.le⟩)
    -- Need: ContinuousWithinAt at 0 within Ico 0 β_c
    -- Use the fact that nhdsWithin (Icc 0 b') 0 contains points in (Ico 0 β_c) near 0
    apply hcwa.mono_of_mem_nhdsWithin
    -- Need: Set.Icc 0 b' ∈ 𝓝[Ico 0 β_c] 0
    rw [mem_nhdsWithin]
    refine ⟨Set.Iio b', isOpen_Iio, ?_, ?_⟩
    · exact hb'_pos
    · intro x hx
      have hx_lt_b' : x < b' := hx.1
      have hx_in_Ico : x ∈ Set.Ico (0 : ℝ) (1 / (J * ↑(2 * d))) := hx.2
      exact Set.mem_Icc.mpr ⟨hx_in_Ico.1, hx_lt_b'.le⟩
  · -- β₀ > 0: use Step 175
    have hβ₀_in_open : β₀ ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) := ⟨hβ₀_pos, hβ₀.2⟩
    exact (correlationInfinite_continuousAt_beta_of_high_temp
      hd Λ r_val s_val hrs J hJ_pos β₀ hβ₀_in_open).continuousWithinAt

/-- **ContinuousOn corr_∞ on Ico 0 J_c (half-open) in J** (Step 236):
For `0 < β`, `1 ≤ d`: `J ↦ corr_∞(J)` is continuous on `Ico 0 (1/(β·2d))`
(closed at 0, open at J_c). Direct J-direction analogue of Step 182. -/
theorem correlationInfinite_continuousOn_J_of_high_temp_Ico
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β) :
    ContinuousOn
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ico (0 : ℝ) (1 / (β * ↑(2 * d)))) := by
  have h2d_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
    exact_mod_cast this
  have hβ2d_pos : 0 < β * ↑(2 * d) := mul_pos hβ_pos h2d_pos
  have hJc_pos : 0 < 1 / (β * ↑(2 * d)) := one_div_pos.mpr hβ2d_pos
  intro J₀ hJ₀
  rcases eq_or_lt_of_le hJ₀.1 with hJ₀0 | hJ₀_pos
  · subst hJ₀0
    set b' : ℝ := (1 / (β * ↑(2 * d))) / 2 with hb'_def
    have hb'_pos : 0 < b' := by positivity
    have hb'_lt_Jc : b' < 1 / (β * ↑(2 * d)) := by
      have : b' = (1 / (β * ↑(2 * d))) / 2 := rfl
      linarith
    have hlt : b' * β * ↑(2 * d) < 1 := by
      have h1 : b' * (β * ↑(2 * d)) < 1 := by
        have := (lt_div_iff₀ hβ2d_pos).mp hb'_lt_Jc
        linarith [this]
      linarith [h1]
    have hcont_closed := correlationInfinite_continuousOn_J_of_high_temp_zero_closed
      hd Λ r_val s_val hrs β hβ_pos b' hb'_pos hlt
    have hcwa := hcont_closed 0 (Set.mem_Icc.mpr ⟨le_refl _, hb'_pos.le⟩)
    apply hcwa.mono_of_mem_nhdsWithin
    rw [mem_nhdsWithin]
    refine ⟨Set.Iio b', isOpen_Iio, ?_, ?_⟩
    · exact hb'_pos
    · intro x hx
      have hx_lt_b' : x < b' := hx.1
      have hx_in_Ico : x ∈ Set.Ico (0 : ℝ) (1 / (β * ↑(2 * d))) := hx.2
      exact Set.mem_Icc.mpr ⟨hx_in_Ico.1, hx_lt_b'.le⟩
  · have hJ₀_in_open : J₀ ∈ Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d))) := ⟨hJ₀_pos, hJ₀.2⟩
    exact (correlationInfinite_continuousAt_J_of_high_temp
      hd Λ r_val s_val hrs β hβ_pos J₀ hJ₀_in_open).continuousWithinAt

end Ambient
end IsingModel
