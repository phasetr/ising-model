import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempLipschitz.Continuity

/-!
# Continuity of corr_∞ on open high-temperature intervals at ℤ^d

Narrow child module for two ℤ^d
`correlationInfinite_continuousOn_{beta,J}_of_high_temp_open` wrappers
(Steps 173 / 227) extracted from `LatticeMassHighTempLipschitz.lean`. Each
upgrades the closed-interval continuity package to `ContinuousOn` on the
open high-temperature interval `Ioo 0 _c` via a closed-neighborhood
exhaustion.
-/

namespace IsingModel
namespace Ambient

/-- **Continuity of corr_∞ on the open high-temperature interval** (Step 173):
For `0 < J`, `1 ≤ d`, the function `β ↦ corr_∞(β)` is continuous on the open
high-temperature interval `Ioo 0 (1/(J·2d))`.

Proof: For each β₀ in the open interval, choose a closed neighborhood `[a, b]`
inside the open interval. Step 169 gives continuity on `[a, b]`, hence at β₀.
Aggregating over β₀ gives continuity on the entire open interval. -/
theorem correlationInfinite_continuousOn_beta_of_high_temp_open
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J) :
    ContinuousOn
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  have h2d_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
    exact_mod_cast this
  have hJ2d_pos : 0 < J * ↑(2 * d) := mul_pos hJ_pos h2d_pos
  intro β₀ hβ₀
  have hβ₀_pos : 0 < β₀ := hβ₀.1
  have hβ₀_lt : β₀ < 1 / (J * ↑(2 * d)) := hβ₀.2
  -- Choose a closed neighborhood [a, b] with a < β₀ < b inside the open interval
  -- Pick a = β₀/2 and b = (β₀ + βc)/2 where βc = 1/(J·2d)
  have ha_pos : 0 < β₀ / 2 := by positivity
  have ha_lt_β₀ : β₀ / 2 < β₀ := by linarith
  have hβ₀_lt_b : β₀ < (β₀ + 1 / (J * ↑(2 * d))) / 2 := by linarith
  have hb_lt_βc : (β₀ + 1 / (J * ↑(2 * d))) / 2 < 1 / (J * ↑(2 * d)) := by linarith
  have ha_le_β₀ : β₀ / 2 ≤ β₀ := ha_lt_β₀.le
  have hβ₀_le_b : β₀ ≤ (β₀ + 1 / (J * ↑(2 * d))) / 2 := hβ₀_lt_b.le
  have hab : β₀ / 2 ≤ (β₀ + 1 / (J * ↑(2 * d))) / 2 := ha_le_β₀.trans hβ₀_le_b
  have hlt : (β₀ + 1 / (J * ↑(2 * d))) / 2 * J * ↑(2 * d) < 1 := by
    have h1 : (β₀ + 1 / (J * ↑(2 * d))) / 2 * (J * ↑(2 * d)) < 1 := by
      have := (lt_div_iff₀ hJ2d_pos).mp hb_lt_βc
      linarith [this]
    linarith [h1]
  have hcont_Icc := correlationInfinite_continuousOn_beta_of_high_temp
    Λ r_val s_val hrs J hJ_pos.le (β₀ / 2) ((β₀ + 1 / (J * ↑(2 * d))) / 2) ha_pos hab hlt
  apply ContinuousAt.continuousWithinAt
  have h_Icc_nhd : Set.Icc (β₀ / 2) ((β₀ + 1 / (J * ↑(2 * d))) / 2) ∈ nhds β₀ :=
    Icc_mem_nhds ha_lt_β₀ hβ₀_lt_b
  exact (hcont_Icc β₀ ⟨ha_le_β₀, hβ₀_le_b⟩).continuousAt h_Icc_nhd

/-- **Continuity of corr_∞ on Ioo 0 J_c in J** (Step 227):
For `0 < β`, `1 ≤ d`, `J ↦ corr_∞(J)` is continuous on the open
high-temperature interval `Ioo 0 (1/(β·2d))`.

Direct J-direction analogue of Step 173. Proof: for each J₀ in the open interval,
choose `[a, b] ⊂ Ioo 0 (1/(β·2d))` with `J₀ ∈ Ioo a b` (e.g., `a = J₀/2`,
`b = (J₀+J_c)/2`); Step 223 gives continuity on `[a, b]`, hence at J₀. -/
theorem correlationInfinite_continuousOn_J_of_high_temp_open
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β) :
    ContinuousOn
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d)))) := by
  have h2d_pos : (0 : ℝ) < ↑(2 * d) := by
    have : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
    exact_mod_cast this
  have hβ2d_pos : 0 < β * ↑(2 * d) := mul_pos hβ_pos h2d_pos
  intro J₀ hJ₀
  have hJ₀_pos : 0 < J₀ := hJ₀.1
  have hJ₀_lt : J₀ < 1 / (β * ↑(2 * d)) := hJ₀.2
  have ha_pos : 0 < J₀ / 2 := by positivity
  have ha_lt_J₀ : J₀ / 2 < J₀ := by linarith
  have hJ₀_lt_b : J₀ < (J₀ + 1 / (β * ↑(2 * d))) / 2 := by linarith
  have hb_lt_Jc : (J₀ + 1 / (β * ↑(2 * d))) / 2 < 1 / (β * ↑(2 * d)) := by linarith
  have ha_le_J₀ : J₀ / 2 ≤ J₀ := ha_lt_J₀.le
  have hJ₀_le_b : J₀ ≤ (J₀ + 1 / (β * ↑(2 * d))) / 2 := hJ₀_lt_b.le
  have hab : J₀ / 2 ≤ (J₀ + 1 / (β * ↑(2 * d))) / 2 := ha_le_J₀.trans hJ₀_le_b
  have hlt : (J₀ + 1 / (β * ↑(2 * d))) / 2 * β * ↑(2 * d) < 1 := by
    have h1 : (J₀ + 1 / (β * ↑(2 * d))) / 2 * (β * ↑(2 * d)) < 1 := by
      have := (lt_div_iff₀ hβ2d_pos).mp hb_lt_Jc
      linarith [this]
    linarith [h1]
  have hcont_Icc := correlationInfinite_continuousOn_J_of_high_temp
    Λ r_val s_val hrs β hβ_pos (J₀ / 2) ((J₀ + 1 / (β * ↑(2 * d))) / 2) ha_pos hab hlt
  apply ContinuousAt.continuousWithinAt
  have h_Icc_nhd : Set.Icc (J₀ / 2) ((J₀ + 1 / (β * ↑(2 * d))) / 2) ∈ nhds J₀ :=
    Icc_mem_nhds ha_lt_J₀ hJ₀_lt_b
  exact (hcont_Icc J₀ ⟨ha_le_J₀, hJ₀_le_b⟩).continuousAt h_Icc_nhd

end Ambient
end IsingModel
