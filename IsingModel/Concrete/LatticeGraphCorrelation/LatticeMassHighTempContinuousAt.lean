import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempLipschitzContinuousOnOpen

/-!
# correlationInfinite continuousAt wrappers on Ioo 0 _c

Narrow child module for two ℤ^d
`correlationInfinite_continuousAt_{beta,J}_of_high_temp` wrappers. Each
statement promotes the corresponding `ContinuousOn ... _open` lemma to
`ContinuousAt` at an interior point.
-/

namespace IsingModel
namespace Ambient

/-- **ContinuousAt of corr_∞ at every β in the open high-temperature interval** (Step 175):
For `0 < J`, `1 ≤ d`, every `β₀ ∈ Ioo 0 (1/(J·2d))`: corr_∞ is continuous at β₀
(as a function ℝ → ℝ, no within-restriction).

Proof: Since `Ioo 0 β_c` is open, it's a neighborhood of any of its points. So
ContinuousOn (Step 173) restricted to a neighborhood gives ContinuousAt. -/
theorem correlationInfinite_continuousAt_beta_of_high_temp
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J)
    (β₀ : ℝ) (hβ₀ : β₀ ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) :
    ContinuousAt
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      β₀ := by
  have hcont_open := correlationInfinite_continuousOn_beta_of_high_temp_open
    hd Λ r_val s_val hrs J hJ_pos
  have h_nhd : Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) ∈ nhds β₀ :=
    IsOpen.mem_nhds isOpen_Ioo hβ₀
  exact (hcont_open β₀ hβ₀).continuousAt h_nhd

/-- **ContinuousAt of corr_∞ at every J ∈ Ioo 0 J_c** (Step 229):
For `0 < β`, `1 ≤ d`, every `J₀ ∈ Ioo 0 (1/(β·2d))`: corr_∞ is continuous at J₀
(as a function ℝ → ℝ, full neighborhood).

Direct J-direction analogue of Step 175. Proof: open set is a neighborhood of any
interior point ⇒ Step 227 ContinuousOn restricts to ContinuousAt. -/
theorem correlationInfinite_continuousAt_J_of_high_temp
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β)
    (J₀ : ℝ) (hJ₀ : J₀ ∈ Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d)))) :
    ContinuousAt
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      J₀ := by
  have hcont_open := correlationInfinite_continuousOn_J_of_high_temp_open
    hd Λ r_val s_val hrs β hβ_pos
  have h_nhd : Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d))) ∈ nhds J₀ :=
    IsOpen.mem_nhds isOpen_Ioo hJ₀
  exact (hcont_open J₀ hJ₀).continuousAt h_nhd

end Ambient
end IsingModel
