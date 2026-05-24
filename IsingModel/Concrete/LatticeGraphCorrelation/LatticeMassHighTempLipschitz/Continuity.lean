import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempLipschitz.Lipschitz

/-!
# Lattice mass high-temp Lipschitz split — infinite-volume correlation continuity in beta and J

Part of the split high-temperature Lipschitz layer (Issue #1850).
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **Continuity of infinite-volume two-point function in β** (Step 169, GJ §17.5):
For any exhaustion `Λ`, vertices `r_val ≠ s_val`, `0 ≤ J`, `0 < a ≤ b`, `bJ·2d < 1`,
`β ↦ correlationInfinite (latticeGraph d) Λ ⟨J,0,β⟩ {r_val,s_val}` is continuous on `[a, b]`.

Follows immediately from the Lipschitz bound of Step 168.

Reference: Glimm–Jaffe §17.5 p.~312. -/
theorem correlationInfinite_continuousOn_beta_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1) :
    ContinuousOn
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc a b) :=
  (correlationInfinite_lipschitzOnWith_beta_of_high_temp Λ r_val s_val hrs J hJ a b ha hab
    hlt).continuousOn

/-- **Continuity of infinite-volume two-point function in J** (Step 223):
For any exhaustion `Λ`, vertices `r_val ≠ s_val`, `0 < β`, `0 < a ≤ b`, `bβ·2d < 1`,
`J ↦ correlationInfinite (latticeGraph d) Λ ⟨J,0,β⟩ {r_val,s_val}` is continuous on `[a, b]`.

Direct J-direction analogue of Step 169. Follows immediately from Step 222
(`correlationInfinite_lipschitzOnWith_J_of_high_temp`). -/
theorem correlationInfinite_continuousOn_J_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * β * ↑(2 * d) < 1) :
    ContinuousOn
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc a b) :=
  (correlationInfinite_lipschitzOnWith_J_of_high_temp Λ r_val s_val hrs β hβ a b ha hab
    hlt).continuousOn


end Ambient
end IsingModel
