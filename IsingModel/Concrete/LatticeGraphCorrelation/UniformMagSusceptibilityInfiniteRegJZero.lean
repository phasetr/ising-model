import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `susceptibilityInfinite_latticeGraph_*_J_zero` regularity wrappers

Narrow child module for four ℤ^d
`susceptibilityInfinite_latticeGraph_*_J_zero` regularity wrappers
extracted from `UniformMagSusceptibilityInfinite.lean`:

* `susceptibilityInfinite_latticeGraph_continuousOn_field_J_zero`,
* `susceptibilityInfinite_latticeGraph_continuousOn_beta_J_zero`,
* `susceptibilityInfinite_latticeGraph_differentiableOn_field_J_zero`,
* `susceptibilityInfinite_latticeGraph_differentiableOn_beta_J_zero`.

Each result is a thin pass-through of the ambient
`Ambient.susceptibilityInfinite_*_J_zero` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `UniformMagSusceptibilityInfinite` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d susceptibilityInfinite ContinuousOn h on Ici 0 at J = 0** (Step 265). -/
theorem susceptibilityInfinite_latticeGraph_continuousOn_field_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ) (hβ : 0 < β)
    (i : Fin d → ℤ) :
    ContinuousOn
      (fun h => susceptibilityInfinite (IsingModel.latticeGraph d) Λ ⟨0, h, β⟩ i)
      (Set.Ici (0 : ℝ)) :=
  susceptibilityInfinite_continuousOn_field_J_zero (IsingModel.latticeGraph d) Λ β hβ i

/-- **ℤ^d susceptibilityInfinite ContinuousOn β on Ioi 0 at J = 0** (Step 265). -/
theorem susceptibilityInfinite_latticeGraph_continuousOn_beta_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h : ℝ) (hh_nn : 0 ≤ h)
    (i : Fin d → ℤ) :
    ContinuousOn
      (fun β => susceptibilityInfinite (IsingModel.latticeGraph d) Λ ⟨0, h, β⟩ i)
      (Set.Ioi (0 : ℝ)) :=
  susceptibilityInfinite_continuousOn_beta_J_zero (IsingModel.latticeGraph d) Λ h hh_nn i

/-- **ℤ^d susceptibilityInfinite DifferentiableOn h on Ioi 0 at J = 0** (Step 265). -/
theorem susceptibilityInfinite_latticeGraph_differentiableOn_field_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ) (hβ : 0 < β)
    (i : Fin d → ℤ) :
    DifferentiableOn ℝ
      (fun h => susceptibilityInfinite (IsingModel.latticeGraph d) Λ ⟨0, h, β⟩ i)
      (Set.Ioi (0 : ℝ)) :=
  susceptibilityInfinite_differentiableOn_field_J_zero (IsingModel.latticeGraph d) Λ β hβ i

/-- **ℤ^d susceptibilityInfinite DifferentiableOn β on Ioi 0 at J = 0** (Step 265). -/
theorem susceptibilityInfinite_latticeGraph_differentiableOn_beta_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h : ℝ) (hh_nn : 0 ≤ h)
    (i : Fin d → ℤ) :
    DifferentiableOn ℝ
      (fun β => susceptibilityInfinite (IsingModel.latticeGraph d) Λ ⟨0, h, β⟩ i)
      (Set.Ioi (0 : ℝ)) :=
  susceptibilityInfinite_differentiableOn_beta_J_zero (IsingModel.latticeGraph d) Λ h hh_nn i

end Ambient

end IsingModel
