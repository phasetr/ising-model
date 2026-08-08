import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `susceptibilityInfinite` regularity on the zero-coupling slice

Records the parameter regularity of the ℤ^d infinite-volume susceptibility at zero
coupling: `ContinuousOn` in the external field over `Set.Ici 0` and in the inverse
temperature over `Set.Ioi 0`, and `DifferentiableOn ℝ` in each of those two variables
over `Set.Ioi 0`. The two statements varying the field fix `0 < β`; the two varying
the inverse temperature fix `0 ≤ h`.
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
