import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d magnetizationInfinite J=0 regularity wrappers

Narrow child module for four ℤ^d
`magnetizationInfinite_latticeGraph_*_J_zero` regularity wrappers (Step 267)
extracted from `UniformMagSusceptibilityInfinite.lean`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d magnetizationInfinite ContinuousOn h on Ici 0 at J = 0** (Step 267). -/
theorem magnetizationInfinite_latticeGraph_continuousOn_field_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ) (hβ : 0 < β)
    (i : Fin d → ℤ) :
    ContinuousOn
      (fun h => magnetizationInfinite (IsingModel.latticeGraph d) Λ ⟨0, h, β⟩ i)
      (Set.Ici (0 : ℝ)) :=
  magnetizationInfinite_continuousOn_field_J_zero (IsingModel.latticeGraph d) Λ β hβ i

/-- **ℤ^d magnetizationInfinite ContinuousOn β on Ioi 0 at J = 0** (Step 267). -/
theorem magnetizationInfinite_latticeGraph_continuousOn_beta_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h : ℝ) (hh_nn : 0 ≤ h)
    (i : Fin d → ℤ) :
    ContinuousOn
      (fun β => magnetizationInfinite (IsingModel.latticeGraph d) Λ ⟨0, h, β⟩ i)
      (Set.Ioi (0 : ℝ)) :=
  magnetizationInfinite_continuousOn_beta_J_zero (IsingModel.latticeGraph d) Λ h hh_nn i

/-- **ℤ^d magnetizationInfinite DifferentiableOn h on Ioi 0 at J = 0** (Step 267). -/
theorem magnetizationInfinite_latticeGraph_differentiableOn_field_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ) (hβ : 0 < β)
    (i : Fin d → ℤ) :
    DifferentiableOn ℝ
      (fun h => magnetizationInfinite (IsingModel.latticeGraph d) Λ ⟨0, h, β⟩ i)
      (Set.Ioi (0 : ℝ)) :=
  magnetizationInfinite_differentiableOn_field_J_zero (IsingModel.latticeGraph d) Λ β hβ i

/-- **ℤ^d magnetizationInfinite DifferentiableOn β on Ioi 0 at J = 0** (Step 267). -/
theorem magnetizationInfinite_latticeGraph_differentiableOn_beta_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h : ℝ) (hh_nn : 0 ≤ h)
    (i : Fin d → ℤ) :
    DifferentiableOn ℝ
      (fun β => magnetizationInfinite (IsingModel.latticeGraph d) Λ ⟨0, h, β⟩ i)
      (Set.Ioi (0 : ℝ)) :=
  magnetizationInfinite_differentiableOn_beta_J_zero (IsingModel.latticeGraph d) Λ h hh_nn i

end Ambient
end IsingModel
