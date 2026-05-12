import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMagTwoPoint
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.Concrete.LatticeGraphCorrelation.UniformMag

/-!
# ℤ^d susceptibilityInfinite + magnetizationInfinite J_zero regularity wrappers

Narrow child module for 11 ℤ^d
`susceptibilityInfinite_latticeGraph_*` and
`magnetizationInfinite_latticeGraph_*` wrappers covering trivial
slices `J_zero` / `β_zero` / `zero_params` and the
`continuousOn` / `differentiableOn` regularity in field /
β-direction at `J = 0`. Theorem names are unchanged from the former
`UniformMag` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d susceptibilityInfinite at J = 0 site-wise** (Step 261, ferromagnetic). -/
theorem susceptibilityInfinite_latticeGraph_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (i : Fin d → ℤ) :
    susceptibilityInfinite (IsingModel.latticeGraph d) Λ ⟨0, h, β⟩ i
      = Real.tanh (β * h) * (1 - Real.tanh (β * h)) :=
  susceptibilityInfinite_J_zero (IsingModel.latticeGraph d) Λ h β hf i

/-- **ℤ^d susceptibilityInfinite at β = 0 site-wise** (Step 261). -/
theorem susceptibilityInfinite_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ)
    (i : Fin d → ℤ) :
    susceptibilityInfinite (IsingModel.latticeGraph d) Λ ⟨J, h, 0⟩ i = 0 :=
  susceptibilityInfinite_beta_zero (IsingModel.latticeGraph d) Λ J h i

/-- **ℤ^d susceptibilityInfinite at J = h = 0 site-wise** (Step 261). -/
theorem susceptibilityInfinite_latticeGraph_zero_params
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ) (hβ : 0 < β)
    (i : Fin d → ℤ) :
    susceptibilityInfinite (IsingModel.latticeGraph d) Λ ⟨0, 0, β⟩ i = 0 :=
  susceptibilityInfinite_zero_params (IsingModel.latticeGraph d) Λ β hβ i

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
