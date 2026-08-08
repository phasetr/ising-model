import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `susceptibilityInfinite` trivial-slice wrappers

Evaluates the ℤ^d infinite-volume susceptibility on the degenerate parameter slices, where
the model decouples and the susceptibility collapses to its free value.
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

end Ambient

end IsingModel
