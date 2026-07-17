import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularity
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete pointwise regularity wrappers for lattice susceptibility

This module contains concrete `latticeGraph` specializations and compatibility-named
compatibility names for ambient `ContinuousAt`, `DifferentiableAt`,
`Continuous`, and `Differentiable` APIs for per-parameter
`susceptibilityAlongExhaustion` regularity. It is split out of the original
concrete correlation module so future susceptibility pointwise work can build a
narrower child path.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ### Compatibility-named ℤ^d along-ex susceptibility regularity names -/

/-! ## Moved: susceptibilityAlongExhaustion β-direction (h=0) wrappers

The four wrappers
`susceptibilityAlongExhaustion_continuousAt_beta`,
`susceptibilityAlongExhaustion_differentiableAt_beta`,
`susceptibilityAlongExhaustion_continuous_beta`,
`susceptibilityAlongExhaustion_differentiable_beta` (all at `h = 0`)
now live in `SusceptibilityPointwiseRegularityBetaHZero.lean`. -/


/-! ## Moved: susceptibilityAlongExhaustion β general-h wrappers

The four `susceptibilityAlongExhaustion_*_beta_general_h` wrappers
(`continuousAt`, `differentiableAt`, `continuous`, `differentiable`)
now live in `SusceptibilityPointwiseRegularityGeneralH.lean`. -/


/-! ## Moved: susceptibilityAlongExhaustion field-direction regularity

The four wrappers
`susceptibilityAlongExhaustion_{continuousAt,differentiableAt,continuous,differentiable}_field`
now live in `SusceptibilityPointwiseRegularityField.lean`. -/

/-- **susceptibilityAlongExhaustion Continuous in J**. -/
theorem susceptibilityAlongExhaustion_continuous_J
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (i : Fin d → ℤ) (h β : ℝ) (n : ℕ) :
    Continuous
      (fun J' => susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J', h, β⟩ : IsingParams ℝ) i n) :=
  Ambient.susceptibilityAlongExhaustion_continuous_J_gen
    (IsingModel.latticeGraph d) Λ h β i n

/-- **susceptibilityAlongExhaustion Differentiable in J**. -/
theorem susceptibilityAlongExhaustion_differentiable_J
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (i : Fin d → ℤ) (h β : ℝ) (n : ℕ) :
    Differentiable ℝ
      (fun J' => susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J', h, β⟩ : IsingParams ℝ) i n) :=
  Ambient.susceptibilityAlongExhaustion_differentiable_J_gen
    (IsingModel.latticeGraph d) Λ h β i n

/-! ## Moved: ℤ^d-specialized susceptibilityAlongExhaustion pointwise wrappers

The six `susceptibilityAlongExhaustion_latticeGraph_*` wrappers
(`{continuousAt,differentiableAt}_{beta_general_h,field,J}`) now
live in `SusceptibilityPointwiseRegularityLatticeGraph.lean`. -/


end Ambient
end IsingModel
