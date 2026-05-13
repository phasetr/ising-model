import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularity

/-!
# Concrete pointwise regularity wrappers for lattice susceptibility

This module contains concrete `latticeGraph` specializations and legacy
compatibility names for ambient `ContinuousAt`, `DifferentiableAt`,
`Continuous`, and `Differentiable` APIs for per-parameter
`susceptibilityAlongExhaustion` regularity. It is split out of the legacy
concrete correlation module so future susceptibility pointwise work can build a
narrower child path.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ### Legacy-compatible ℤ^d along-ex susceptibility regularity names -/

/-- **susceptibilityAlongExhaustion ContinuousAt β at h = 0**. -/
theorem susceptibilityAlongExhaustion_continuousAt_beta
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (i : Fin d → ℤ) (J β : ℝ) (n : ℕ) :
    ContinuousAt
      (fun β' => susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β'⟩ : IsingParams ℝ) i n)
      β :=
  Ambient.susceptibilityAlongExhaustion_continuousAt_beta_gen
    (IsingModel.latticeGraph d) Λ J 0 β i n

/-- **susceptibilityAlongExhaustion DifferentiableAt β at h = 0**. -/
theorem susceptibilityAlongExhaustion_differentiableAt_beta
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (i : Fin d → ℤ) (J β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ
      (fun β' => susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β'⟩ : IsingParams ℝ) i n)
      β :=
  Ambient.susceptibilityAlongExhaustion_differentiableAt_beta_gen
    (IsingModel.latticeGraph d) Λ J 0 β i n

/-- **susceptibilityAlongExhaustion Continuous in β over the whole ℝ at h = 0**. -/
theorem susceptibilityAlongExhaustion_continuous_beta
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (i : Fin d → ℤ) (J : ℝ) (n : ℕ) :
    Continuous
      (fun β' => susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β'⟩ : IsingParams ℝ) i n) :=
  Ambient.susceptibilityAlongExhaustion_continuous_beta_gen
    (IsingModel.latticeGraph d) Λ J 0 i n

/-- **susceptibilityAlongExhaustion Differentiable in β over the whole ℝ at h = 0**. -/
theorem susceptibilityAlongExhaustion_differentiable_beta
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (i : Fin d → ℤ) (J : ℝ) (n : ℕ) :
    Differentiable ℝ
      (fun β' => susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β'⟩ : IsingParams ℝ) i n) :=
  Ambient.susceptibilityAlongExhaustion_differentiable_beta_gen
    (IsingModel.latticeGraph d) Λ J 0 i n

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

The six wrappers
`susceptibilityAlongExhaustion_latticeGraph_{continuousAt,differentiableAt}_{beta_general_h,field,J}`
now live in `SusceptibilityPointwiseRegularityLatticeGraph.lean`. -/


end Ambient
end IsingModel
