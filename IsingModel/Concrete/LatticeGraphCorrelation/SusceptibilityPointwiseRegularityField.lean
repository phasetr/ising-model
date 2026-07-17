import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularity
import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularityAt
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete susceptibilityAlongExhaustion field-direction regularity

Narrow child module for four ℤ^d
`susceptibilityAlongExhaustion_{continuousAt,differentiableAt,continuous,differentiable}_field`
wrappers. Each wrapper is a thin pass-through to the corresponding
ambient `susceptibilityAlongExhaustion_*_field_gen` lemma at
`IsingModel.latticeGraph d`.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient


/-- **susceptibilityAlongExhaustion ContinuousAt h**. -/
theorem susceptibilityAlongExhaustion_continuousAt_field
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (i : Fin d → ℤ) (J h β : ℝ) (n : ℕ) :
    ContinuousAt
      (fun h' => susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, h', β⟩ : IsingParams ℝ) i n) h :=
  Ambient.susceptibilityAlongExhaustion_continuousAt_field_gen
    (IsingModel.latticeGraph d) Λ J h β i n

/-- **susceptibilityAlongExhaustion DifferentiableAt h**. -/
theorem susceptibilityAlongExhaustion_differentiableAt_field
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (i : Fin d → ℤ) (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ
      (fun h' => susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, h', β⟩ : IsingParams ℝ) i n) h :=
  Ambient.susceptibilityAlongExhaustion_differentiableAt_field_gen
    (IsingModel.latticeGraph d) Λ J h β i n

/-- **susceptibilityAlongExhaustion Continuous in h**. -/
theorem susceptibilityAlongExhaustion_continuous_field
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (i : Fin d → ℤ) (J β : ℝ) (n : ℕ) :
    Continuous
      (fun h' => susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, h', β⟩ : IsingParams ℝ) i n) :=
  Ambient.susceptibilityAlongExhaustion_continuous_field_gen
    (IsingModel.latticeGraph d) Λ J β i n

/-- **susceptibilityAlongExhaustion Differentiable in h**. -/
theorem susceptibilityAlongExhaustion_differentiable_field
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (i : Fin d → ℤ) (J β : ℝ) (n : ℕ) :
    Differentiable ℝ
      (fun h' => susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, h', β⟩ : IsingParams ℝ) i n) :=
  Ambient.susceptibilityAlongExhaustion_differentiable_field_gen
    (IsingModel.latticeGraph d) Λ J β i n


end Ambient
end IsingModel
