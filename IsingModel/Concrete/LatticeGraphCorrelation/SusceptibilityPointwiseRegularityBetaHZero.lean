import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularityAtDifferentiableAtBeta
import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularityAtContinuousAtBeta

/-!
# Compatibility-named ℤ^d susceptibility β-direction (h=0) regularity wrappers

Narrow child module for four compatibility-named ℤ^d
`susceptibilityAlongExhaustion_*_beta` wrappers (at `h = 0`)
extracted from `SusceptibilityPointwiseRegularity.lean`:

* `susceptibilityAlongExhaustion_continuousAt_beta`,
* `susceptibilityAlongExhaustion_differentiableAt_beta`,
* `susceptibilityAlongExhaustion_continuous_beta`,
* `susceptibilityAlongExhaustion_differentiable_beta`.

Each result is a thin pass-through of the ambient
`Ambient.susceptibilityAlongExhaustion_*_beta_gen` lemma at
`G := IsingModel.latticeGraph d` and `h = 0`. The theorem names are
unchanged from the former `SusceptibilityPointwiseRegularity`
declarations.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

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

end Ambient
end IsingModel
