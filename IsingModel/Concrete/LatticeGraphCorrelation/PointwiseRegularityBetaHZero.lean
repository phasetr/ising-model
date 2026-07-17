import IsingModel.Lattice
import IsingModel.AmbientLattice.BetaDerivative
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Compatibility-named ℤ^d correlationAlongEx β-direction (h=0) wrappers

Narrow child module for four compatibility-named ℤ^d
`correlationAlongExhaustion_*_beta` wrappers (at `h = 0`)
extracted from `PointwiseRegularity.lean`:

* `correlationAlongExhaustion_continuousAt_beta`,
* `correlationAlongExhaustion_continuous_beta`,
* `correlationAlongExhaustion_differentiableAt_beta`,
* `correlationAlongExhaustion_differentiable_beta`.

Each result is a thin pass-through of the ambient
`Ambient.correlationAlongExhaustion_*_beta_gen` lemma at
`G := IsingModel.latticeGraph d` and `h = 0`. The theorem names are
unchanged from the former `PointwiseRegularity` declarations.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **correlationAlongExhaustion ContinuousAt β at h = 0**. -/
theorem correlationAlongExhaustion_continuousAt_beta
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (A : Finset (Fin d → ℤ)) (J β : ℝ) (n : ℕ) :
    ContinuousAt
      (fun β' => Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β'⟩ : IsingParams ℝ) A n)
      β :=
  Ambient.correlationAlongExhaustion_continuousAt_beta_gen
    (IsingModel.latticeGraph d) Λ J β A n

/-- **correlationAlongExhaustion Continuous in β over the whole ℝ at h = 0**. -/
theorem correlationAlongExhaustion_continuous_beta
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (A : Finset (Fin d → ℤ)) (J : ℝ) (n : ℕ) :
    Continuous
      (fun β' => Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β'⟩ : IsingParams ℝ) A n) :=
  Ambient.correlationAlongExhaustion_continuous_beta_gen
    (IsingModel.latticeGraph d) Λ J A n

/-- **correlationAlongExhaustion DifferentiableAt β at h = 0**. -/
theorem correlationAlongExhaustion_differentiableAt_beta
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (A : Finset (Fin d → ℤ)) (J β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ
      (fun β' => Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β'⟩ : IsingParams ℝ) A n)
      β :=
  Ambient.correlationAlongExhaustion_differentiableAt_beta_gen
    (IsingModel.latticeGraph d) Λ J β A n

/-- **correlationAlongExhaustion Differentiable in β over the whole ℝ at h = 0**. -/
theorem correlationAlongExhaustion_differentiable_beta
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (A : Finset (Fin d → ℤ)) (J : ℝ) (n : ℕ) :
    Differentiable ℝ
      (fun β' => Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β'⟩ : IsingParams ℝ) A n) :=
  Ambient.correlationAlongExhaustion_differentiable_beta_gen
    (IsingModel.latticeGraph d) Λ J A n

end Ambient

end IsingModel
