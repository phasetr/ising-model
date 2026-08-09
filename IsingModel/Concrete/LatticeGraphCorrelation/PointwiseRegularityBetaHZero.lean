import IsingModel.Lattice
import IsingModel.AmbientLattice.BetaDerivative
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d regularity of the along-exhaustion correlation in β at zero external field

Concrete `latticeGraph d` statements that, for a fixed finite subset of `Fin d → ℤ` and at a
fixed stage of an arbitrary `Ambient.Exhaustion`, the correlation of that subset at zero
external field is continuous, and differentiable over `ℝ`, as a function of the inverse
temperature — at a prescribed value, and on the whole line. The coupling is held fixed and
unrestricted. No statement here carries a hypothesis or takes an instance argument.
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
