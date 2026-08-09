import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularityAtDifferentiableAtBeta
import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularityAtContinuousAtBeta

/-!
# ℤ^d regularity of the along-exhaustion susceptibility in β at an unrestricted field

Concrete `latticeGraph d` statements that, at a fixed site of `Fin d → ℤ` and a fixed stage
of an arbitrary `Ambient.Exhaustion`, the susceptibility of that stage is continuous, and
differentiable over `ℝ`, as a function of the inverse temperature — at a prescribed value,
and on the whole line — with the coupling and the external field held fixed and unrestricted.
No statement here carries a hypothesis or takes an instance argument.
-/

namespace IsingModel
namespace Ambient

/-- **susceptibilityAlongExhaustion ContinuousAt β at general h**. -/
theorem susceptibilityAlongExhaustion_continuousAt_beta_general_h
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (i : Fin d → ℤ) (J h β : ℝ) (n : ℕ) :
    ContinuousAt
      (fun β' => susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, h, β'⟩ : IsingParams ℝ) i n)
      β :=
  Ambient.susceptibilityAlongExhaustion_continuousAt_beta_gen
    (IsingModel.latticeGraph d) Λ J h β i n

/-- **susceptibilityAlongExhaustion DifferentiableAt β at general h**. -/
theorem susceptibilityAlongExhaustion_differentiableAt_beta_general_h
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (i : Fin d → ℤ) (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ
      (fun β' => susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, h, β'⟩ : IsingParams ℝ) i n)
      β :=
  Ambient.susceptibilityAlongExhaustion_differentiableAt_beta_gen
    (IsingModel.latticeGraph d) Λ J h β i n

/-- **susceptibilityAlongExhaustion Continuous in β at general h**. -/
theorem susceptibilityAlongExhaustion_continuous_beta_general_h
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (i : Fin d → ℤ) (J h : ℝ) (n : ℕ) :
    Continuous
      (fun β' => susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, h, β'⟩ : IsingParams ℝ) i n) :=
  Ambient.susceptibilityAlongExhaustion_continuous_beta_gen
    (IsingModel.latticeGraph d) Λ J h i n

/-- **susceptibilityAlongExhaustion Differentiable in β at general h**. -/
theorem susceptibilityAlongExhaustion_differentiable_beta_general_h
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (i : Fin d → ℤ) (J h : ℝ) (n : ℕ) :
    Differentiable ℝ
      (fun β' => susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, h, β'⟩ : IsingParams ℝ) i n) :=
  Ambient.susceptibilityAlongExhaustion_differentiable_beta_gen
    (IsingModel.latticeGraph d) Λ J h i n

end Ambient
end IsingModel
