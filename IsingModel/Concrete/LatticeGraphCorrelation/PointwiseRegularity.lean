import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Lattice
import IsingModel.AmbientLattice.BetaDerivative
import IsingModel.AmbientLattice.JDerivative

/-!
# Concrete pointwise regularity wrappers for the ℤ^d Ising correlation

This module contains concrete `latticeGraph` specializations of ambient
`ContinuousAt`, `DifferentiableAt`, `Continuous`, and `Differentiable` APIs for
β- and J-direction along-exhaustion correlation. It is split out of the legacy
concrete correlation module so future pointwise regularity work can build a
narrower child path.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ### ℤ^d along-ex pointwise (ContinuousAt / DifferentiableAt)
wrappers, lifting the ambient general-G versions from PR #1635 -/

/-! #### Legacy-compatible β-direction names -/

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

/-! #### J-direction latticeGraph-named wrappers -/

/-- **ℤ^d along-ex: `correlationAlongExhaustion` ContinuousAt J**. -/
theorem correlationAlongExhaustion_latticeGraph_continuousAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    ContinuousAt (fun J' =>
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J', h, β⟩ : IsingParams ℝ) A n) J :=
  Ambient.correlationAlongExhaustion_continuousAt_J_gen
    (IsingModel.latticeGraph d) Λ J h β A n

/-- **ℤ^d along-ex: `correlationAlongExhaustion` DifferentiableAt J**. -/
theorem correlationAlongExhaustion_latticeGraph_differentiableAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    DifferentiableAt ℝ (fun J' =>
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J', h, β⟩ : IsingParams ℝ) A n) J :=
  Ambient.correlationAlongExhaustion_differentiableAt_J_gen
    (IsingModel.latticeGraph d) Λ J h β A n



end Ambient

end IsingModel
