import IsingModel.Lattice
import IsingModel.AmbientLattice.BetaDerivative
import IsingModel.AmbientLattice.JDerivative

/-!
# Concrete pointwise regularity wrappers for the ℤ^d Ising correlation

This module contains concrete `latticeGraph` specializations of ambient
`ContinuousAt`, `DifferentiableAt`, `Continuous`, and `Differentiable` APIs for
β- and J-direction along-exhaustion correlation. It is split out of the original
concrete correlation module so future pointwise regularity work can build a
narrower child path.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ### ℤ^d along-ex pointwise (ContinuousAt / DifferentiableAt)
wrappers, lifting the ambient general-G versions from PR #1635 -/

/-! ## Moved: correlationAlongEx β-direction (h=0) wrappers

The four wrappers
`correlationAlongExhaustion_continuousAt_beta`,
`correlationAlongExhaustion_continuous_beta`,
`correlationAlongExhaustion_differentiableAt_beta`,
`correlationAlongExhaustion_differentiable_beta` (all at `h = 0`) now
live in `PointwiseRegularityBetaHZero.lean`. -/


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
