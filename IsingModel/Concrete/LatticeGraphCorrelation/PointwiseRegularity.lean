import IsingModel.Lattice
import IsingModel.AmbientLattice.JDerivative

/-!
# ℤ^d pointwise regularity of the along-exhaustion correlation in the coupling

Concrete `latticeGraph d` statements that, for a fixed finite subset of `Fin d → ℤ` and at a
fixed stage of an arbitrary `Ambient.Exhaustion`, the correlation of that subset is
continuous, and differentiable over `ℝ`, at a prescribed value of the coupling, with the
external field and the inverse temperature held fixed and unrestricted. Each requires a
`Fintype` instance on the edge set induced at every stage, and that instance is its entire
requirement: no `Prop`-typed hypothesis is carried here.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

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
