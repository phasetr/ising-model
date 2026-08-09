import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.Magnetization

/-!
# ℤ^d pointwise regularity of the along-exhaustion magnetization in the inverse temperature

Concrete `latticeGraph d` statements that, at a fixed site of `Fin d → ℤ` and a fixed stage
of an arbitrary `Ambient.Exhaustion`, the magnetization of that stage is continuous, and
differentiable over `ℝ`, at a prescribed inverse temperature, with the coupling and the
external field held fixed and unrestricted. Each requires a `Fintype` instance on the edge
set induced at every stage, and that instance is its entire requirement: no `Prop`-typed
hypothesis is carried here.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: `magnetizationAlongExhaustion` ContinuousAt β** (general h). -/
theorem magnetizationAlongExhaustion_latticeGraph_continuousAt_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    ContinuousAt (fun β' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β'⟩ : IsingParams ℝ) i n) β :=
  Ambient.magnetizationAlongExhaustion_continuousAt_beta
    (IsingModel.latticeGraph d) Λ J h β i n

/-- **ℤ^d along-ex: `magnetizationAlongExhaustion` DifferentiableAt β** (general h). -/
theorem magnetizationAlongExhaustion_latticeGraph_differentiableAt_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    DifferentiableAt ℝ (fun β' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β'⟩ : IsingParams ℝ) i n) β :=
  Ambient.magnetizationAlongExhaustion_differentiableAt_beta
    (IsingModel.latticeGraph d) Λ J h β i n

end Ambient
end IsingModel
