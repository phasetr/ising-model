import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.Magnetization

/-!
# ℤ^d regularity of the along-exhaustion magnetization in the inverse temperature

Concrete `latticeGraph d` statements that, at a fixed site of `Fin d → ℤ` and a fixed stage
of an arbitrary `Ambient.Exhaustion`, the magnetization of that stage is continuous, and
differentiable over `ℝ`, as a function of the inverse temperature on the whole line, with the
coupling and the external field held fixed and unrestricted. Each requires a
`Fintype` instance on the edge set induced at every stage, and that instance is its entire
requirement: no `Prop`-typed hypothesis is carried here.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: `magnetizationAlongExhaustion` Continuous in β** (general h). -/
theorem magnetizationAlongExhaustion_latticeGraph_continuous_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    Continuous (fun β' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J, h, β'⟩ : IsingParams ℝ) i n) :=
  Ambient.magnetizationAlongExhaustion_continuous_beta
    (IsingModel.latticeGraph d) Λ J h i n

/-- **ℤ^d along-ex: `magnetizationAlongExhaustion` Differentiable in β** (general h). -/
theorem magnetizationAlongExhaustion_latticeGraph_differentiable_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    Differentiable ℝ (fun β' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J, h, β'⟩ : IsingParams ℝ) i n) :=
  Ambient.magnetizationAlongExhaustion_differentiable_beta
    (IsingModel.latticeGraph d) Λ J h i n

end Ambient
end IsingModel
