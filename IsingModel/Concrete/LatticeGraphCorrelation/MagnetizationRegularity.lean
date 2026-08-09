import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.Magnetization

/-!
# ℤ^d regularity of the along-exhaustion magnetization in field and coupling

Concrete `latticeGraph d` statements that, at a fixed site of `Fin d → ℤ` and a fixed stage
of an arbitrary `Ambient.Exhaustion`, the magnetization of that stage is continuous, and
differentiable over `ℝ`, as a function of the external field on the whole line, and likewise
as a function of the coupling, with the remaining parameters held fixed and unrestricted.
Each requires a `Fintype` instance on the edge set induced at every stage, and that instance
is its entire requirement: no `Prop`-typed hypothesis is carried here.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: magnetization Continuous in `h`**. -/
theorem magnetizationAlongExhaustion_latticeGraph_continuous_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    Continuous (fun h' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J, h', β⟩ : IsingParams ℝ) i n) :=
  Ambient.magnetizationAlongExhaustion_continuous_field
    (IsingModel.latticeGraph d) Λ J β i n

/-- **ℤ^d along-ex: magnetization Differentiable in `h`**. -/
theorem magnetizationAlongExhaustion_latticeGraph_differentiable_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    Differentiable ℝ (fun h' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J, h', β⟩ : IsingParams ℝ) i n) :=
  Ambient.magnetizationAlongExhaustion_differentiable_field
    (IsingModel.latticeGraph d) Λ J β i n

/-- **ℤ^d along-ex: magnetization Continuous in `J`**. -/
theorem magnetizationAlongExhaustion_latticeGraph_continuous_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    Continuous (fun J' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J', h, β⟩ : IsingParams ℝ) i n) :=
  Ambient.magnetizationAlongExhaustion_continuous_J
    (IsingModel.latticeGraph d) Λ h β i n

/-- **ℤ^d along-ex: magnetization Differentiable in `J`**. -/
theorem magnetizationAlongExhaustion_latticeGraph_differentiable_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    Differentiable ℝ (fun J' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d)
        Λ (⟨J', h, β⟩ : IsingParams ℝ) i n) :=
  Ambient.magnetizationAlongExhaustion_differentiable_J
    (IsingModel.latticeGraph d) Λ h β i n

end Ambient
end IsingModel
