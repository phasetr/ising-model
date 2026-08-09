import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.Magnetization

/-!
# ℤ^d pointwise regularity of the along-exhaustion magnetization in field and coupling

Concrete `latticeGraph d` statements that, at a fixed site of `Fin d → ℤ` and a fixed stage
of an arbitrary `Ambient.Exhaustion`, the magnetization of that stage is continuous, and
differentiable over `ℝ`, at a prescribed value of the external field, and likewise at a
prescribed value of the coupling, with the remaining parameters held fixed and unrestricted.
Each requires a `Fintype` instance on the edge set induced at every stage, and that instance
is its entire requirement: no `Prop`-typed hypothesis is carried here.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: `magnetizationAlongExhaustion` ContinuousAt h**. -/
theorem magnetizationAlongExhaustion_latticeGraph_continuousAt_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    ContinuousAt (fun h' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h', β⟩ : IsingParams ℝ) i n) h :=
  Ambient.magnetizationAlongExhaustion_continuousAt_field
    (IsingModel.latticeGraph d) Λ J h β i n

/-- **ℤ^d along-ex: `magnetizationAlongExhaustion` DifferentiableAt h**. -/
theorem magnetizationAlongExhaustion_latticeGraph_differentiableAt_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    DifferentiableAt ℝ (fun h' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h', β⟩ : IsingParams ℝ) i n) h :=
  Ambient.magnetizationAlongExhaustion_differentiableAt_field
    (IsingModel.latticeGraph d) Λ J h β i n

/-- **ℤ^d along-ex: `magnetizationAlongExhaustion` ContinuousAt J**. -/
theorem magnetizationAlongExhaustion_latticeGraph_continuousAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    ContinuousAt (fun J' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i n) J :=
  Ambient.magnetizationAlongExhaustion_continuousAt_J
    (IsingModel.latticeGraph d) Λ J h β i n

/-- **ℤ^d along-ex: `magnetizationAlongExhaustion` DifferentiableAt J**. -/
theorem magnetizationAlongExhaustion_latticeGraph_differentiableAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    DifferentiableAt ℝ (fun J' =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i n) J :=
  Ambient.magnetizationAlongExhaustion_differentiableAt_J
    (IsingModel.latticeGraph d) Λ J h β i n

end Ambient
end IsingModel
