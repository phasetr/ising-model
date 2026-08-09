import IsingModel.Lattice
import IsingModel.AmbientLattice.Defs.Regularity.Defs

/-!
# ℤ^d regularity of the finite-volume susceptibility in field and coupling

Concrete `latticeGraph d` statements that the susceptibility at a fixed vertex of a fixed
finite volume is continuous, and differentiable over `ℝ`, as a function of the external field
on the whole line, and likewise as a function of the coupling, with the remaining parameters
held fixed and unrestricted. Each requires a `Fintype` instance on the edge set induced by
the volume, and that instance is its entire requirement: no `Prop`-typed hypothesis is
carried here.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: susceptibility Continuous in `h`**. -/
theorem susceptibilityΛ_latticeGraph_continuous_field
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) (i : ↑Λ) :
    Continuous (fun h' =>
      Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h', β⟩ : IsingParams ℝ) i) :=
  Ambient.susceptibilityΛ_continuous_field
    (IsingModel.latticeGraph d) Λ J β i

/-- **ℤ^d Λ: susceptibility Differentiable in `h`**. -/
theorem susceptibilityΛ_latticeGraph_differentiable_field
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) (i : ↑Λ) :
    Differentiable ℝ (fun h' =>
      Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h', β⟩ : IsingParams ℝ) i) :=
  Ambient.susceptibilityΛ_differentiable_field
    (IsingModel.latticeGraph d) Λ J β i

/-- **ℤ^d Λ: susceptibility Continuous in `J`**. -/
theorem susceptibilityΛ_latticeGraph_continuous_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h β : ℝ) (i : ↑Λ) :
    Continuous (fun J' =>
      Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i) :=
  Ambient.susceptibilityΛ_continuous_J
    (IsingModel.latticeGraph d) Λ h β i

/-- **ℤ^d Λ: susceptibility Differentiable in `J`**. -/
theorem susceptibilityΛ_latticeGraph_differentiable_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h β : ℝ) (i : ↑Λ) :
    Differentiable ℝ (fun J' =>
      Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i) :=
  Ambient.susceptibilityΛ_differentiable_J
    (IsingModel.latticeGraph d) Λ h β i

end Ambient
end IsingModel
