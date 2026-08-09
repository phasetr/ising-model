import IsingModel.Lattice
import IsingModel.AmbientLattice.Defs.Regularity.HasDerivCorr

/-!
# ℤ^d differentiability of the finite-volume magnetization in one parameter

Concrete `latticeGraph d` statements that the magnetization at a fixed vertex of a fixed
finite volume has a derivative in one parameter of the record at a prescribed value, the
others being held fixed. The external field and the coupling are treated at unrestricted
parameters, and the inverse temperature is treated at zero external field and again at an
unrestricted one. Every statement is in existence form and requires a `Fintype` instance on
the edge set induced by the volume; that instance is its entire requirement, since no
`Prop`-typed hypothesis is carried here.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: `magnetizationΛ` HasDerivAt in h**. -/
theorem magnetizationΛ_latticeGraph_hasDerivAt_field
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) (i : ↑Λ) :
    ∃ c : ℝ, HasDerivAt (fun h' =>
        Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h', β⟩ : IsingParams ℝ) i) c h :=
  ⟨_, Ambient.magnetizationΛ_hasDerivAt_field
    (IsingModel.latticeGraph d) Λ J h β i⟩

/-- **ℤ^d Λ: `magnetizationΛ` HasDerivAt in β at h = 0**. -/
theorem magnetizationΛ_latticeGraph_hasDerivAt_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) (i : ↑Λ) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) i) c β :=
  ⟨_, Ambient.magnetizationΛ_hasDerivAt_beta
    (IsingModel.latticeGraph d) Λ J β i⟩

/-- **ℤ^d Λ: `magnetizationΛ` HasDerivAt in β at general h**. -/
theorem magnetizationΛ_latticeGraph_hasDerivAt_beta_general_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) (i : ↑Λ) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) i) c β :=
  ⟨_, Ambient.magnetizationΛ_hasDerivAt_beta_general_h
    (IsingModel.latticeGraph d) Λ J h β i⟩

/-- **ℤ^d Λ: `magnetizationΛ` HasDerivAt in J**. -/
theorem magnetizationΛ_latticeGraph_hasDerivAt_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) (i : ↑Λ) :
    ∃ c : ℝ, HasDerivAt (fun J' =>
        Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ
          (⟨J', h, β⟩ : IsingParams ℝ) i) c J :=
  ⟨_, Ambient.magnetizationΛ_hasDerivAt_J
    (IsingModel.latticeGraph d) Λ J h β i⟩

end Ambient
end IsingModel
