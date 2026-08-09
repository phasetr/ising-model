import IsingModel.Lattice
import IsingModel.AmbientLattice.Defs.Regularity.HasDerivCorr

/-!
# ℤ^d differentiability of the finite-volume correlation in one parameter

Concrete `latticeGraph d` statements that the correlation of a fixed finite set of vertices
of a fixed finite volume has a derivative in one parameter of the record at a prescribed
value, the others being held fixed. The inverse temperature is treated at zero external field
and again at an unrestricted one; the coupling and the external field are each treated at
unrestricted parameters. Every statement is in existence form, asserting that some real
number is the derivative rather than naming it, and requires a `Fintype` instance on the edge
set induced by the volume; that instance is its entire requirement, since no `Prop`-typed
hypothesis is carried anywhere in this module.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: `correlationΛ` HasDerivAt in β at h = 0**. -/
theorem hasDerivAt_correlationΛ_latticeGraph_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) (A : Finset (↑Λ : Type _)) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.correlationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) A) c β :=
  ⟨_, Ambient.hasDerivAt_correlationΛ_beta
    (IsingModel.latticeGraph d) Λ J β A⟩

/-- **ℤ^d Λ: `correlationΛ` HasDerivAt in β at general h**. -/
theorem hasDerivAt_correlationΛ_latticeGraph_beta_general_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) (A : Finset (↑Λ : Type _)) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.correlationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) A) c β :=
  ⟨_, Ambient.hasDerivAt_correlationΛ_beta_general_h
    (IsingModel.latticeGraph d) Λ J h β A⟩

/-- **ℤ^d Λ: `correlationΛ` HasDerivAt in J**. -/
theorem hasDerivAt_correlationΛ_latticeGraph_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) (A : Finset (↑Λ : Type _)) :
    ∃ c : ℝ, HasDerivAt (fun J' =>
        Ambient.correlationΛ (IsingModel.latticeGraph d) Λ
          (⟨J', h, β⟩ : IsingParams ℝ) A) c J :=
  ⟨_, Ambient.hasDerivAt_correlationΛ_J
    (IsingModel.latticeGraph d) Λ J h β A⟩

/-- **ℤ^d Λ: `correlationΛ` HasDerivAt in h**. -/
theorem hasDerivAt_correlationΛ_latticeGraph_field
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) (A : Finset (↑Λ : Type _)) :
    ∃ c : ℝ, HasDerivAt (fun h' =>
        Ambient.correlationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h', β⟩ : IsingParams ℝ) A) c h :=
  ⟨_, Ambient.hasDerivAt_correlationΛ_field
    (IsingModel.latticeGraph d) Λ J h β A⟩

end Ambient

end IsingModel
