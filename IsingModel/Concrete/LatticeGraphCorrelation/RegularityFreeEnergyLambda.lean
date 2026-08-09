import IsingModel.Lattice
import IsingModel.AmbientLattice.Defs.Regularity.HasDerivBasic

/-!
# ℤ^d differentiability of the finite-volume free energy in one parameter

Concrete `latticeGraph d` statements that the free energy of a fixed finite volume has a
derivative in the inverse temperature, in the coupling, and in the external field, at a
prescribed value of the parameter in question and with the others held fixed and
unrestricted. Every statement is in existence form and requires a `Fintype` instance on the
edge set induced by the volume; that instance is its entire requirement, since no
`Prop`-typed hypothesis is carried here.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: `freeEnergyΛ` HasDerivAt in β at general h**. -/
theorem hasDerivAt_freeEnergyΛ_latticeGraph_beta_general_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β'⟩ : IsingParams ℝ)) c β :=
  ⟨_, Ambient.hasDerivAt_freeEnergyΛ_beta_general_h
    (IsingModel.latticeGraph d) Λ J h β⟩

/-- **ℤ^d Λ: `freeEnergyΛ` HasDerivAt in J**. -/
theorem hasDerivAt_freeEnergyΛ_latticeGraph_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) :
    ∃ c : ℝ, HasDerivAt (fun J' =>
        Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J', h, β⟩ : IsingParams ℝ)) c J :=
  ⟨_, Ambient.hasDerivAt_freeEnergyΛ_J
    (IsingModel.latticeGraph d) Λ J h β⟩

/-- **ℤ^d Λ: `freeEnergyΛ` HasDerivAt in h**. -/
theorem hasDerivAt_freeEnergyΛ_latticeGraph_field
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) :
    ∃ c : ℝ, HasDerivAt (fun h' =>
        Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h', β⟩ : IsingParams ℝ)) c h :=
  ⟨_, Ambient.hasDerivAt_freeEnergyΛ_field
    (IsingModel.latticeGraph d) Λ J h β⟩

end Ambient

end IsingModel
