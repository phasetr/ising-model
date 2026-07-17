import IsingModel.Lattice
import IsingModel.AmbientLattice.Defs.Regularity.HasDerivBasic

/-!
# ℤ^d Λ-layer `freeEnergyΛ` HasDerivAt wrappers

Narrow child module for three ℤ^d Λ-layer `freeEnergyΛ_latticeGraph_*`
`HasDerivAt` wrappers extracted from `Regularity.lean`:

* `hasDerivAt_freeEnergyΛ_latticeGraph_beta_general_h`,
* `hasDerivAt_freeEnergyΛ_latticeGraph_J`,
* `hasDerivAt_freeEnergyΛ_latticeGraph_field`.

Each result is a thin pass-through of the ambient
`Ambient.hasDerivAt_freeEnergyΛ_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged from
the former `Regularity` declarations.
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
