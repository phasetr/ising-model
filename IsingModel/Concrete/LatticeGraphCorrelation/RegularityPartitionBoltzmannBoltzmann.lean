import IsingModel.Lattice
import IsingModel.AmbientLattice.Defs.Regularity.HasDerivBasic

/-!
# ℤ^d differentiability of the finite-volume Boltzmann weight in one parameter

Concrete `latticeGraph d` statements that, at a fixed configuration on a fixed finite volume,
the Boltzmann weight of the induced subgraph has a derivative in the inverse temperature, in
the coupling, and in the external field, at a prescribed value of the parameter in question
and with the others held fixed and unrestricted. Every statement is in existence form and
requires a `Fintype` instance on the edge set induced by the volume; that instance is its
entire requirement, since no `Prop`-typed hypothesis is carried here.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: ambient-induced Boltzmann weight HasDerivAt in β**
(per-configuration, lifted from `IsingModel.boltzmannWeight`). -/
theorem hasDerivAt_boltzmannWeightΛ_latticeGraph_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) (σ : Config (↑Λ : Type _)) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        IsingModel.boltzmannWeight
          (inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β'⟩ : IsingParams ℝ) σ) c β :=
  ⟨_, Ambient.hasDerivAt_boltzmannWeightΛ_beta
    (IsingModel.latticeGraph d) Λ J h β σ⟩

/-- **ℤ^d Λ: ambient-induced Boltzmann weight HasDerivAt in J**. -/
theorem hasDerivAt_boltzmannWeightΛ_latticeGraph_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) (σ : Config (↑Λ : Type _)) :
    ∃ c : ℝ, HasDerivAt (fun J' =>
        IsingModel.boltzmannWeight
          (inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J', h, β⟩ : IsingParams ℝ) σ) c J :=
  ⟨_, Ambient.hasDerivAt_boltzmannWeightΛ_J
    (IsingModel.latticeGraph d) Λ J h β σ⟩

/-- **ℤ^d Λ: ambient-induced Boltzmann weight HasDerivAt in h**. -/
theorem hasDerivAt_boltzmannWeightΛ_latticeGraph_field
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) (σ : Config (↑Λ : Type _)) :
    ∃ c : ℝ, HasDerivAt (fun h' =>
        IsingModel.boltzmannWeight
          (inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h', β⟩ : IsingParams ℝ) σ) c h :=
  ⟨_, Ambient.hasDerivAt_boltzmannWeightΛ_field
    (IsingModel.latticeGraph d) Λ J h β σ⟩
end Ambient

end IsingModel
