import IsingModel.Lattice
import IsingModel.AmbientLattice.Defs.Regularity.HasDerivBasic

/-!
# ℤ^d Λ-layer `boltzmannWeightΛ` HasDerivAt wrappers

Narrow child module for three Λ-layer
`hasDerivAt_boltzmannWeightΛ_latticeGraph_*` HasDerivAt wrappers
extracted from `RegularityPartitionBoltzmann.lean`:

* `hasDerivAt_boltzmannWeightΛ_latticeGraph_beta`,
* `hasDerivAt_boltzmannWeightΛ_latticeGraph_J`,
* `hasDerivAt_boltzmannWeightΛ_latticeGraph_field`.

Each result is a thin pass-through of the ambient
`Ambient.hasDerivAt_boltzmannWeightΛ_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `RegularityPartitionBoltzmann` declarations.
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
