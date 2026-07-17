import IsingModel.Lattice
import IsingModel.AmbientLattice.Defs.Regularity.HasDerivBasic

/-!
# Concrete ℤ^d Λ-layer `partitionFunctionΛ`/`boltzmannWeightΛ` `hasDerivAt` wrappers

Narrow child module for the 6 ℤ^d Λ-layer
`hasDerivAt_partitionFunctionΛ_latticeGraph_{beta,J,field}` and
`hasDerivAt_boltzmannWeightΛ_latticeGraph_{beta,J,field}` wrappers
extracted from `Regularity.lean` in PR #2044. Each is a thin
pass-through to the corresponding ambient `hasDerivAt_partitionFunctionΛ_*`
or `hasDerivAt_boltzmannWeightΛ_*` lemma at `IsingModel.latticeGraph d`.
All wrappers are stated in existence form `∃ c : ℝ, HasDerivAt _ c _`.
The theorem names are unchanged from the former `Regularity`
declarations.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: `partitionFunctionΛ` HasDerivAt in β**. -/
theorem hasDerivAt_partitionFunctionΛ_latticeGraph_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β'⟩ : IsingParams ℝ)) c β :=
  ⟨_, Ambient.hasDerivAt_partitionFunctionΛ_beta
    (IsingModel.latticeGraph d) Λ J h β⟩

/-- **ℤ^d Λ: `partitionFunctionΛ` HasDerivAt in J**. -/
theorem hasDerivAt_partitionFunctionΛ_latticeGraph_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) :
    ∃ c : ℝ, HasDerivAt (fun J' =>
        Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J', h, β⟩ : IsingParams ℝ)) c J :=
  ⟨_, Ambient.hasDerivAt_partitionFunctionΛ_J
    (IsingModel.latticeGraph d) Λ J h β⟩

/-- **ℤ^d Λ: `partitionFunctionΛ` HasDerivAt in h**. -/
theorem hasDerivAt_partitionFunctionΛ_latticeGraph_field
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) :
    ∃ c : ℝ, HasDerivAt (fun h' =>
        Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h', β⟩ : IsingParams ℝ)) c h :=
  ⟨_, Ambient.hasDerivAt_partitionFunctionΛ_field
    (IsingModel.latticeGraph d) Λ J h β⟩

/-! ## Moved: boltzmannWeightΛ HasDerivAt wrappers

The three wrappers
`hasDerivAt_boltzmannWeightΛ_latticeGraph_beta`,
`hasDerivAt_boltzmannWeightΛ_latticeGraph_J`,
`hasDerivAt_boltzmannWeightΛ_latticeGraph_field` now live in
`RegularityPartitionBoltzmannBoltzmann.lean`. -/

end Ambient

end IsingModel
