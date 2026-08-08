import IsingModel.Lattice
import IsingModel.AmbientLattice.Defs.Regularity.HasDerivBasic

/-!
# Concrete ℤ^d Λ-layer `partitionFunctionΛ` `hasDerivAt` wrappers

Instantiates the Λ-level parameter derivatives of the partition function at
`IsingModel.latticeGraph d`, in the `β`, `J` and field directions, stated in existence form
`∃ c : ℝ, HasDerivAt _ c _`.
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

end Ambient

end IsingModel
