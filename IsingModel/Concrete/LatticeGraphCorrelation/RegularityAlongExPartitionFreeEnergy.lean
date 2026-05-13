import IsingModel.Lattice
import IsingModel.AmbientLattice.BetaDerivative
import IsingModel.AmbientLattice.BetaDerivativePartitionSusc
import IsingModel.AmbientLattice.JDerivative
import IsingModel.AmbientLattice.FieldDerivative

/-!
# Concrete ℤ^d along-ex partitionFunction / freeEnergy hasDerivAt wrappers

Narrow child module for six ℤ^d along-exhaustion `hasDerivAt` wrappers for
`partitionFunctionAlongExhaustion` and `freeEnergyAlongExhaustion`. Each is a
thin pass-through to the corresponding ambient lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d along-ex `partitionFunctionAlongExhaustion` /
`freeEnergyAlongExhaustion` `hasDerivAt` wrappers -/

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` HasDerivAt in β**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_hasDerivAt_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) n) c β :=
  Ambient.partitionFunctionAlongExhaustion_hasDerivAt_beta
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` HasDerivAt in J**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_hasDerivAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun J' =>
        Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J', h, β⟩ : IsingParams ℝ) n) c J :=
  Ambient.partitionFunctionAlongExhaustion_hasDerivAt_J
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` HasDerivAt in h**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_hasDerivAt_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun h' =>
        Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h', β⟩ : IsingParams ℝ) n) c h :=
  Ambient.partitionFunctionAlongExhaustion_hasDerivAt_field
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` HasDerivAt in β at general h**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_hasDerivAt_beta_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) n) c β :=
  Ambient.freeEnergyAlongExhaustion_hasDerivAt_beta_general_h
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` HasDerivAt in J**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_hasDerivAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun J' =>
        Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J', h, β⟩ : IsingParams ℝ) n) c J :=
  Ambient.freeEnergyAlongExhaustion_hasDerivAt_J
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` HasDerivAt in h**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_hasDerivAt_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun h' =>
        Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h', β⟩ : IsingParams ℝ) n) c h :=
  Ambient.freeEnergyAlongExhaustion_hasDerivAt_field
    (IsingModel.latticeGraph d) Λ J h β n

end Ambient
end IsingModel
