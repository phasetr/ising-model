import IsingModel.Lattice
import IsingModel.AmbientLattice.BetaDerivativePartitionSusc
import IsingModel.AmbientLattice.JDerivative
import IsingModel.AmbientLattice.FieldDerivative

/-!
# ℤ^d along-ex `freeEnergyAlongExhaustion` HasDerivAt wrappers

Narrow child module for three ℤ^d along-exhaustion
`freeEnergyAlongExhaustion_latticeGraph_hasDerivAt_*` wrappers:

* `freeEnergyAlongExhaustion_latticeGraph_hasDerivAt_beta_general_h`,
* `freeEnergyAlongExhaustion_latticeGraph_hasDerivAt_J`,
* `freeEnergyAlongExhaustion_latticeGraph_hasDerivAt_field`.

Each result is a thin pass-through of the ambient
`Ambient.freeEnergyAlongExhaustion_hasDerivAt_*` lemma at
`G := IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

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
