import IsingModel.Lattice
import IsingModel.AmbientLattice.BetaDerivativePartitionSusc
import IsingModel.AmbientLattice.JDerivative
import IsingModel.AmbientLattice.FieldDerivative

/-!
# ℤ^d differentiability of the along-exhaustion free energy in one parameter

Concrete `latticeGraph d` statements that, at a fixed stage of an arbitrary
`Ambient.Exhaustion` of `Fin d → ℤ`, the free energy of that stage has a derivative in the
inverse temperature, in the coupling, and in the external field, at a prescribed value of the
parameter in question and with the others held fixed and unrestricted. Every statement is in
existence form and requires a `Fintype` instance on the edge set induced at every stage; that
instance is its entire requirement, since no `Prop`-typed hypothesis is carried here.
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
