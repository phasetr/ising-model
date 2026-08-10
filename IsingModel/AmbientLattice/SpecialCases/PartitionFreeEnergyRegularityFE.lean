import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyRegularityFEDifferentiable
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyRegularityFEJoint

/-!
# Continuity of the stage free energy in each parameter direction

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set, and carries
no Prop-valued hypothesis.

The stage free energy is continuous on `ℝ` as a function of the inverse temperature with `J`
and `h` fixed, as a function of the external field with `J` and `β` fixed, and as a function
of the coupling with `h` and `β` fixed.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: freeEnergy Continuous in β** (general h). -/
theorem freeEnergyAlongExhaustion_continuous_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    Continuous (fun β' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h, β'⟩ n) :=
  freeEnergyΛ_continuous_beta G (Λ.volume n) J h

/-- **Along-ex: freeEnergy Continuous in h**. -/
theorem freeEnergyAlongExhaustion_continuous_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    Continuous (fun h' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h', β⟩ n) :=
  freeEnergyΛ_continuous_field G (Λ.volume n) J β

/-- **Along-ex: freeEnergy Continuous in J**. -/
theorem freeEnergyAlongExhaustion_continuous_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J', h, β⟩ n) :=
  freeEnergyΛ_continuous_J G (Λ.volume n) h β

end Ambient
end IsingModel
