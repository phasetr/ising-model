import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityHZero
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityFE
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityPartitionGeneralH
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityJoint

/-!
# Regularity of the stage partition function at a point of the external-field axis

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set, and carries
no Prop-valued hypothesis.

At arbitrary `J` and `β`, the stage partition function as a function of the external field is
continuous at every point `h` and differentiable over `ℝ` at every point `h`. Each statement
is the `.continuousAt` or `.differentiableAt` projection of the corresponding regularity on
all of `ℝ`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **partitionFunctionAlongExhaustion ContinuousAt h**. -/
theorem partitionFunctionAlongExhaustion_continuousAt_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun h' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h', β⟩ n) h :=
  (partitionFunctionΛ_continuous_h G (Λ.volume n) J β).continuousAt

/-- **partitionFunctionAlongExhaustion DifferentiableAt h**. -/
theorem partitionFunctionAlongExhaustion_differentiableAt_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun h' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, h', β⟩ n) h :=
  (partitionFunctionΛ_differentiable_h G (Λ.volume n) J β).differentiableAt

end Ambient
end IsingModel
