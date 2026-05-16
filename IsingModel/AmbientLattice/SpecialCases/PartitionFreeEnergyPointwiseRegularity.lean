import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityHZero
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityFE
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityPartitionGeneralH
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityJoint

/-!
# Ambient partition/free-energy pointwise regularity wrappers

This module contains general-graph `ContinuousAt` and `DifferentiableAt` APIs
for per-parameter and joint `partitionFunctionAlongExhaustion` /
`freeEnergyAlongExhaustion` regularity. It is split out of the original ambient
special-cases module so concrete partition/free-energy pointwise wrappers can
depend on a narrower child path.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### Along-exhaustion partition-function pointwise wrappers -/

/-! ## Moved: partitionFunctionAlongExhaustion h = 0 pointwise wrappers

The four `partitionFunctionAlongExhaustion_*_h_zero` ContinuousAt /
DifferentiableAt pointwise wrappers now live in
`PartitionFreeEnergyPointwiseRegularityHZero.lean`. They are re-imported
here so downstream consumers continue to see the symbols. -/



/-! ## Moved: partitionFunctionAlongExhaustion general-h pointwise wrappers

The four `partitionFunctionAlongExhaustion_*_general_h` ContinuousAt /
DifferentiableAt pointwise wrappers now live in
`PartitionFreeEnergyPointwiseRegularityPartitionGeneralH.lean`. They are
re-imported here so downstream consumers continue to see the symbols. -/



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

/-! ## Moved: 2 joint pointwise wrappers

The two `partitionFunctionAlongExhaustion_*_joint` joint pointwise
wrappers (`_continuousAt_joint`, `_differentiableAt_joint`) now live
in
`IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityJoint`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella.
-/

/-! ## Moved: freeEnergyAlongExhaustion pointwise wrappers

The eight `freeEnergyAlongExhaustion_{continuousAt,differentiableAt}_*`
pointwise wrappers (beta, field, J, joint) now live in
`PartitionFreeEnergyPointwiseRegularityFE.lean`. They are re-imported
here so downstream consumers continue to see the symbols. -/


end Ambient
end IsingModel
