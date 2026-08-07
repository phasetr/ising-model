import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityFENonJointDifferentiableAt
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityFENonJointBeta

/-!
# Ambient `freeEnergyAlongExhaustion` non-joint pointwise `ContinuousAt` wrappers

Gives per-parameter (rather than joint) pointwise continuity of the along-exhaustion free
energy, so a caller varying a single parameter does not have to carry the joint hypothesis.
Each passes through to a `freeEnergyΛ_continuous_*` ambient lemma via `.continuousAt`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### Along-exhaustion free-energy pointwise wrappers -/

/-- **freeEnergyAlongExhaustion ContinuousAt h**. -/
theorem freeEnergyAlongExhaustion_continuousAt_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun h' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h', β⟩ n) h :=
  (freeEnergyΛ_continuous_field G (Λ.volume n) J β).continuousAt

/-- **freeEnergyAlongExhaustion ContinuousAt J**. -/
theorem freeEnergyAlongExhaustion_continuousAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun J' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J', h, β⟩ n) J :=
  (freeEnergyΛ_continuous_J G (Λ.volume n) h β).continuousAt

end Ambient
end IsingModel
