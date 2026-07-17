import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaJoint

/-!
# Ambient freeEnergyAlongExhaustion `Differentiable` joint wrapper

Narrow child module for the ambient
`freeEnergyAlongExhaustion_differentiable_joint` regularity wrapper
extracted from `PartitionFreeEnergyRegularityFEDifferentiable.lean`.
The wrapper is a thin pass-through to the Λ-level
`freeEnergyΛ_differentiable_joint` lemma. The theorem name is
unchanged from the former `PartitionFreeEnergyRegularity`
declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: freeEnergy jointly Differentiable ℝ**. -/
theorem freeEnergyAlongExhaustion_differentiable_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ n) :=
  freeEnergyΛ_differentiable_joint G (Λ.volume n)

end Ambient
end IsingModel
