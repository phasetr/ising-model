import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaJoint

/-!
# Ambient freeEnergyAlongExhaustion `Continuous` joint wrapper

Narrow child module for the ambient
`freeEnergyAlongExhaustion_continuous_joint` regularity wrapper
extracted from `PartitionFreeEnergyRegularityFE.lean`. The wrapper
is a thin pass-through to the Λ-level
`freeEnergyΛ_continuous_joint` lemma. The theorem name is
unchanged from the former `PartitionFreeEnergyRegularity`
declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: freeEnergy jointly Continuous**. -/
theorem freeEnergyAlongExhaustion_continuous_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ n) :=
  freeEnergyΛ_continuous_joint G (Λ.volume n)

end Ambient
end IsingModel
