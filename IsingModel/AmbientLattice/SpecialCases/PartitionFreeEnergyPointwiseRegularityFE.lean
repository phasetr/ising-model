import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityFENonJoint

/-!
# Ambient freeEnergyAlongExhaustion pointwise wrappers

Provides the joint pointwise regularity of the along-exhaustion free energy, obtained from
the Λ-level `freeEnergyΛ_{continuous,differentiable}_*` lemmas through the `.continuousAt` /
`.differentiableAt` projections. This is the layer the §17.5–§17.6 derivative arguments
quote.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-! ### Along-exhaustion free-energy pointwise wrappers -/

/-- **freeEnergyAlongExhaustion jointly ContinuousAt**. -/
theorem freeEnergyAlongExhaustion_continuousAt_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ n) p :=
  (freeEnergyΛ_continuous_joint G (Λ.volume n)).continuousAt

/-- **freeEnergyAlongExhaustion jointly DifferentiableAt**. -/
theorem freeEnergyAlongExhaustion_differentiableAt_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨q.2.1, q.2.2, q.1⟩ n) p :=
  (freeEnergyΛ_differentiable_joint G (Λ.volume n)).differentiableAt


end Ambient
end IsingModel
