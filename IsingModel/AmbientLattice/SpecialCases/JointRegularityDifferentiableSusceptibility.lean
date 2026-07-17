import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMagSuscep

/-!
# Joint `Differentiable` susceptibility along-ex wrapper

Narrow child module for the along-exhaustion susceptibility joint
`Differentiable` wrapper extracted from
`JointRegularityDifferentiable.lean`:

* `susceptibilityAlongExhaustion_differentiable_joint_gen`

The wrapper unfolds `susceptibilityAlongExhaustion` and dispatches
on `i ∈ Λ.volume n`, falling back to `differentiable_const`
off-volume and forwarding to `susceptibilityΛ_differentiable_joint`
on-volume. The theorem name is unchanged from the former
`JointRegularity` declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: susceptibility jointly Differentiable ℝ in `(β, J, h)`** (general G). -/
theorem susceptibilityAlongExhaustion_differentiable_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      susceptibilityAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ i n) := by
  unfold susceptibilityAlongExhaustion
  by_cases hi : i ∈ Λ.volume n
  · simp only [hi, dif_pos]
    exact susceptibilityΛ_differentiable_joint G (Λ.volume n) ⟨i, hi⟩
  · simp only [hi, dif_neg, not_false_iff]
    exact differentiable_const _

end Ambient
end IsingModel
