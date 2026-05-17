import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.AmbientLattice.SpecialCases.JointRegularityDifferentiableSusceptibility

/-!
# Joint `Differentiable` correlation / magnetization along-ex wrappers

Narrow child module for the two along-exhaustion joint
`Differentiable` wrappers in the correlation / magnetization
observables:

* `correlationAlongExhaustion_differentiable_joint_gen`
* `magnetizationAlongExhaustion_differentiable_joint`

The corresponding susceptibility wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.JointRegularityDifferentiableSusceptibility`
and is re-imported through this parent module. Each wrapper is a
thin pass-through to the corresponding `_differentiable_joint*`
ambient lemma via `unfold` + `by_cases`. Theorem names are
unchanged from the former `JointRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: correlation jointly Differentiable ℝ in `(β, J, h)`** (general G). -/
theorem correlationAlongExhaustion_differentiable_joint_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (A : Finset V) (n : ℕ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      correlationAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ A n) := by
  unfold correlationAlongExhaustion
  by_cases hA : A ⊆ Λ.volume n
  · simp only [hA, dif_pos]
    exact correlationΛ_differentiable_joint G (Λ.volume n) (liftFinset A hA)
  · simp only [hA, dif_neg, not_false_iff]
    exact differentiable_const _

/-- **Along-ex: magnetization jointly Differentiable ℝ in `(β, J, h)`** (general G). -/
theorem magnetizationAlongExhaustion_differentiable_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (i : V) (n : ℕ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      magnetizationAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ i n) := by
  unfold magnetizationAlongExhaustion correlationAlongExhaustion
  by_cases hi : ({i} : Finset V) ⊆ Λ.volume n
  · simp only [hi, dif_pos]
    exact correlationΛ_differentiable_joint G (Λ.volume n) (liftFinset {i} hi)
  · simp only [hi, dif_neg, not_false_iff]
    exact differentiable_const _

/-! ## Moved: 1 susceptibility joint Differentiable wrapper

The `susceptibilityAlongExhaustion_differentiable_joint_gen`
wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.JointRegularityDifferentiableSusceptibility`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel
