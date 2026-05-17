import IsingModel.AmbientLattice.MagnetizationAlongExhaustion

/-!
# Susceptibility `Differentiable` in `β` along-ex wrapper

Narrow child module for the along-exhaustion
`susceptibilityAlongExhaustion_differentiable_beta_gen` wrapper
extracted from
`SusceptibilityPointwiseRegularityDifferentiable.lean`. The
wrapper is a thin pass-through to the corresponding
`susceptibilityΛ_differentiable_beta` ambient lemma via `unfold`
+ `by_cases`. The theorem name is unchanged from the former
`SusceptibilityPointwiseRegularity` declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: susceptibility Differentiable in `β`** (general G, general h). -/
theorem susceptibilityAlongExhaustion_differentiable_beta_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (i : V) (n : ℕ) :
    Differentiable ℝ (fun β' =>
      susceptibilityAlongExhaustion G Λ
        (⟨J, h, β'⟩ : IsingParams ℝ) i n) := by
  unfold susceptibilityAlongExhaustion
  by_cases hi : i ∈ Λ.volume n
  · simp only [hi, dif_pos]
    exact susceptibilityΛ_differentiable_beta G (Λ.volume n) J h _
  · simp only [hi, dif_neg, not_false_iff]
    exact differentiable_const _

end Ambient
end IsingModel
