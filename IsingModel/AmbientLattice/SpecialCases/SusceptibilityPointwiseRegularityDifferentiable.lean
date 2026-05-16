import IsingModel.AmbientLattice.MagnetizationAlongExhaustion

/-!
# Susceptibility `Differentiable` along-ex wrappers

Narrow child module for the three along-exhaustion susceptibility
`Differentiable` wrappers extracted from
`SusceptibilityPointwiseRegularity.lean`. Each wrapper is a thin
pass-through to the corresponding `susceptibilityΛ_differentiable_*`
ambient lemma via `unfold` + `by_cases`. Theorem names are
unchanged from the former `SusceptibilityPointwiseRegularity`
declarations.
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

/-- **Along-ex: susceptibility Differentiable in `h`** (general G). -/
theorem susceptibilityAlongExhaustion_differentiable_field_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) (n : ℕ) :
    Differentiable ℝ (fun h' =>
      susceptibilityAlongExhaustion G Λ
        (⟨J, h', β⟩ : IsingParams ℝ) i n) := by
  unfold susceptibilityAlongExhaustion
  by_cases hi : i ∈ Λ.volume n
  · simp only [hi, dif_pos]
    exact susceptibilityΛ_differentiable_field G (Λ.volume n) J β _
  · simp only [hi, dif_neg, not_false_iff]
    exact differentiable_const _

/-- **Along-ex: susceptibility Differentiable in `J`** (general G). -/
theorem susceptibilityAlongExhaustion_differentiable_J_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (i : V) (n : ℕ) :
    Differentiable ℝ (fun J' =>
      susceptibilityAlongExhaustion G Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i n) := by
  unfold susceptibilityAlongExhaustion
  by_cases hi : i ∈ Λ.volume n
  · simp only [hi, dif_pos]
    exact susceptibilityΛ_differentiable_J G (Λ.volume n) h β _
  · simp only [hi, dif_neg, not_false_iff]
    exact differentiable_const _

end Ambient
end IsingModel
