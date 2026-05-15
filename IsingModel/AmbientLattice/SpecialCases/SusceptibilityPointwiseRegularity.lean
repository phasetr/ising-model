import IsingModel.AmbientLattice.MagnetizationAlongExhaustion

/-!
# Ambient susceptibility pointwise regularity wrappers

This module contains general-graph `Continuous`, `Differentiable`,
`ContinuousAt`, and `DifferentiableAt` APIs for per-parameter
`susceptibilityAlongExhaustion` regularity. It is split out of the legacy
ambient special-cases module so concrete susceptibility pointwise wrappers can
depend on a narrower child path.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### Along-exhaustion susceptibility regularity wrappers -/

/-- **Along-ex: susceptibility Continuous in `β`** (general G, general h). -/
theorem susceptibilityAlongExhaustion_continuous_beta_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (i : V) (n : ℕ) :
    Continuous (fun β' =>
      susceptibilityAlongExhaustion G Λ
        (⟨J, h, β'⟩ : IsingParams ℝ) i n) := by
  unfold susceptibilityAlongExhaustion
  by_cases hi : i ∈ Λ.volume n
  · simp only [hi, dif_pos]
    exact susceptibilityΛ_continuous_beta G (Λ.volume n) J h _
  · simp only [hi, dif_neg, not_false_iff]
    exact continuous_const

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

/-- **Along-ex: susceptibility Continuous in `h`** (general G). -/
theorem susceptibilityAlongExhaustion_continuous_field_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) (n : ℕ) :
    Continuous (fun h' =>
      susceptibilityAlongExhaustion G Λ
        (⟨J, h', β⟩ : IsingParams ℝ) i n) := by
  unfold susceptibilityAlongExhaustion
  by_cases hi : i ∈ Λ.volume n
  · simp only [hi, dif_pos]
    exact susceptibilityΛ_continuous_field G (Λ.volume n) J β _
  · simp only [hi, dif_neg, not_false_iff]
    exact continuous_const

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

/-- **Along-ex: susceptibility Continuous in `J`** (general G). -/
theorem susceptibilityAlongExhaustion_continuous_J_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (i : V) (n : ℕ) :
    Continuous (fun J' =>
      susceptibilityAlongExhaustion G Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i n) := by
  unfold susceptibilityAlongExhaustion
  by_cases hi : i ∈ Λ.volume n
  · simp only [hi, dif_pos]
    exact susceptibilityΛ_continuous_J G (Λ.volume n) h β _
  · simp only [hi, dif_neg, not_false_iff]
    exact continuous_const

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

/-! ## Moved: ContinuousAt / DifferentiableAt along-ex susceptibility wrappers

The six `susceptibilityAlongExhaustion_{continuousAt,differentiableAt}_{beta,field,J}_gen`
pointwise wrappers now live in
`IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularityAt`.
The legacy import path is preserved by re-exporting the new child
from `Legacy.lean` and from each downstream consumer that previously
imported only this parent.
-/

end Ambient
end IsingModel
