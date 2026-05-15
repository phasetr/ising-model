import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularity

/-!
# Susceptibility `ContinuousAt` / `DifferentiableAt` along-ex wrappers

Narrow child module for the six pointwise `ContinuousAt` /
`DifferentiableAt` susceptibility wrappers along an exhaustion,
obtained from the corresponding `_continuous_*_gen` /
`_differentiable_*_gen` wrappers in the parent
`SusceptibilityPointwiseRegularity` module via the `.continuousAt` /
`.differentiableAt` projections. Theorem names are unchanged from
the former `SusceptibilityPointwiseRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: susceptibility ContinuousAt β** (general G, general h). -/
theorem susceptibilityAlongExhaustion_continuousAt_beta_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    ContinuousAt
      (fun β' => susceptibilityAlongExhaustion G Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) i n) β :=
  (susceptibilityAlongExhaustion_continuous_beta_gen G Λ J h i n).continuousAt

/-- **Along-ex: susceptibility DifferentiableAt β** (general G, general h). -/
theorem susceptibilityAlongExhaustion_differentiableAt_beta_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    DifferentiableAt ℝ
      (fun β' => susceptibilityAlongExhaustion G Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) i n) β :=
  (susceptibilityAlongExhaustion_differentiable_beta_gen G Λ J h i n).differentiableAt

/-- **Along-ex: susceptibility ContinuousAt h** (general G). -/
theorem susceptibilityAlongExhaustion_continuousAt_field_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    ContinuousAt
      (fun h' => susceptibilityAlongExhaustion G Λ
          (⟨J, h', β⟩ : IsingParams ℝ) i n) h :=
  (susceptibilityAlongExhaustion_continuous_field_gen G Λ J β i n).continuousAt

/-- **Along-ex: susceptibility DifferentiableAt h** (general G). -/
theorem susceptibilityAlongExhaustion_differentiableAt_field_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    DifferentiableAt ℝ
      (fun h' => susceptibilityAlongExhaustion G Λ
          (⟨J, h', β⟩ : IsingParams ℝ) i n) h :=
  (susceptibilityAlongExhaustion_differentiable_field_gen G Λ J β i n).differentiableAt

/-- **Along-ex: susceptibility ContinuousAt J** (general G). -/
theorem susceptibilityAlongExhaustion_continuousAt_J_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    ContinuousAt
      (fun J' => susceptibilityAlongExhaustion G Λ
          (⟨J', h, β⟩ : IsingParams ℝ) i n) J :=
  (susceptibilityAlongExhaustion_continuous_J_gen G Λ h β i n).continuousAt

/-- **Along-ex: susceptibility DifferentiableAt J** (general G). -/
theorem susceptibilityAlongExhaustion_differentiableAt_J_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    DifferentiableAt ℝ
      (fun J' => susceptibilityAlongExhaustion G Λ
          (⟨J', h, β⟩ : IsingParams ℝ) i n) J :=
  (susceptibilityAlongExhaustion_differentiable_J_gen G Λ h β i n).differentiableAt

end Ambient
end IsingModel
