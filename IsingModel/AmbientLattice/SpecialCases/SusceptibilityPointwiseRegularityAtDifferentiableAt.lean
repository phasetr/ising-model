import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularityDifferentiable

/-!
# Susceptibility `DifferentiableAt` along-ex wrappers

Turns the parametrized differentiability of the along-exhaustion susceptibility into
pointwise `DifferentiableAt` form via the `.differentiableAt` projection, which is what the
GJ §17.6 derivative computations consume.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: susceptibility DifferentiableAt h** (general G). -/
theorem susceptibilityAlongExhaustion_differentiableAt_field_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    DifferentiableAt ℝ
      (fun h' => susceptibilityAlongExhaustion G Λ
          (⟨J, h', β⟩ : IsingParams ℝ) i n) h :=
  (susceptibilityAlongExhaustion_differentiable_field_gen G Λ J β i n).differentiableAt

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
