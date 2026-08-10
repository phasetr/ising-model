import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularityDifferentiableBeta

/-!
# Differentiability of the stage susceptibility at a point of the inverse-temperature axis

Stage-`n` statement for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. It takes `DecidableEq V` and
the stagewise `Fintype` instance on that subgraph's edge set, and carries no Prop-valued
hypothesis.

At a site `i : V` and arbitrary `J` and `h`, the stage susceptibility as a function of the
inverse temperature is differentiable over `ℝ` at every point `β`. The statement is the
`.differentiableAt` projection of the corresponding differentiability on all of `ℝ`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: susceptibility DifferentiableAt β** (general G, general h). -/
theorem susceptibilityAlongExhaustion_differentiableAt_beta_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    DifferentiableAt ℝ
      (fun β' => susceptibilityAlongExhaustion G Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) i n) β :=
  (susceptibilityAlongExhaustion_differentiable_beta_gen G Λ J h i n).differentiableAt

end Ambient
end IsingModel
