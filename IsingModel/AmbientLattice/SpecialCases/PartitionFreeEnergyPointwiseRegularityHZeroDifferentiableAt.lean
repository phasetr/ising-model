import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaSection186

/-!
# Differentiability of the stage partition function at a point, at zero external field

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set, and carries
no Prop-valued hypothesis.

Along the zero-field slice `⟨·, 0, ·⟩`, the stage partition function as a function of the
inverse temperature is differentiable over `ℝ` at every point `β`, with `J` fixed, and as a
function of the coupling it is differentiable over `ℝ` at every point `J`, with `β` fixed.
Each statement is the `.differentiableAt` projection of the corresponding differentiability on
all of `ℝ`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **partitionFunctionAlongExhaustion DifferentiableAt β at h = 0**. -/
theorem partitionFunctionAlongExhaustion_differentiableAt_beta_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun β' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J, 0, β'⟩ n) β :=
  (partitionFunctionΛ_differentiable_beta_h_zero G (Λ.volume n) J).differentiableAt

/-- **partitionFunctionAlongExhaustion DifferentiableAt J at h = 0**. -/
theorem partitionFunctionAlongExhaustion_differentiableAt_J_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun J' : ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨J', 0, β⟩ n) J :=
  (partitionFunctionΛ_differentiable_J_h_zero G (Λ.volume n) β).differentiableAt

end Ambient
end IsingModel
