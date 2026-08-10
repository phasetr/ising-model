import IsingModel.AmbientLattice.Exhaustion

/-!
# Differentiability of the stage free energy at a point of the inverse-temperature axis

Stage-`n` statement for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. It takes `DecidableEq V` and
the stagewise `Fintype` instance on that subgraph's edge set, and carries no Prop-valued
hypothesis.

At arbitrary `J` and `h`, the stage free energy as a function of the inverse temperature is
differentiable over `ℝ` at every point `β`. The statement is the `.differentiableAt`
projection of the corresponding differentiability on all of `ℝ`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **freeEnergyAlongExhaustion DifferentiableAt β** (general h). -/
theorem freeEnergyAlongExhaustion_differentiableAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun β' : ℝ =>
      freeEnergyAlongExhaustion G Λ ⟨J, h, β'⟩ n) β :=
  (freeEnergyΛ_differentiable_beta G (Λ.volume n) J h).differentiableAt

end Ambient
end IsingModel
