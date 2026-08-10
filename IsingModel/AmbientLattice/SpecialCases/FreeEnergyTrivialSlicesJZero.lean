import IsingModel.AmbientLattice.Exhaustion

/-!
# The stage free energy at `J = 0`

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set; the
graph-independence statement takes in addition the stagewise `Fintype` instance for the
induced subgraph of the empty ambient graph.

At `J = 0`, and at every stage, the stage free energy of `G` agrees with the stage free energy
of the empty ambient graph; that statement carries no Prop-valued hypothesis. At a stage whose
volume is nonempty it equals `Real.log (2 * Real.cosh (β * h))`, for arbitrary `h` and `β`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-exhaustion J=0 graph-independence**:
`freeEnergyAlongExhaustion G Λ ⟨0, h, β⟩ n
  = freeEnergyAlongExhaustion ⊥ Λ ⟨0, h, β⟩ n`
for any `n`, any `G, Λ`, any `h, β` (no nonempty hypothesis).

Lift of `IsingModel.freeEnergy_eq_bot_at_J_zero` (PR #175) through
the definitional unfolding
`freeEnergyAlongExhaustion = freeEnergy (inducedGraph …)`:
apply the base identity on both sides to reduce to the same
`freeEnergy_bot` expression. -/
theorem freeEnergyAlongExhaustion_eq_bot_at_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph (⊥ : SimpleGraph V) (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion (⊥ : SimpleGraph V) Λ
          (⟨0, h, β⟩ : IsingParams ℝ) n := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨0, h, β⟩ : IsingParams ℝ)
    = IsingModel.freeEnergy (inducedGraph (⊥ : SimpleGraph V) (Λ.volume n))
          (⟨0, h, β⟩ : IsingParams ℝ)
  rw [IsingModel.freeEnergy_eq_bot_at_J_zero (inducedGraph G (Λ.volume n)),
      IsingModel.freeEnergy_eq_bot_at_J_zero
        (inducedGraph (⊥ : SimpleGraph V) (Λ.volume n))]

/-- **Along-exhaustion J=0 closed form (graph-independent)**:
for nonempty `Λ.volume n` and any ambient graph `G, Λ` and any `h, β`,
`freeEnergyAlongExhaustion G Λ ⟨0, h, β⟩ n = log (2·cosh(β·h))`.

Specialization of `IsingModel.freeEnergy_J_zero` via `change` +
definitional unfolding. -/
theorem freeEnergyAlongExhaustion_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) n
      = Real.log (2 * Real.cosh (β * h)) := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨0, h, β⟩ : IsingParams ℝ) = _
  exact IsingModel.freeEnergy_J_zero _ h β (Finset.Nonempty.fintype_card_coe_pos hne)

end Ambient
end IsingModel
