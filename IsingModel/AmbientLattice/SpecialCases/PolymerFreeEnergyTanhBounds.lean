import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhBoundsFerro
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhBoundsHasDerivAt

/-!
# The polymer free energy as `log (1 + ε)`, and its linear `tanh` bound

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Write `ε(t)` for the sum of `∏ P ∈ Γ, t ^ P.card` over the vertex-disjoint compatible polymer
families `Γ` of the stage subgraph with the empty family erased from the index set, and `|E|`
for the edge count of that subgraph.

At the activity `Real.tanh (β * J)`, and with `0 ≤ β * J` as the only Prop-valued hypothesis,
the polymer free energy is at most `|E| * Real.tanh (β * J)`. Separately, and with no
Prop-valued hypothesis, the polymer free energy at an arbitrary activity `t : ℝ` equals
`Real.log (1 + ε(t))`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: polymerFreeEnergy tanh ≤ |E| · tanh** under
`0 ≤ β·J`. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_le_card_mul
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.tanh (β * J) :=
  polymerFreeEnergy_Λ_tanh_le_card_mul G (Λ.volume n) hβJ

/-- **Along-ex: polymerFreeEnergy = log(1 + ε(t))** decomposition. -/
theorem polymerFreeEnergyAlongExhaustion_eq_log_one_add_eps
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t =
      Real.log (1 + ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
              ∏ P ∈ Γ, t ^ P.card) :=
  polymerFreeEnergy_Λ_eq_log_one_add_eps G (Λ.volume n) t

end Ambient
end IsingModel
