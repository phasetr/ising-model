import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMayerRecurrenceEpsilon

/-!
# The reduced polymer-family sum near zero activity, along an exhaustion

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Write `ε(t)` for the sum of `∏ P ∈ Γ, t ^ P.card` over the vertex-disjoint compatible
polymer families of the stage subgraph other than the empty family. For `t` in some
neighbourhood of `0`, `ε(t) < 1`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: ε(t) < 1 eventually as t → 0**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_minus_one_lt_one_eventually
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    ∀ᶠ t : ℝ in nhds 0,
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) < 1 :=
  vdPolymerFamilies_sum_Λ_minus_one_lt_one_eventually G (Λ.volume n)

end Ambient
end IsingModel
