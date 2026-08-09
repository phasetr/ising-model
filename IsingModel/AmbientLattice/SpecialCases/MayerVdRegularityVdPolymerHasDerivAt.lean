import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaVdPolymer

/-!
# The derivative of the polymer-family sum in the activity, along an exhaustion

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

At every real `t`, the map sending an activity `s` to the sum of `∏ P ∈ Γ, s ^ P.card` over
the stage subgraph's vertex-disjoint compatible polymer families has derivative
`∑ Γ, ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) * (Q.card * t ^ (Q.card - 1))` at `t`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: `vdPolymerFamilies_sum` `HasDerivAt`**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_hasDerivAt
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, s ^ P.card)
      (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) *
          ((Q.card : ℝ) * t ^ (Q.card - 1))) t :=
  vdPolymerFamilies_sum_Λ_hasDerivAt G (Λ.volume n) t

end Ambient
end IsingModel
