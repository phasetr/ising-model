import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaPfeSharpening

/-!
# Monotonicity of the polymer-family sum on the nonnegative activity ray

Stage-`n` statement for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. It takes `DecidableEq V` and
the stagewise `Fintype` instance on that subgraph's edge set, and carries no Prop-valued
hypothesis.

As a function of the activity, the sum of `∏ P ∈ Γ, t ^ P.card` over the vertex-disjoint
compatible polymer families `Γ` of the stage subgraph is monotone on `Set.Ici 0`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: vdSum is `MonotoneOn (Set.Ici 0)`**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_monotoneOn_Ici_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    MonotoneOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ici 0) :=
  vdPolymerFamilies_sum_Λ_monotoneOn_Ici_zero G (Λ.volume n)

end Ambient
end IsingModel
