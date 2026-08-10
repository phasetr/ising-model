import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaVdPolymer

/-!
# Real-analyticity of the log polymer-family sum at a `tanh` activity, along an exhaustion

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set, and has
`0 ≤ β * J` at the base point as its only Prop-valued hypothesis.

At the activity `Real.tanh (β * J)`, the logarithm of the sum over vertex-disjoint compatible
polymer families of the stage subgraph is real-analytic at `β` as a function of the inverse
temperature with `J` held fixed, and real-analytic at `J` as a function of the coupling with
`β` held fixed.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: log_vdPolymerFamilies_sum ∘ tanh AnalyticAt in β under
`0 ≤ β·J`**. -/
theorem log_vdPolymerFamilies_sumAlongExhaustion_tanh_analyticAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ =>
        Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card)) β :=
  log_vdPolymerFamilies_sum_Λ_tanh_analyticAt_beta
    G (Λ.volume n) J β hβJ

/-- **Along-ex: log_vdPolymerFamilies_sum ∘ tanh AnalyticAt in J under
`0 ≤ β·J`**. -/
theorem log_vdPolymerFamilies_sumAlongExhaustion_tanh_analyticAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β J : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ =>
        Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card)) J :=
  log_vdPolymerFamilies_sum_Λ_tanh_analyticAt_J
    G (Λ.volume n) β J hβJ

end Ambient
end IsingModel
