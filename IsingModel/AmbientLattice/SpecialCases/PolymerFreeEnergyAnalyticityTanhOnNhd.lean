import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaRegularity

/-!
# Real-analyticity of the polymer free energy at a `tanh` activity on the nonnegative ray

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

At the activity `Real.tanh (β * J)`, the polymer free energy of the stage subgraph is
real-analytic on a neighbourhood of each point of `Set.Ici 0`: as a function of the inverse
temperature with `0 ≤ J` as the only Prop-valued hypothesis, and as a function of the coupling
with `0 ≤ β` as the only Prop-valued hypothesis.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: polymerFreeEnergy ∘ tanh ∘ (·*J) `AnalyticOnNhd ℝ _
(Set.Ici 0)` in β under `0 ≤ J`** (§18.6 along-ex wrap). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_analyticOnNhd_beta_Ici_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) (n : ℕ) :
    AnalyticOnNhd ℝ (fun β' : ℝ =>
        IsingModel.polymerFreeEnergy
          (inducedGraph G (Λ.volume n)) (Real.tanh (β' * J)))
      (Set.Ici 0) :=
  polymerFreeEnergy_Λ_tanh_analyticOnNhd_beta_Ici_zero
    G (Λ.volume n) hJ

/-- **Along-ex: polymerFreeEnergy ∘ tanh ∘ (β*·) `AnalyticOnNhd ℝ _
(Set.Ici 0)` in J under `0 ≤ β`** (§18.6 along-ex wrap). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_analyticOnNhd_J_Ici_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) :
    AnalyticOnNhd ℝ (fun J' : ℝ =>
        IsingModel.polymerFreeEnergy
          (inducedGraph G (Λ.volume n)) (Real.tanh (β * J')))
      (Set.Ici 0) :=
  polymerFreeEnergy_Λ_tanh_analyticOnNhd_J_Ici_zero
    G (Λ.volume n) hβ

end Ambient
end IsingModel
