import IsingModel.AmbientLattice.AnalyticityLambdaPolymer
import IsingModel.AmbientLattice.AnalyticityLambdaBasicIdentities
import IsingModel.AmbientLattice.Exhaustion

/-!
# Equivalences for the vertex-disjoint compatible polymer-family sum

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Write `Ξ(t)` for the sum of `∏ P ∈ Γ, t ^ P.card` over the stage subgraph's vertex-disjoint
compatible polymer families and `ε(t)` for the same sum with the empty family removed.

At every real `t`, `Ξ(t) = 1` is equivalent to `ε(t) = 0`; for an activity `t` with `0 ≤ t`,
`1 < Ξ(t)` is equivalent to `0 < ε(t)`. With the activity read as `Real.tanh (β * J)` under
`0 ≤ β * J`, `1 < Ξ` is equivalent to `0 < Real.tanh (β * J)` together with the stage
subgraph having a polymer, and `Ξ = 1` is equivalent to `Real.tanh (β * J) = 0` or that
subgraph having no polymer.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: vdSum = 1 ↔ ε = 0**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_eq_one_iff_eps_eq_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, t ^ P.card) = 1 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) = 0 :=
  vdPolymerFamilies_sum_Λ_eq_one_iff_eps_zero G (Λ.volume n) t

/-- **Along-ex: vdSum > 1 ↔ ε > 0 under `0 ≤ t`**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_gt_one_iff_eps_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card :=
  vdPolymerFamilies_sum_Λ_gt_one_iff_eps_pos G (Λ.volume n) ht

/-- **Along-ex: vdSum_tanh > 1 ↔ 0 < tanh ∧ allPolymers ≠ ∅**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_tanh_gt_one_iff
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers
          (inducedGraph G (Λ.volume n))).Nonempty :=
  vdPolymerFamilies_sum_Λ_tanh_gt_one_iff G (Λ.volume n) hβJ

/-- **Along-ex: vdSum_tanh = 1 ↔ tanh = 0 ∨ allPolymers = ∅**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_tanh_eq_one_iff
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 1 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers
          (inducedGraph G (Λ.volume n)) = ∅ :=
  vdPolymerFamilies_sum_Λ_tanh_eq_one_iff G (Λ.volume n) hβJ

end Ambient
end IsingModel
