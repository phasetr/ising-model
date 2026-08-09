import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaSandwich

/-!
# Two-sided bounds on the polymer-family sum at activity `Real.tanh (β * J)`

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Each statement assumes `0 ≤ J` and `0 < β`. Write `Ξ` for the sum of
`∏ P ∈ Γ, Real.tanh (β * J) ^ P.card` over the stage subgraph's vertex-disjoint compatible
polymer families and `|E|` for that subgraph's edge count.

`Ξ` lies between `1` and `2 ^ |E|`, and also between `1` and
`(1 + Real.tanh (β * J)) ^ |E|`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-exhaustion: VD polymer-family sum sandwich
(ferromagnetic)** (§18.5 ferromagnetic along-ex wrap). -/
theorem vdPolymerFamilies_sumAlongExhaustion_sandwich_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card :=
  vdPolymerFamilies_sum_Λ_sandwich_ferromagnetic G (Λ.volume n) hJ hβ

/-- **Along-exhaustion: VD polymer-family sum sharp sandwich
(ferromagnetic)** (§18.5 ferromagnetic along-ex wrap). -/
theorem
vdPolymerFamilies_sumAlongExhaustion_sandwich_sharp_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^
        (inducedGraph G (Λ.volume n)).edgeFinset.card :=
  vdPolymerFamilies_sum_Λ_sandwich_sharp_ferromagnetic
    G (Λ.volume n) hJ hβ

end Ambient
end IsingModel
