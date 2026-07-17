import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaSandwich

/-!
# §18.5 cluster-expansion convergence ferromagnetic sandwich wrappers

Narrow child module for the two §18.5 ambient alongExhaustion
ferromagnetic `vdPolymerFamilies_sumAlongExhaustion_sandwich*_ferromagnetic`
cluster-expansion convergence sandwich wrappers extracted from
`HighTemperatureVdSandwichFE.lean`:

* `vdPolymerFamilies_sumAlongExhaustion_sandwich_ferromagnetic`
* `vdPolymerFamilies_sumAlongExhaustion_sandwich_sharp_ferromagnetic`

Each wrapper is a thin pass-through to the corresponding
`vdPolymerFamilies_sum_Λ_sandwich_*_ferromagnetic` ambient lemma.
Theorem names are unchanged from the former
`HighTemperatureVdSandwichFE` declarations.
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
