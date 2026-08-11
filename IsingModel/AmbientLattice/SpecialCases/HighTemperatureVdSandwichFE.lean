import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureVdSandwichFreeEnergy
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureVdSandwichFEFerro

/-!
# §18.5 cluster-expansion convergence sandwich wrappers along an exhaustion

Provides the GJ §18.5 two-sided bound on the vertex-disjoint polymer-family sum along an
exhaustion, in plain and sharpened form — the convergence input for the stagewise
cluster-expansion estimates. Each passes through to its
`vdPolymerFamilies_sum_Λ_sandwich*` ambient counterpart.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-exhaustion: VD polymer-family sum sandwich** (§18.5
along-ex wrap of `vdPolymerFamilies_sum_sandwich`). -/
theorem vdPolymerFamilies_sumAlongExhaustion_sandwich
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card :=
  vdPolymerFamilies_sum_Λ_sandwich G (Λ.volume n) hβJ

/-- **Along-exhaustion: VD polymer-family sum sharp sandwich** (§18.5
along-ex wrap of `vdPolymerFamilies_sum_sandwich_sharp`). -/
theorem vdPolymerFamilies_sumAlongExhaustion_sandwich_sharp
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^
        (inducedGraph G (Λ.volume n)).edgeFinset.card :=
  vdPolymerFamilies_sum_Λ_sandwich_sharp G (Λ.volume n) hβJ

end Ambient
end IsingModel
