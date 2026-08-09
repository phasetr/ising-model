import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureVdSandwichFE

/-!
# ℤ^d sandwich for the vertex-disjoint polymer-family activity sum (§18.5)

Instantiates at `IsingModel.latticeGraph d`, at activity `tanh (β * J)`, the sandwich of the
activity sum `∑_Γ ∏_{P ∈ Γ} tanh (β * J) ^ |P|` over all vertex-disjoint compatible polymer
families between `1` and `2 ^ |E|`, and its sharpening with the upper bound
`(1 + tanh (β * J)) ^ |E|`, on a fixed finite volume `Λ` and at a stage `n` of an
`Ambient.Exhaustion` of `Fin d → ℤ`. Every statement here carries `0 ≤ β * J` as its only sign
condition, and none carries a convergence hypothesis on the edge count.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: VD polymer-family sum sandwich** (§18.5 ℤ^d Λ wrap of
`vdPolymerFamilies_sum_sandwich`). -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_sandwich
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  Ambient.vdPolymerFamilies_sum_Λ_sandwich
    (IsingModel.latticeGraph d) Λ hβJ

/-- **ℤ^d Λ: VD polymer-family sum sharp sandwich** (§18.5 ℤ^d Λ
wrap of `vdPolymerFamilies_sum_sandwich_sharp`). -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_sandwich_sharp
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  Ambient.vdPolymerFamilies_sum_Λ_sandwich_sharp
    (IsingModel.latticeGraph d) Λ hβJ

/-- **ℤ^d along-exhaustion: VD polymer-family sum sandwich** (§18.5
ℤ^d along-ex wrap). -/
theorem vdPolymerFamilies_sumAlongExhaustion_latticeGraph_sandwich
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^ (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n)).edgeFinset.card :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_sandwich
    (IsingModel.latticeGraph d) Λ hβJ n

/-- **ℤ^d along-exhaustion: VD polymer-family sum sharp sandwich**
(§18.5 ℤ^d along-ex wrap). -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_sandwich_sharp
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_sandwich_sharp
    (IsingModel.latticeGraph d) Λ hβJ n

end Ambient
end IsingModel
