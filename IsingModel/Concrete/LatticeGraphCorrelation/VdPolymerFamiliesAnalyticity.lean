import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.VdPolymerFamiliesAnalyticity

/-!
# ℤ^d analyticity of the polymer-family activity sum

Concrete `latticeGraph d` statements that the sum, over the compatible polymer families of an
induced subgraph, of the product of the activity raised to each polymer's cardinality is
analytic in that activity at every real point; the same holds for the variant in which the
empty family is removed from the sum. Each is stated on the subgraph induced by a fixed
finite volume, requiring a `Fintype` instance on that induced edge set, and at a fixed stage
of an arbitrary `Ambient.Exhaustion` of `Fin d → ℤ`, requiring instead a `Fintype` instance
on the edge set induced at every stage. Those instances are the entire requirement, since no
`Prop`-typed hypothesis is carried anywhere in this module.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: vdPolymerFamilies_sum AnalyticAt ℝ in t**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_analyticAt
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, s ^ P.card) t :=
  Ambient.vdPolymerFamilies_sum_Λ_analyticAt
    (IsingModel.latticeGraph d) Λ t

/-- **ℤ^d along-ex: vdPolymerFamilies_sum AnalyticAt ℝ in t**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_latticeGraph_analyticAt
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, s ^ P.card) t :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_analyticAt
    (IsingModel.latticeGraph d) Λ n t

/-- **ℤ^d Λ: ε(t) is `AnalyticAt ℝ` at every `t`**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_analyticAt
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
        ∏ P ∈ Γ, s ^ P.card) t :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_analyticAt
    (IsingModel.latticeGraph d) Λ t

/-- **ℤ^d along-ex: ε(t) is `AnalyticAt ℝ` at every `t`**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_analyticAt
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (t : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun s : ℝ =>
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, s ^ P.card) t :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_analyticAt
    (IsingModel.latticeGraph d) Λ t n

end Ambient
end IsingModel
