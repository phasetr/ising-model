import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaCapstones

/-!
# ℤ^d partition function through polymer families and even subgraphs (§18.4)

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ` and at the parameter
record `⟨J, 0, β⟩`, the identification of the partition function with
`2 ^ |Λ| * cosh (β * J) ^ |E_Λ|` times the activity sum over `vdCompatiblePolymerFamilies`,
and with that same prefactor times the sum of `tanh (β * J) ^ |X|` over `evenSubgraphs`;
together with the evaluation of `mayerPartialSum` at order `1` and activity `1` as the number
of polymers of the induced subgraph. No sign condition on `J` or `β` is imposed here.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d Λ: §18.4 partitionFunction polymer-family form**. -/
theorem
partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_polymer_family
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) :
    Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J, 0, β⟩ =
      (2 : ℝ) ^ Fintype.card ↑(Λ : Finset (Fin d → ℤ)) *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
  Ambient.partitionFunctionΛ_high_temp_expansion_h_zero_polymer_family
    (IsingModel.latticeGraph d) Λ J β

/-- **ℤ^d Λ: §18.4 partitionFunction even-subgraph form**. -/
theorem
partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_closed_evenSubgraphs
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) :
    Ambient.partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        ⟨J, 0, β⟩ =
      (2 : ℝ) ^ Fintype.card ↑(Λ : Finset (Fin d → ℤ)) *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        ∑ X ∈ IsingModel.evenSubgraphs
                (inducedGraph (IsingModel.latticeGraph d) Λ),
          Real.tanh (β * J) ^ X.card :=
  Ambient.partitionFunctionΛ_high_temp_expansion_h_zero_closed_evenSubgraphs
    (IsingModel.latticeGraph d) Λ J β

/-- **ℤ^d Λ: mayerPartialSum at N=1, t=1**. -/
theorem mayerPartialSum_Λ_latticeGraph_one_at_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) 1 1 =
      (IsingModel.allPolymers
        (inducedGraph (IsingModel.latticeGraph d) Λ)).card :=
  Ambient.mayerPartialSum_Λ_one_at_one (IsingModel.latticeGraph d) Λ

end Ambient
end IsingModel
