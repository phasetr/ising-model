import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureCapstones

/-!
# ℤ^d AlongExhaustion high-temperature capstone wrappers

Instantiates the along-exhaustion §18.3–§18.5 capstones at `IsingModel.latticeGraph d`: the
polymer-family and even-subgraph closed forms of the zero-field partition function, and the
order-1 Mayer partial sum at unit activity, which evaluates to the polymer count.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: §18.4 partitionFunction polymer-family form**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_polymer_family
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J β : ℝ) (n : ℕ) :
    Ambient.partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ n =
      (2 : ℝ) ^
          Fintype.card ↑(Λ.volume n : Finset (Fin d → ℤ)) *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)).edgeFinset.card *
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d)
                  (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
  Ambient.partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_polymer_family
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d along-ex: §18.4 partitionFunction even-subgraph form**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_closed_evenSubgraphs
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J β : ℝ) (n : ℕ) :
    Ambient.partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ n =
      (2 : ℝ) ^
          Fintype.card ↑(Λ.volume n : Finset (Fin d → ℤ)) *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)).edgeFinset.card *
        ∑ X ∈ IsingModel.evenSubgraphs
                (inducedGraph (IsingModel.latticeGraph d)
                  (Λ.volume n)),
          Real.tanh (β * J) ^ X.card :=
  Ambient.partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed_evenSubgraphs
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d along-ex: mayerPartialSum at N=1, t=1**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_one_at_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 1 1 =
      (IsingModel.allPolymers
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n))).card :=
  Ambient.mayerPartialSumAlongExhaustion_one_at_one
    (IsingModel.latticeGraph d) Λ n

end Ambient
end IsingModel
