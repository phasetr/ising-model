import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerExpansionEdgeCases

/-!
# ℤ^d Mayer partial sum at truncation order two and on polymer-free stages

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ`, the closed form of the Mayer partial sum at truncation order `2` — the polymer
activity sum `∑_P t ^ |P|` plus `-1/2` times the sum over the incompatible ordered pairs of
polymers — and its vanishing at every truncation order and activity when the stage-`n` induced
subgraph has no polymer, and when that subgraph has no edge. The order-`2` closed form assumes
nothing about the activity; the vanishing statements assume only the stated emptiness.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: mayerPartialSum at `N = 2`**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_two
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (t : ℝ) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 2 t =
      (∑ P ∈ IsingModel.allPolymers
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n)),
            t ^ P.card) +
        (-1/2 : ℝ) *
          ∑ pq ∈ ((IsingModel.allPolymers
                    (inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n))) ×ˢ
                  (IsingModel.allPolymers
                    (inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)))).filter
              (fun pq => IsingModel.PolymersIncompatible pq.1 pq.2),
            (t ^ pq.1.card * t ^ pq.2.card) :=
  Ambient.mayerPartialSumAlongExhaustion_two
    (IsingModel.latticeGraph d) Λ t n

/-- **ℤ^d along-ex: mayerPartialSum = 0 on no-polymer induced
graphs**. -/
theorem
mayerPartialSumAlongExhaustion_latticeGraph_eq_zero_of_no_polymers
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    (h_no : IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N t = 0 :=
  Ambient.mayerPartialSumAlongExhaustion_eq_zero_of_no_polymers
    (IsingModel.latticeGraph d) Λ n h_no t N

/-- **ℤ^d along-ex: mayerPartialSum = 0 on edgeless induced
graphs**. -/
theorem
mayerPartialSumAlongExhaustion_latticeGraph_eq_zero_of_edgeFinset_empty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    (h_empty : (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeFinset = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N t = 0 :=
  Ambient.mayerPartialSumAlongExhaustion_eq_zero_of_edgeFinset_empty
    (IsingModel.latticeGraph d) Λ n h_empty t N

end Ambient
end IsingModel
