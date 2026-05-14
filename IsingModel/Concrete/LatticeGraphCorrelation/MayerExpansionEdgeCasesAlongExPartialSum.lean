import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerExpansionEdgeCases

/-!
# Concrete along-ex mayerPartialSumAlongExhaustion wrappers

Narrow child module for 3 ℤ^d along-exhaustion
`mayerPartialSumAlongExhaustion_latticeGraph_*` wrappers extracted
from `MayerExpansionEdgeCasesAlongEx.lean`:

* `mayerPartialSumAlongExhaustion_latticeGraph_two`,
* `mayerPartialSumAlongExhaustion_latticeGraph_eq_zero_of_no_polymers`,
* `mayerPartialSumAlongExhaustion_latticeGraph_eq_zero_of_edgeFinset_empty`.

Each result is a thin pass-through of the corresponding ambient
`Ambient.mayerPartialSumAlongExhaustion_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `MayerExpansionEdgeCasesAlongEx` declarations.
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
