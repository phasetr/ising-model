import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerExpansionEdgeCasesTwo
import IsingModel.AmbientLattice.SpecialCases.MayerExpansionEdgeCasesAbsLe

/-!
# ℤ^d AlongExhaustion mayer-expansion edge-case wrappers

Instantiates the along-exhaustion evaluations and absolute bound for the second-order Mayer
expansion term at `IsingModel.latticeGraph d`, which is where the GJ §18.5
remainder estimate is anchored.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: mayerExpansionTerm at `n = 2`**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_two
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (t : ℝ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 2 t =
      ∑ pq ∈ (IsingModel.allPolymers
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))) ×ˢ
              (IsingModel.allPolymers
                (inducedGraph (IsingModel.latticeGraph d)
                  (Λ.volume n))),
        (if IsingModel.PolymersIncompatible pq.1 pq.2 then (-1/2 : ℝ)
          else 0) *
          (t ^ pq.1.card * t ^ pq.2.card) :=
  Ambient.mayerExpansionTermAlongExhaustion_two
    (IsingModel.latticeGraph d) Λ t n

/-- **ℤ^d along-ex: mayerExpansionTerm at `n = 2`, filter form**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_two_filter
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (t : ℝ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 2 t =
      (-1/2 : ℝ) *
        ∑ pq ∈ ((IsingModel.allPolymers
                  (inducedGraph (IsingModel.latticeGraph d)
                    (Λ.volume n))) ×ˢ
                (IsingModel.allPolymers
                  (inducedGraph (IsingModel.latticeGraph d)
                    (Λ.volume n)))).filter
            (fun pq => IsingModel.PolymersIncompatible pq.1 pq.2),
          (t ^ pq.1.card * t ^ pq.2.card) :=
  Ambient.mayerExpansionTermAlongExhaustion_two_filter
    (IsingModel.latticeGraph d) Λ t n

/-- **ℤ^d along-ex: mayerExpansionTerm absolute bound**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_abs_le
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (k : ℕ) (t : ℝ) (n : ℕ) :
    |IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) k t| ≤
      ∑ ω ∈ Fintype.piFinset
              (fun _ : Fin k => IsingModel.allPolymers
                (inducedGraph (IsingModel.latticeGraph d)
                  (Λ.volume n))),
        |IsingModel.ursellCoefficient ω| *
          |IsingModel.clusterSeqActivity t ω| :=
  Ambient.mayerExpansionTermAlongExhaustion_abs_le
    (IsingModel.latticeGraph d) Λ k t n

end Ambient
end IsingModel
