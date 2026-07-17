import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerBasicIdentitiesExpansionTerm

/-!
# ℤ^d mayerExpansionTermAlongExhaustion_latticeGraph wrappers

Narrow child module for three ℤ^d
`mayerExpansionTermAlongExhaustion_latticeGraph_*` wrappers extracted
from `MayerBasicIdentitiesAlongEx.lean`:

* `mayerExpansionTermAlongExhaustion_latticeGraph_zero`,
* `mayerExpansionTermAlongExhaustion_latticeGraph_one`,
* `mayerExpansionTermAlongExhaustion_latticeGraph_at_zero`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: mayerExpansionTerm at n = 0 = 0**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (t : ℝ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 0 t = 0 :=
  Ambient.mayerExpansionTermAlongExhaustion_zero
    (IsingModel.latticeGraph d) Λ t n

/-- **ℤ^d along-ex: mayerExpansionTerm at n = 1**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (t : ℝ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 1 t =
      ∑ P ∈ IsingModel.allPolymers
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        t ^ P.card :=
  Ambient.mayerExpansionTermAlongExhaustion_one
    (IsingModel.latticeGraph d) Λ t n

/-- **ℤ^d along-ex: mayerExpansionTerm at t = 0 = 0**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_at_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (k : ℕ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) k 0 = 0 :=
  Ambient.mayerExpansionTermAlongExhaustion_at_zero
    (IsingModel.latticeGraph d) Λ k n

end Ambient
end IsingModel
