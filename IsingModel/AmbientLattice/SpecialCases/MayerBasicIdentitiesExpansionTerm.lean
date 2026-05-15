import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient mayerExpansionTermAlongExhaustion basic identity wrappers

Narrow child module for 3 ambient `mayerExpansionTermAlongExhaustion_*`
basic identity wrappers extracted from `MayerBasicIdentities.lean`:

* `mayerExpansionTermAlongExhaustion_zero`,
* `mayerExpansionTermAlongExhaustion_one`,
* `mayerExpansionTermAlongExhaustion_at_zero`.

Each result is a thin pass-through of the corresponding Λ-level
`mayerExpansionTerm_Λ_*` lemma. The theorem names are unchanged from
the former `MayerBasicIdentities` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-- **Along-ex: mayerExpansionTerm at n = 0 = 0**. -/
theorem mayerExpansionTermAlongExhaustion_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph G (Λ.volume n)) 0 t = 0 :=
  mayerExpansionTerm_Λ_zero G (Λ.volume n) t

/-- **Along-ex: mayerExpansionTerm at n = 1 = ∑_P t^|P|**. -/
theorem mayerExpansionTermAlongExhaustion_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph G (Λ.volume n)) 1 t =
      ∑ P ∈ IsingModel.allPolymers
            (inducedGraph G (Λ.volume n)), t ^ P.card :=
  mayerExpansionTerm_Λ_one G (Λ.volume n) t

/-- **Along-ex: mayerExpansionTerm at t = 0 = 0**. -/
theorem mayerExpansionTermAlongExhaustion_at_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph G (Λ.volume n)) k 0 = 0 :=
  mayerExpansionTerm_Λ_at_zero G (Λ.volume n) k

end Ambient
end IsingModel
