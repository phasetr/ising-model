import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerBasicIdentitiesExpansionTermAtZero

/-!
# Ambient mayerExpansionTermAlongExhaustion small-`k` identity wrappers

Narrow child module for the two ambient
`mayerExpansionTermAlongExhaustion_*` small-`k` basic identity
wrappers extracted from `MayerBasicIdentities.lean`:

* `mayerExpansionTermAlongExhaustion_zero` (k=0)
* `mayerExpansionTermAlongExhaustion_one` (k=1)

The corresponding `_at_zero` (t=0) wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.MayerBasicIdentitiesExpansionTermAtZero`
and is re-imported through this parent module. Each wrapper is a
thin pass-through of the corresponding Λ-level
`mayerExpansionTerm_Λ_*` lemma. The theorem names are unchanged
from the former `MayerBasicIdentities` declarations.
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

/-! ## Moved: 1 at_zero (t=0) wrapper

The `mayerExpansionTermAlongExhaustion_at_zero` wrapper (t=0) now
lives in
`IsingModel.AmbientLattice.SpecialCases.MayerBasicIdentitiesExpansionTermAtZero`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel
