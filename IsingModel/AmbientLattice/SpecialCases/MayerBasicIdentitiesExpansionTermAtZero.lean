import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaBasicIdentities

/-!
# Ambient `mayerExpansionTermAlongExhaustion_at_zero` wrapper

Narrow child module for the ambient
`mayerExpansionTermAlongExhaustion_at_zero` basic-identity wrapper
(t=0) extracted from `MayerBasicIdentitiesExpansionTerm.lean`. The
wrapper is a thin pass-through to the Λ-level
`mayerExpansionTerm_Λ_at_zero` lemma. The theorem name is
unchanged from the former `MayerBasicIdentities` declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

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
