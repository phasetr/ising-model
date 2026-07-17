import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMayer

/-!
# Mayer `mayerExpansionTerm` continuity wrapper along an exhaustion

Narrow child module for the along-exhaustion
`mayerExpansionTermAlongExhaustion_continuous` wrapper extracted
from `MayerVdRegularity.lean`. The wrapper is a thin pass-through
to `mayerExpansionTerm_Λ_continuous`. The theorem name is unchanged
from the former `MayerVdRegularity` declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: `mayerExpansionTerm` is `Continuous`**. -/
theorem mayerExpansionTermAlongExhaustion_continuous
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (n : ℕ) :
    Continuous (fun t : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k t) :=
  mayerExpansionTerm_Λ_continuous G (Λ.volume n) k

end Ambient
end IsingModel
