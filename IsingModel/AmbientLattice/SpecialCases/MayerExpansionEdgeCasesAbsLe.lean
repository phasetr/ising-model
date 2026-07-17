import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMayerPfeEdgeBounds

/-!
# Mayer expansion `abs_le` along an exhaustion

Narrow child module for the along-exhaustion
`mayerExpansionTermAlongExhaustion_abs_le` wrapper extracted from
`MayerExpansionEdgeCases.lean`. The wrapper is a thin pass-through
to `mayerExpansionTerm_Λ_abs_le`. The theorem name is unchanged
from the former `MayerExpansionEdgeCases` declaration.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: mayerExpansionTerm absolute bound**. -/
theorem mayerExpansionTermAlongExhaustion_abs_le
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (t : ℝ) (n : ℕ) :
    |IsingModel.mayerExpansionTerm (inducedGraph G (Λ.volume n)) k t| ≤
      ∑ ω ∈ Fintype.piFinset
              (fun _ : Fin k => IsingModel.allPolymers
                (inducedGraph G (Λ.volume n))),
        |IsingModel.ursellCoefficient ω| *
          |IsingModel.clusterSeqActivity t ω| :=
  mayerExpansionTerm_Λ_abs_le G (Λ.volume n) k t

end Ambient
end IsingModel
