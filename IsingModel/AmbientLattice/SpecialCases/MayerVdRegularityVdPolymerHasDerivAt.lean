import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaVdPolymer

/-!
# `vdPolymerFamilies_sum` `HasDerivAt` wrapper along an exhaustion

Narrow child module for the §18.5 along-exhaustion
`vdPolymerFamilies_sumAlongExhaustion_hasDerivAt` wrapper extracted
from `MayerVdRegularityVdPolymer.lean`. The wrapper is a thin
pass-through to `vdPolymerFamilies_sum_Λ_hasDerivAt`. The theorem
name is unchanged from the former `MayerVdRegularity` declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: `vdPolymerFamilies_sum` `HasDerivAt`**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_hasDerivAt
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, s ^ P.card)
      (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) *
          ((Q.card : ℝ) * t ^ (Q.card - 1))) t :=
  vdPolymerFamilies_sum_Λ_hasDerivAt G (Λ.volume n) t

end Ambient
end IsingModel
