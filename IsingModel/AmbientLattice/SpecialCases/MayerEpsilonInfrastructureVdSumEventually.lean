import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMayerRecurrenceEpsilon

/-!
# Mayer ε(t) `lt_one_eventually` wrapper along an exhaustion

Narrow child module for the §18.5 along-exhaustion
`vdPolymerFamilies_sumAlongExhaustion_minus_one_lt_one_eventually`
wrapper extracted from `MayerEpsilonInfrastructureVdSum.lean`. The
wrapper is a thin pass-through to the corresponding ambient
`vdPolymerFamilies_sum_Λ_minus_one_lt_one_eventually` lemma. The
theorem name is unchanged from the former
`MayerEpsilonInfrastructure` declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: ε(t) < 1 eventually as t → 0**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_minus_one_lt_one_eventually
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    ∀ᶠ t : ℝ in nhds 0,
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) < 1 :=
  vdPolymerFamilies_sum_Λ_minus_one_lt_one_eventually G (Λ.volume n)

end Ambient
end IsingModel
