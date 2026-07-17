import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaBasicIdentities

/-!
# `vdPolymerFamilies_sumAlongExhaustion` at-zero / at-one identities

Narrow child module for the two §18.5 along-exhaustion
`vdPolymerFamilies_sumAlongExhaustion` evaluation identities at
`t = 0` and `t = 1` extracted from `MayerBasicIdentities.lean`:

* `vdPolymerFamilies_sumAlongExhaustion_at_zero`
* `vdPolymerFamilies_sumAlongExhaustion_at_one`

Each wrapper is a thin pass-through to the corresponding
`vdPolymerFamilies_sum_Λ_at_*` ambient lemma. Theorem names are
unchanged from the former `MayerBasicIdentities` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: vdPolymerFamilies_sum at t = 0 = 1**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_at_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 1 :=
  vdPolymerFamilies_sum_Λ_at_zero G (Λ.volume n)

/-- **Along-ex: vdPolymerFamilies_sum at t = 1 = #vdCompatPoly**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_at_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, (1 : ℝ) ^ P.card) =
      (IsingModel.vdCompatiblePolymerFamilies
        (inducedGraph G (Λ.volume n))).card :=
  vdPolymerFamilies_sum_Λ_at_one G (Λ.volume n)

end Ambient
end IsingModel
