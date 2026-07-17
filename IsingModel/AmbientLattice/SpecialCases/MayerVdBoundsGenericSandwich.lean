import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaBasicIdentities

/-!
# Mayer vd generic-t sandwich bound wrappers along an exhaustion

Narrow child module for the two §18.5 along-exhaustion
`vdPolymerFamilies_sumAlongExhaustion` sandwich bound wrappers
extracted from `MayerVdBoundsGeneric.lean`:

* `vdPolymerFamilies_sumAlongExhaustion_ge_one_of_nonneg`
* `vdPolymerFamilies_sumAlongExhaustion_le_one_plus_pow_of_nonneg`

Each wrapper is a thin pass-through to the corresponding
`vdPolymerFamilies_sum_Λ_*` ambient lemma giving the `1 ≤ vdSum`
lower bound and `vdSum ≤ (1+t)^|E|` upper bound under `0 ≤ t`.
Theorem names are unchanged from the former `MayerVdBounds`
declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: 1 ≤ vdSum** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sumAlongExhaustion_ge_one_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    1 ≤ ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card :=
  vdPolymerFamilies_sum_Λ_ge_one_of_nonneg G (Λ.volume n) ht

/-- **Along-ex: vdSum ≤ (1+t)^|E|** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sumAlongExhaustion_le_one_plus_pow_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card)
      ≤ (1 + t) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card :=
  vdPolymerFamilies_sum_Λ_le_one_plus_pow_of_nonneg G (Λ.volume n) ht

end Ambient
end IsingModel
