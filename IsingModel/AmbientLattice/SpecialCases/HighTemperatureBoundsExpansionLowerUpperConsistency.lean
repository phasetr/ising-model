import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient alongExhaustion HT expansion bounds consistency wrappers at h = 0

Narrow child module for the two §18.3-§18.4 ambient alongExhaustion
`lower ≤ upper` bound consistency wrappers extracted from
`HighTemperatureBoundsExpansionLowerUpper.lean`:

* `partitionFunctionAlongExhaustion_high_temp_h_zero_lower_le_upper`
* `freeEnergyAlongExhaustion_high_temp_h_zero_lower_le_upper`

Each wrapper is a thin pass-through to the corresponding Λ-level
`partitionFunctionΛ_high_temp_h_zero_lower_le_upper` /
`freeEnergyΛ_high_temp_h_zero_lower_le_upper` lemma stating that
the high-temperature expansion's lower bound does not exceed the
upper bound. Theorem names are unchanged from the former
`HighTemperatureBoundsExpansion` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- **Along-exhaustion Z bounds consistency**: lower ≤ upper. -/
theorem partitionFunctionAlongExhaustion_high_temp_h_zero_lower_le_upper
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    (2 : ℝ) ^ (Λ.volume n).card *
        Real.cosh (β * J) ^
          (inducedGraph G (Λ.volume n)).edgeFinset.card
      ≤ (2 : ℝ) ^ ((Λ.volume n).card +
            (inducedGraph G (Λ.volume n)).edgeFinset.card) *
        Real.cosh (β * J) ^
            (inducedGraph G (Λ.volume n)).edgeFinset.card :=
  partitionFunctionΛ_high_temp_h_zero_lower_le_upper G (Λ.volume n) J β

omit [DecidableEq V] in
/-- **Along-exhaustion freeEnergy bounds consistency**: lower ≤ upper. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_lower_le_upper
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card * Real.log (Real.cosh (β * J))
      ≤ Real.log 2
        + ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
            (Λ.volume n).card * Real.log (2 * Real.cosh (β * J)) :=
  freeEnergyΛ_high_temp_h_zero_lower_le_upper G (Λ.volume n) J β hβJ

end Ambient

end IsingModel
