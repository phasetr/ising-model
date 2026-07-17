import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient alongExhaustion §18.7 named-rate distance-bound capstone

Narrow child module for the §18.7 alongExhaustion named-rate
pair-correlation distance-bound capstone wrapper
(`_..._exp_highTempExpRate_dist`) extracted from
`HighTemperatureBoundsDecayCapstonesDist.lean`.

The wrapper is a thin pass-through to the corresponding
`correlationΛ_*` ambient lemma, written with the named
`highTempExpRate` constant. The theorem name is unchanged from the
former `HighTemperatureBoundsDecayCapstones` declaration.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex §18.7 named-rate capstone at stage `n`**: the stage-`n`
pair-correlation distance bound written with `highTempExpRate`. -/
theorem
correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_highTempExpRate_dist
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.exp (-(highTempExpRate β J) *
          ((inducedGraph G (Λ.volume n)).dist i j : ℝ)) :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_highTempExpRate_dist
    G (Λ.volume n) J β hβJ i j

end Ambient

end IsingModel
