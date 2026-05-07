import IsingModel.AmbientLattice.Defs
import IsingModel.AmbientLattice.Exhaustion

/-!
# Lightweight ambient-lattice correlation-decay wrappers

This module keeps the high-temperature correlation-decay along-exhaustion
API away from the heavier `SpecialCases` import chain. In particular,
`SpecialCases` imports analytic and cluster-expansion modules, while the
wrappers here only need finite-volume Lambda-level bounds and the
`Exhaustion` type.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex ferromagnetic §18.7 named-rate capstone at stage `n`**:
under `0 ≤ J, 0 < β`, the stage-`n` pair-correlation distance bound is
written with `highTempExpRate`. This lightweight wrapper avoids importing
the analytic cluster-expansion stack needed by `SpecialCases`. -/
theorem
correlationAlongExhaustion_high_temp_h_zero_at_pair_le_exp_highTempExpRate_dist_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.exp (-(highTempExpRate β J) *
          ((inducedGraph G (Λ.volume n)).dist i j : ℝ)) :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_highTempExpRate_dist_ferromagnetic
    G (Λ.volume n) J β hJ hβ i j

/-- **Along-ex ferromagnetic §18.7 named monotone-rate capstone at stage
`n`**: under `0 ≤ J, 0 < β`, any `α ≤ highTempExpRate β J` gives the
stage-`n` pair-correlation distance bound with rate `α`. This wrapper is
kept in the lightweight correlation-decay module. -/
theorem
correlationAlongExhaustion_high_temp_h_zero_at_pair_le_exp_alpha_dist_of_le_highTempExpRate_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β α : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (hα : α ≤ highTempExpRate β J) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.exp (-α * ((inducedGraph G (Λ.volume n)).dist i j : ℝ)) :=
  correlationΛ_high_temp_h_zero_at_pair_le_exp_alpha_dist_of_le_highTempExpRate_ferromagnetic
    G (Λ.volume n) J β α hJ hβ hα i j

end Ambient
end IsingModel
