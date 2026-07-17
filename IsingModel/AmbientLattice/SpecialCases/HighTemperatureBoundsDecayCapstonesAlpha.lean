import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient alongExhaustion §18.7 alpha-rate distance-bound capstones at h = 0

Narrow child module for the three §18.7 alpha-rate
pair-correlation distance-bound capstones extracted from
`HighTemperatureBoundsDecayCapstonesDist.lean`:

* `..._le_two_pow_edges_mul_exp_alpha_dist`,
* `..._le_exp_alpha_dist_of_le_highTempExpRate`,
* `..._le_two_pow_edges_mul_exp_alpha_dist_ferro`.

The first two are thin pass-throughs to the corresponding
`correlationΛ_*` ambient lemmas. The third (ferro) calls the
first one (kept inside this child).
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex §18.7 monotone-rate capstone at stage `n`**: any
`α ≤ -log(tanh(β·J))` may replace the exact high-temperature rate in the
pair-correlation distance bound at `Λ.volume n`. -/
theorem
correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β α : ℝ) (hβJ : 0 ≤ β * J)
    (hα : α ≤ -Real.log (Real.tanh (β * J))) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.exp (-α * ((inducedGraph G (Λ.volume n)).dist i j : ℝ)) :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist
    G (Λ.volume n) J β α hβJ hα i j

/-- **Along-ex §18.7 named monotone-rate capstone at stage `n`**:
any `α ≤ highTempExpRate β J` gives the stage-`n` pair-correlation
distance bound with rate `α`. -/
theorem
correlationAlongExhaustion_high_temp_h_zero_at_pair_le_exp_alpha_dist_of_le_highTempExpRate
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β α : ℝ) (hβJ : 0 ≤ β * J)
    (hα : α ≤ highTempExpRate β J) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.exp (-α * ((inducedGraph G (Λ.volume n)).dist i j : ℝ)) :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist_of_le_highTempExpRate
    G (Λ.volume n) J β α hβJ hα i j

/-! ## Moved: 1 ferromagnetic §18.7 alpha-rate capstone

The ferromagnetic alpha-rate
`_..._exp_alpha_dist_ferro` capstone now lives in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDecayCapstonesAlphaFerro`,
which depends on this parent module. Downstream consumers reach
the ferro wrapper through the umbrella `SpecialCases.lean` (which
imports both children), or by importing the ferro child directly.
This parent module does **not** re-import the ferro child, to avoid
an import cycle.
-/

end Ambient

end IsingModel
