import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDecayCapstonesAlpha

/-!
# Ambient alongExhaustion §18.7 alpha-rate distance-bound ferromagnetic capstone

Narrow child module for the §18.7 ferromagnetic α-rate
pair-correlation distance-bound capstone extracted from
`HighTemperatureBoundsDecayCapstonesAlpha.lean`:

* `correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist_ferro`

The wrapper is a thin pass-through to its non-ferromagnetic sibling
in the parent under `mul_nonneg hβ.le hJ`. The theorem name is
unchanged from the former
`HighTemperatureBoundsDecayCapstonesDist` declaration.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex ferromagnetic §18.7 monotone-rate capstone at stage `n`**:
under `0 ≤ J, 0 < β`, any `α ≤ -log(tanh(β·J))` gives the stage-`n`
pair-correlation distance bound with rate `α`. -/
theorem
correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β α : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (hα : α ≤ -Real.log (Real.tanh (β * J))) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.exp (-α * ((inducedGraph G (Λ.volume n)).dist i j : ℝ)) :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist
    G Λ J β α (mul_nonneg hβ.le hJ) hα n i j

end Ambient

end IsingModel
