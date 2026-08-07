import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient alongExhaustion §18.7 alpha-rate distance-bound capstones at h = 0

Expresses the GJ §18.7 pair-correlation decay with the rate written as a free parameter `α`
rather than as the named high-temperature rate, which is the form the ℤ^d layer and the
monotone-rate comparisons need. Each bound passes through to the matching `correlationΛ_*`
ambient lemma.
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

end Ambient

end IsingModel
