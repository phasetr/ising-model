import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDecayCapstonesAlpha

/-!
# A ferromagnetic exponential-decay bound at an arbitrary admissible rate

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Under `0 ≤ J` and `0 < β`, for any rate `α` with `α ≤ -Real.log (Real.tanh (β * J))` and any
sites `i` and `j` of the stage volume, the finite-volume correlation of `{i, j}` at the
parameter record `⟨J, 0, β⟩` is at most `2 ^ |E| * Real.exp (-α * d i j)`, where `|E|` is
the edge count of the stage subgraph and `d` its graph distance.
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
