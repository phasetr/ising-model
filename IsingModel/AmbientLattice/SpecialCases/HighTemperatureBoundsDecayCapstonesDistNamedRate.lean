import IsingModel.AmbientLattice.Exhaustion

/-!
# The zero-field exponential-decay bound at the named high-temperature rate

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Under `0 ≤ β * J`, for sites `i` and `j` of the stage volume, the finite-volume correlation
of `{i, j}` at the parameter record `⟨J, 0, β⟩` is at most
`2 ^ |E| * Real.exp (-(highTempExpRate β J) * d i j)`, where `highTempExpRate β J` is
`-Real.log (Real.tanh (β * J))`, `|E|` is the edge count of the stage subgraph and `d` its
graph distance.
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
