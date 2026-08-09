import IsingModel.AmbientLattice.Exhaustion

/-!
# A single-edge lower bound on the zero-field pair correlation, along an exhaustion

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Under `0 ≤ β * J`, for distinct sites `i` and `j` of the stage volume joined by an edge of
the stage subgraph, the finite-volume correlation of `{i, j}` at the parameter record
`⟨J, 0, β⟩` is at least `Real.tanh (β * J) / 2 ^ |E|`, where `|E|` is the edge count of that
subgraph.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-exhaustion transport of the project-derived pair lower bound at stage `n`.**
Applies the Λ-level single-edge lower bound at the stage-`n`
subtype `↑(Λ.volume n)`. Along-exhaustion wrapper for
`correlationΛ_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ)
    (i j : ↑(Λ.volume n)) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph G (Λ.volume n)).edgeSet) :
    Real.tanh (β * J) /
        (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
      ≤ correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
          ({i, j} : Finset ↑(Λ.volume n)) :=
  correlationΛ_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    G (Λ.volume n) J β hβJ i j hij he

end Ambient
end IsingModel
