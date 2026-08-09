import IsingModel.AmbientLattice.Exhaustion

/-!
# Strict positivity of the zero-field pair correlation across an edge

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Under `0 < J` and `0 < β`, for distinct sites `i` and `j` of the stage volume joined by an
edge of the stage subgraph, the finite-volume correlation of `{i, j}` at the parameter
record `⟨J, 0, β⟩` is strictly positive.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex ferromagnetic pair strict positivity under edge at stage `n`**:
under `0 < J, 0 < β` and an edge in the stage-`n` induced subgraph,
`0 < ⟨σ_iσ_j⟩^{Λ_n}`. Stage-`n` Λ-level specialization of
`correlation_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β) (n : ℕ)
    (i j : ↑(Λ.volume n)) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph G (Λ.volume n)).edgeSet) :
    0 < correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n)) :=
  correlationΛ_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic
    G (Λ.volume n) J β hJ hβ i j hij he

end Ambient

end IsingModel
