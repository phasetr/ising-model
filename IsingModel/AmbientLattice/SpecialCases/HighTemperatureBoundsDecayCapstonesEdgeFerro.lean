import IsingModel.AmbientLattice.Exhaustion

/-!
# Ambient alongExhaustion §18.3 / §18.7 edge-pair ferromagnetic capstones

Narrow child module for the §18.3 / §18.7 ambient
alongExhaustion ferromagnetic edge-pair strict-positivity wrapper extracted from
`HighTemperatureBoundsDecayCapstonesEdge.lean`:

* `correlationAlongExhaustion_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic`

The wrapper is a thin pass-through to
`correlationΛ_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic`. The theorem name is
unchanged from the former
`AmbientLattice/SpecialCases/HighTemperatureBounds` declarations.
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
