import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharper
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviation
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBounds
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsTripleRatio
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFe
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDecayCapstonesEdgeFerro

/-!
# Ambient alongExhaustion §18.3 / §18.7 edge-pair correlation capstones

Narrow child module for the two §18.3 / §18.7 ambient
alongExhaustion edge-pair correlation capstone wrappers extracted
from `HighTemperatureBoundsDecayCapstones.lean`:

* `correlationAlongExhaustion_high_temp_h_zero_at_pair_pos_of_edge`
* `correlationAlongExhaustion_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic`

Each wrapper is a thin pass-through to the corresponding
`correlationΛ_*` ambient lemma stating pair-correlation
strict positivity under an edge. Theorem names are unchanged from the
former
`AmbientLattice/SpecialCases/HighTemperatureBounds` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex pair correlation strict positivity under edge at stage `n` (GJ §18.3 / FV (3.46))**:
under `0 < β·J` and an edge in the stage-`n` induced subgraph,
`0 < ⟨σ_iσ_j⟩^{Λ_n}`. Stage-`n` Λ-level specialization of
`correlation_high_temp_h_zero_at_pair_pos_of_edge`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_pos_of_edge
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (n : ℕ)
    (i j : ↑(Λ.volume n)) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph G (Λ.volume n)).edgeSet) :
    0 < correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n)) :=
  correlationΛ_high_temp_h_zero_at_pair_pos_of_edge
    G (Λ.volume n) J β hβJ i j hij he

/-! ## Moved: ferromagnetic edge-pair capstone

The ferromagnetic capstone `_at_pair_pos_of_edge_ferromagnetic` now lives in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDecayCapstonesEdgeFerro`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient

end IsingModel
