import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharper
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviation
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBounds
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsTripleRatio
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFe
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDecayCapstonesDist

/-!
# Ambient alongExhaustion §18.7 high-temperature exponential-decay capstone wrappers

Narrow child module for 11 §18.7 alongExhaustion exponential-decay
capstone wrappers (pair correlation `tanh_pow_dist` / `exp_rate_dist`
/ `exp_highTempExpRate_dist` / `exp_alpha_dist` / `pos_of_edge` /
`ge_tanh_div_two_pow_edges`, with ferromagnetic variants). Theorem
names are unchanged from the former
`AmbientLattice/SpecialCases/HighTemperatureBounds` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-! ## Moved: distance-bound capstones

The six distance-bound capstones
(`_tanh_pow_dist`, `_exp_rate_dist`, `_exp_highTempExpRate_dist`,
`_exp_alpha_dist`, `_exp_alpha_dist_of_le_highTempExpRate`,
`_exp_alpha_dist_ferro`) now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDecayCapstonesDist`.
This parent re-imports the new child below so the remaining
ferromagnetic wrappers (`_tanh_pow_dist_ferromagnetic`,
`_exp_rate_dist_ferromagnetic`) continue to see them, and
downstream consumers see all symbols via the parent and
the umbrella `SpecialCases.lean`.
-/

/-- **Along-ex §18.7 ferromagnetic capstone**: under `0 ≤ J, 0 < β`,
the same exponential-decay bound at stage `n`. -/
theorem
correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (i j : ↑(Λ.volume n)) :
    correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.tanh (β * J) ^ (inducedGraph G (Λ.volume n)).dist i j :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    G Λ J β (mul_nonneg hβ.le hJ) n i j

/-- **Along-ex ferromagnetic §18.7 rate-form capstone at stage `n`**:
under `0 ≤ J, 0 < β`, the same explicit-rate pair-correlation bound
holds at `Λ.volume n`. -/
theorem
correlationAlongExhaustion_high_temp_h_zero_at_pair_le_exp_rate_dist_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (i j : ↑(Λ.volume n)) :
    correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.exp (-(-Real.log (Real.tanh (β * J))) *
          ((inducedGraph G (Λ.volume n)).dist i j : ℝ)) :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist
    G Λ J β (mul_nonneg hβ.le hJ) n i j

/-! ## Moved: 2 edge-pair correlation capstones

The two §18.3 / §18.7 edge-pair correlation capstone wrappers
(`correlationAlongExhaustion_high_temp_h_zero_at_pair_pos_of_edge`,
`correlationAlongExhaustion_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic`)
now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDecayCapstonesEdge`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient

end IsingModel
