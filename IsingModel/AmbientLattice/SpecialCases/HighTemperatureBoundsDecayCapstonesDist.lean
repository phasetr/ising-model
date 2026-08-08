import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharper
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviation
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBounds
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsTripleRatio
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFe
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDecayCapstonesAlpha
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDecayCapstonesDistNamedRate

/-!
# Ambient alongExhaustion §18.7 distance-bound capstone wrappers at h = 0

States the GJ §18.7 decay of the zero-field pair correlation in the graph distance between
the two sites, along an exhaustion. Each bound is a stagewise pass-through of the
corresponding `correlationΛ_*` ambient lemma.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex §18.7 capstone: high-temperature exponential decay of
the pair correlation in graph distance, at stage `n`**. Under
`0 ≤ β·J`, for `i, j : ↑(Λ.volume n)`,
`⟨σ_iσ_j⟩^{Λ_n}_{β,0} ≤ 2^{|E_{Λ_n}|} ·
    tanh(β·J)^{(inducedGraph G (Λ.volume n)).dist i j}`.
Stage-`n` Λ-level specialization of
`correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist`. -/
theorem
correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (i j : ↑(Λ.volume n)) :
    correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.tanh (β * J) ^ (inducedGraph G (Λ.volume n)).dist i j :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    G (Λ.volume n) J β hβJ i j

/-- **Along-ex §18.7 rate-form capstone at stage `n`**: under
`0 ≤ β·J`, the pair-correlation distance bound at `Λ.volume n` is
written with the explicit decay rate `-log(tanh(β·J))`. -/
theorem
correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (i j : ↑(Λ.volume n)) :
    correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.exp (-(-Real.log (Real.tanh (β * J))) *
          ((inducedGraph G (Λ.volume n)).dist i j : ℝ)) :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist
    G (Λ.volume n) J β hβJ i j

end Ambient

end IsingModel
