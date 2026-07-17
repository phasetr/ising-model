import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDecayCapstonesDistNamedRate

/-!
# ℤ^d §18.7 highTempExpRate decay-capstone wrappers

Narrow child module for two ℤ^d
`*_latticeGraph_*_le_two_pow_edges_mul_exp_highTempExpRate_dist`
wrappers (Λ and AlongExhaustion variants) extracted from
`HighTemperatureBoundsDecayCapstones.lean`:

* `correlationΛ_latticeGraph_*_two_pow_edges_mul_exp_highTempExpRate_dist`
  (Λ variant),
* `correlationAlongExhaustion_latticeGraph_*_two_pow_edges_mul_exp_highTempExpRate_dist`
  (AlongExhaustion variant). Both at `_h_zero_at_pair_le_`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ §18.7 named-rate capstone**: the finite-volume
pair-correlation distance bound on `latticeGraph d` written with
`highTempExpRate`. -/
theorem
correlationΛ_latticeGraph_h_zero_at_pair_le_two_pow_edges_mul_exp_highTempExpRate_dist
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ)
      ≤ (2 : ℝ) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.exp (-(highTempExpRate β J) *
          ((inducedGraph (IsingModel.latticeGraph d) Λ).dist i j : ℝ)) :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_highTempExpRate_dist
    (IsingModel.latticeGraph d) Λ J β hβJ i j

/-- **ℤ^d along-ex §18.7 named-rate capstone at stage `n`**: the
finite-volume pair-correlation distance bound on `latticeGraph d` written
with `highTempExpRate`. -/
theorem
correlationAlongExhaustion_latticeGraph_h_zero_at_pair_le_two_pow_edges_mul_exp_highTempExpRate_dist
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ (IsingModel.latticeGraph d) (Λ.volume n)
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card *
        Real.exp (-(highTempExpRate β J) *
          ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).dist i j : ℝ)) :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_highTempExpRate_dist
    (IsingModel.latticeGraph d) Λ J β hβJ n i j

end Ambient
end IsingModel
