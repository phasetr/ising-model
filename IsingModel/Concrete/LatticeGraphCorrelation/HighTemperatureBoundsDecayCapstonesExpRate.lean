import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDecayCapstonesDist

/-!
# Concrete §18.7 exp_rate_dist decay-capstone wrappers

Narrow child module for 4 ℤ^d §18.7 exp_rate_dist decay-capstone
wrappers extracted from `HighTemperatureBoundsDecayCapstones.lean`:

* `correlationΛ_latticeGraph_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist`,
* `correlationΛ_latticeGraph_h_zero_at_pair_le_exp_rate_dist_ferro`,
* `correlationAlongExhaustion_latticeGraph_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist`,
* `correlationAlongExhaustion_latticeGraph_h_zero_at_pair_le_exp_rate_dist_ferro`.

Each result is a thin pass-through of the corresponding ambient
`correlation{Λ,AlongExhaustion}_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist`
lemma (or the tanh_pow_dist capstone composed with the explicit rate
`-log(tanh(β·J))`). The theorem names are unchanged from the former
`HighTemperatureBoundsDecayCapstones` declarations.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d Λ §18.7 rate-form capstone**: under `0 ≤ β·J`, the
finite-volume pair-correlation distance bound on `latticeGraph d` is
written with the explicit rate `-log(tanh(β·J))`. -/
theorem correlationΛ_latticeGraph_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ)
      ≤ (2 : ℝ) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.exp (-(-Real.log (Real.tanh (β * J))) *
          ((inducedGraph (IsingModel.latticeGraph d) Λ).dist i j : ℝ)) :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist
    (IsingModel.latticeGraph d) Λ J β hβJ i j

/-- **ℤ^d Λ ferromagnetic §18.7 rate-form capstone**: under
`0 ≤ J, 0 < β`, the same explicit-rate bound holds on `latticeGraph d`. -/
theorem correlationΛ_latticeGraph_h_zero_at_pair_le_exp_rate_dist_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ)
      ≤ (2 : ℝ) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.exp (-(-Real.log (Real.tanh (β * J))) *
          ((inducedGraph (IsingModel.latticeGraph d) Λ).dist i j : ℝ)) :=
  correlationΛ_latticeGraph_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist
    d Λ J β (mul_nonneg hβ.le hJ) i j

/-- **ℤ^d along-ex §18.7 rate-form capstone at stage `n`**: under
`0 ≤ β·J`, the finite-volume pair-correlation distance bound on
`latticeGraph d` is written with the explicit rate `-log(tanh(β·J))`. -/
theorem
correlationAlongExhaustion_latticeGraph_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ (IsingModel.latticeGraph d) (Λ.volume n)
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card *
        Real.exp (-(-Real.log (Real.tanh (β * J))) *
          ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).dist i j : ℝ)) :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist
    (IsingModel.latticeGraph d) Λ J β hβJ n i j

/-- **ℤ^d along-ex ferromagnetic §18.7 rate-form capstone at stage `n`**:
under `0 ≤ J, 0 < β`, the same explicit-rate bound holds on
`latticeGraph d`. -/
theorem correlationAlongExhaustion_latticeGraph_h_zero_at_pair_le_exp_rate_dist_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ (IsingModel.latticeGraph d) (Λ.volume n)
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card *
        Real.exp (-(-Real.log (Real.tanh (β * J))) *
          ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).dist i j : ℝ)) :=
  correlationAlongExhaustion_latticeGraph_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist
    d Λ J β (mul_nonneg hβ.le hJ) n i j

end Ambient

end IsingModel
