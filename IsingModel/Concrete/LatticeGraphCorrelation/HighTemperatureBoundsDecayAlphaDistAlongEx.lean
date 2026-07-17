import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDecayCapstonesAlpha

/-!
# Concrete along-ex §18.7 exp_alpha_dist decay capstone wrappers

Narrow child module for 3 ℤ^d along-exhaustion §18.7
`correlationAlongExhaustion_latticeGraph_h_zero_at_pair_le_*_exp_alpha_dist`
decay capstone wrappers extracted from
`HighTemperatureBoundsDecayAlphaDist.lean`:

* `correlationAlongExhaustion_latticeGraph_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist`,
* `correlationAlongExhaustion_latticeGraph_h_zero_at_pair_le_exp_alpha_dist_of_le_highTempExpRate`,
* `correlationAlongExhaustion_latticeGraph_h_zero_at_pair_le_exp_alpha_dist_ferro`.

Each result is a thin pass-through of the corresponding ambient
`correlationAlongExhaustion_high_temp_h_zero_at_pair_le_*_exp_alpha_dist`
lemma (or composes Λ-direct + AlongEx ferro) at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged from
the former `HighTemperatureBoundsDecayAlphaDist` declarations.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff


/-- **ℤ^d along-ex §18.7 monotone-rate capstone at stage `n`**: any
`α ≤ -log(tanh(β·J))` gives the finite-volume pair-correlation distance
bound on `latticeGraph d` with rate `α` at `Λ.volume n`. -/
theorem correlationAlongExhaustion_latticeGraph_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β α : ℝ) (hβJ : 0 ≤ β * J)
    (hα : α ≤ -Real.log (Real.tanh (β * J))) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ (IsingModel.latticeGraph d) (Λ.volume n)
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card *
        Real.exp (-α *
          ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).dist i j : ℝ)) :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist
    (IsingModel.latticeGraph d) Λ J β α hβJ hα n i j

/-- **ℤ^d along-ex §18.7 named monotone-rate capstone at stage `n`**:
any `α ≤ highTempExpRate β J` gives the finite-volume pair-correlation
distance bound on `latticeGraph d` with rate `α`. -/
theorem
correlationAlongExhaustion_latticeGraph_h_zero_at_pair_le_exp_alpha_dist_of_le_highTempExpRate
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β α : ℝ) (hβJ : 0 ≤ β * J)
    (hα : α ≤ highTempExpRate β J) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ (IsingModel.latticeGraph d) (Λ.volume n)
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card *
        Real.exp (-α *
          ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).dist i j : ℝ)) :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_le_exp_alpha_dist_of_le_highTempExpRate
    (IsingModel.latticeGraph d) Λ J β α hβJ hα n i j

/-- **ℤ^d along-ex ferromagnetic §18.7 monotone-rate capstone at stage
`n`**: under `0 ≤ J, 0 < β`, any `α ≤ -log(tanh(β·J))` gives the
stage-`n` pair-correlation distance bound on `latticeGraph d`. -/
theorem correlationAlongExhaustion_latticeGraph_h_zero_at_pair_le_exp_alpha_dist_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β α : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (hα : α ≤ -Real.log (Real.tanh (β * J))) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ (IsingModel.latticeGraph d) (Λ.volume n)
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card *
        Real.exp (-α *
          ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).dist i j : ℝ)) :=
  correlationAlongExhaustion_latticeGraph_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist
    d Λ J β α (mul_nonneg hβ.le hJ) hα n i j

end Ambient

end IsingModel
