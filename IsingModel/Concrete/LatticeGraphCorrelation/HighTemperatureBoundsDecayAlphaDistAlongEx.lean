import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDecayCapstonesAlpha

/-!
# ℤ^d along-exhaustion exponential decay at any admissible rate (§18.7)

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ` and at the parameter record `⟨J, 0, β⟩`, the decay bound
`2 ^ |E_n| * exp (-α * dist i j)` on the pair correlation, valid for every rate `α` that does
not exceed `-log (tanh (β * J))`; the same bound is also recorded with that ceiling written as
`highTempExpRate β J`. The rate condition is carried by every statement here; the sign
condition is `0 ≤ β * J`, replaced in the ferromagnetic form by `0 ≤ J` together with `0 < β`.
The distance is graph distance in the stage-`n` induced subgraph, and the conclusion is stated
for `correlationΛ` on `Λ.volume n` rather than for `correlationAlongExhaustion`.
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
