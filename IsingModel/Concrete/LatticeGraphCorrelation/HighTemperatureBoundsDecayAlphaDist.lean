import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBounds

/-!
# Concrete §18.7 high-temperature exp_alpha_dist capstone wrappers

Narrow child module for six ℤ^d
`correlation*_latticeGraph_*_exp_alpha_dist*` decay-rate capstone
wrappers (Λ + AlongExhaustion, including general/ferromagnetic and the
`of_le_highTempExpRate` family). Each wrapper is a thin pass-through to
the corresponding ambient §18.7 capstone lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ §18.7 monotone-rate capstone**: any
`α ≤ -log(tanh(β·J))` gives the finite-volume pair-correlation distance
bound on `latticeGraph d` with rate `α`. -/
theorem correlationΛ_latticeGraph_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β α : ℝ)
    (hβJ : 0 ≤ β * J) (hα : α ≤ -Real.log (Real.tanh (β * J)))
    (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ)
      ≤ (2 : ℝ) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.exp (-α * ((inducedGraph (IsingModel.latticeGraph d) Λ).dist i j : ℝ)) :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist
    (IsingModel.latticeGraph d) Λ J β α hβJ hα i j

/-- **ℤ^d Λ ferromagnetic §18.7 monotone-rate capstone**: under
`0 ≤ J, 0 < β`, any `α ≤ -log(tanh(β·J))` gives the finite-volume
pair-correlation distance bound on `latticeGraph d` with rate `α`. -/
theorem correlationΛ_latticeGraph_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β α : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β)
    (hα : α ≤ -Real.log (Real.tanh (β * J))) (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ)
      ≤ (2 : ℝ) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.exp (-α * ((inducedGraph (IsingModel.latticeGraph d) Λ).dist i j : ℝ)) :=
  correlationΛ_latticeGraph_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist
    d Λ J β α (mul_nonneg hβ.le hJ) hα i j

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

/-- **ℤ^d Λ §18.7 named monotone-rate capstone**: any
`α ≤ highTempExpRate β J` gives the finite-volume pair-correlation
distance bound on `latticeGraph d` with rate `α`. -/
theorem correlationΛ_latticeGraph_h_zero_at_pair_le_exp_alpha_dist_of_le_highTempExpRate
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β α : ℝ)
    (hβJ : 0 ≤ β * J) (hα : α ≤ highTempExpRate β J)
    (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ)
      ≤ (2 : ℝ) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.exp (-α * ((inducedGraph (IsingModel.latticeGraph d) Λ).dist i j : ℝ)) :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist_of_le_highTempExpRate
    (IsingModel.latticeGraph d) Λ J β α hβJ hα i j

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
