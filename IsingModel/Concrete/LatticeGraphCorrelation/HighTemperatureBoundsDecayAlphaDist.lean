import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

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

/-! ## Moved: along-ex `_le_two_pow_edges_mul_exp_alpha_dist` wrapper

`correlationAlongExhaustion_latticeGraph_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist`
now lives in `HighTemperatureBoundsDecayAlphaDistAlongEx.lean`. -/


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

/-! ## Moved: along-ex `_of_le_highTempExpRate` wrapper

`correlationAlongExhaustion_latticeGraph_h_zero_at_pair_le_exp_alpha_dist_of_le_highTempExpRate`
now lives in `HighTemperatureBoundsDecayAlphaDistAlongEx.lean`. -/


/-! ## Moved: along-ex `_ferro` wrapper

`correlationAlongExhaustion_latticeGraph_h_zero_at_pair_le_exp_alpha_dist_ferro`
now lives in `HighTemperatureBoundsDecayAlphaDistAlongEx.lean`. -/


end Ambient
end IsingModel
