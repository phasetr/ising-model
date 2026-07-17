import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDecayCapstonesDist

/-!
# Concrete §18.7 high-temperature exponential decay capstone wrappers

Narrow child module for the §18.7 high-temperature pair-correlation
exponential-decay capstone wrappers on `latticeGraph d` at `h = 0`.
16 theorems total, drawn from five capstone families --
`tanh_pow_dist`, `exp_rate_dist`, `exp_highTempExpRate_dist`,
`exp_alpha_dist`, and `exp_alpha_dist_of_le_highTempExpRate` -- in their
`correlationΛ_latticeGraph` / `correlationAlongExhaustion_latticeGraph`
versions and the ferromagnetic variants that previously lived alongside
them in `HighTemperatureBounds.lean`. (Some named-rate / monotone-rate
ferromagnetic variants of `exp_highTempExpRate_dist` continue to live in
`Concrete/LatticeGraphCorrelation/CorrelationDecay.lean` and are
intentionally not moved.) The theorem names are unchanged from the
former `HighTemperatureBounds` declarations.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d Λ §18.7 capstone: high-temperature exponential decay of the
pair correlation in graph distance**. Under `0 ≤ β·J` for `i, j : ↑Λ`,
`⟨σ_iσ_j⟩^Λ_{β,0} ≤ 2^{|E_Λ|} ·
    tanh(β·J)^{(inducedGraph (latticeGraph d) Λ).dist i j}`.
ℤ^d wrapper of
`correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist`. -/
theorem
correlationΛ_latticeGraph_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ)
      ≤ (2 : ℝ) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.tanh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).dist i j :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    (IsingModel.latticeGraph d) Λ J β hβJ i j

/-- **ℤ^d Λ §18.7 ferromagnetic capstone**: under `0 ≤ J, 0 < β`,
the same exponential-decay bound on `latticeGraph d` for `i, j : ↑Λ`. -/
theorem
correlationΛ_latticeGraph_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ)
      ≤ (2 : ℝ) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.tanh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).dist i j :=
  correlationΛ_latticeGraph_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    d Λ J β (mul_nonneg hβ.le hJ) i j

/-- **ℤ^d along-ex §18.7 capstone: high-temperature exponential decay
of the pair correlation in graph distance, at stage `n`**. Under
`0 ≤ β·J` for `i, j : ↑(Λ.volume n)`,
`⟨σ_iσ_j⟩^{Λ_n}_{β,0} ≤ 2^{|E_{Λ_n}|} ·
    tanh(β·J)^{(inducedGraph (latticeGraph d) (Λ.volume n)).dist i j}`.
ℤ^d wrapper of
`correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist`. -/
theorem
correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ (IsingModel.latticeGraph d) (Λ.volume n)
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card *
        Real.tanh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)).dist i j :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    (IsingModel.latticeGraph d) Λ J β hβJ n i j

/-- **ℤ^d along-ex §18.7 ferromagnetic capstone**: under `0 ≤ J, 0 < β`,
the same exponential-decay bound at stage `n` on `latticeGraph d`. -/
theorem
correlationAlongExhaustion_latticeGraph_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ (IsingModel.latticeGraph d) (Λ.volume n)
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card *
        Real.tanh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)).dist i j :=
correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
  d Λ J β (mul_nonneg hβ.le hJ) n i j

/-! ## Moved: §18.7 exp_rate_dist decay-capstone wrappers

The four exp_rate_dist wrappers
(`correlationΛ_latticeGraph_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist`,
its `_ferro` variant, and the corresponding
`correlationAlongExhaustion_latticeGraph` variants) now live in
`HighTemperatureBoundsDecayCapstonesExpRate.lean`. -/



/-! ## Moved: §18.7 highTempExpRate decay-capstone wrappers

The two `*_latticeGraph_*_le_two_pow_edges_mul_exp_highTempExpRate_dist`
wrappers (Λ and AlongExhaustion variants) now live in
`HighTemperatureBoundsDecayCapstonesHighTempExpRate.lean`. -/



/-! ## Moved: §18.7 exp_alpha_dist capstone wrappers

The six wrappers `correlation*_latticeGraph_*_exp_alpha_dist*`
(Λ + AlongExhaustion variants, including `of_le_highTempExpRate`) now
live in `HighTemperatureBoundsDecayAlphaDist.lean`. -/


end Ambient

end IsingModel
