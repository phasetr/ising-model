import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBounds

/-!
# Concrete §18.7 high-temperature exponential decay capstone wrappers

Narrow child module for the §18.7 high-temperature pair-correlation
exponential-decay capstone wrappers on `latticeGraph d` at `h = 0`. 16
theorems total: four capstone families -- `tanh_pow_dist`, the rate-form
`exp_rate_dist`, `exp_alpha_dist`, and
`exp_alpha_dist_of_le_highTempExpRate` -- each in
`correlationΛ_latticeGraph` and `correlationAlongExhaustion_latticeGraph`
versions plus ferromagnetic variants of both (4 families × 4 variants =
16 theorems). The theorem names are unchanged from the former
`HighTemperatureBounds` declarations.
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
