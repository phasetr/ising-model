import IsingModel.Lattice
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Chebyshev → ℓ¹ rate conversion for transfer-matrix decay (GJ §17.5)

In Glimm–Jaffe §17.5 (p. 312) the transfer matrix gives exponential decay
`e^{-m·dist}` of correlations in the lattice hyperplane separation `dist`, which on
`ℤ^d` is the ℓ∞ (Chebyshev) distance `latticeDistanceInf`. Combined with the
geometric bound `dist ≥ |x-y|/a₀` (`a₀ = d`,
`latticeDistance_le_card_mul_latticeDistanceInf`), this yields decay at rate `m/d`
in the ℓ¹ distance `latticeDistance` used throughout the development. These lemmas
record that rate conversion, both as a real-number inequality and at the level of
`Real.exp`.
-/

namespace IsingModel

open Real

/-- **ℓ¹ rate is bounded by the ℓ∞ rate** (GJ §17.5): for `m ≥ 0` and `d > 0`,
`(m/d)·|x-y|₁ ≤ m·|x-y|_∞`. The real-valued form of
`latticeDistance_le_card_mul_latticeDistanceInf`: scaling the ℓ¹ rate down by `d`
makes it dominated by the ℓ∞ rate, so a decay rate `m` in the hyperplane
separation gives rate `m/d` in the ℓ¹ distance. -/
theorem rate_div_card_mul_latticeDistance_le
    (d : ℕ) (x y : Fin d → ℤ) {m : ℝ} (hm : 0 ≤ m) :
    m / d * (latticeDistance d x y : ℝ) ≤ m * (latticeDistanceInf d x y : ℝ) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp [latticeDistance, latticeDistanceInf]
  · have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    have hcast : (latticeDistance d x y : ℝ) ≤ d * (latticeDistanceInf d x y : ℝ) := by
      exact_mod_cast latticeDistance_le_card_mul_latticeDistanceInf d x y
    rw [div_mul_eq_mul_div, div_le_iff₀ hdpos]
    calc m * (latticeDistance d x y : ℝ)
        ≤ m * (d * (latticeDistanceInf d x y : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hcast hm
      _ = m * (latticeDistanceInf d x y : ℝ) * d := by ring

/-- **Exponential decay rate conversion** (GJ §17.5): hyperplane-separation
(ℓ∞) decay `e^{-m·|x-y|_∞}` dominates ℓ¹-distance decay at the reduced rate
`m/d`, `e^{-m·|x-y|_∞} ≤ e^{-(m/d)·|x-y|₁}` for `m ≥ 0`. Immediate from
`rate_div_card_mul_latticeDistance_le` and monotonicity of `Real.exp`. -/
theorem exp_neg_rate_latticeDistanceInf_le
    (d : ℕ) (x y : Fin d → ℤ) {m : ℝ} (hm : 0 ≤ m) :
    Real.exp (-(m * (latticeDistanceInf d x y : ℝ)))
      ≤ Real.exp (-(m / d * (latticeDistance d x y : ℝ))) := by
  apply Real.exp_le_exp.mpr
  simpa using rate_div_card_mul_latticeDistance_le d x y hm

/-- **Transfer-matrix bound transfer to the ℓ¹ distance** (GJ §17.5): a
correlation bound `c ≤ A·e^{-m·|x-y|_∞}` in the hyperplane separation transfers
to a bound `c ≤ A·e^{-(m/d)·|x-y|₁}` in the ℓ¹ distance, for `m ≥ 0` and `A ≥ 0`.
This is exactly how Glimm–Jaffe §17.5 turns the transfer-matrix exponential decay
(rate `m` in the lattice hyperplane separation) into the `e^{-m·dist}` bound with
`dist ≥ |x-y|/a₀`, `a₀ = d`. -/
theorem le_exp_neg_rate_latticeDistance_of_le_exp_neg_latticeDistanceInf
    (d : ℕ) (x y : Fin d → ℤ) {m A c : ℝ} (hm : 0 ≤ m) (hA : 0 ≤ A)
    (hc : c ≤ A * Real.exp (-(m * (latticeDistanceInf d x y : ℝ)))) :
    c ≤ A * Real.exp (-(m / d * (latticeDistance d x y : ℝ))) :=
  hc.trans (mul_le_mul_of_nonneg_left (exp_neg_rate_latticeDistanceInf_le d x y hm) hA)

end IsingModel
