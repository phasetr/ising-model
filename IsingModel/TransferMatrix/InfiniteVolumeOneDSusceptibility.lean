import IsingModel.TransferMatrix.InfiniteVolumeOneD
import IsingModel.TransferMatrix.OneDimSusceptibility
import IsingModel.TransferMatrix.OneDimCorrelationLength

/-!
# Infinite-volume 1D Ising susceptibility and mass form (GJ §17.1)

Two infinite-volume 1D physical observables, consuming the two-point capstone
`twoPointFunction 1 ⟨J,0,β⟩ r = (tanh βJ)^(latticeDistance 1 0 r)` (#3535):

* **Susceptibility**: the bilateral lattice sum of the two-point function equals the
  closed-form susceptibility,
  `∑_{r : Fin 1 → ℤ} (tanh βJ)^(latticeDistance 1 0 r) = isingSusceptibility1D (βJ)
    = (1 + tanh βJ)/(1 − tanh βJ)`,
  via the `ℤ = ℕ ⊔ ℕ` bilateral split (`HasSum.int_rec`) and the
  `(Fin 1 → ℤ) ≃ ℤ` reduction.  The `r = 0` diagonal contributes
  `(tanh βJ)^0 = 1 = ⟨σ₀²⟩`.
* **Mass form**: `twoPointFunction 1 ⟨J,0,β⟩ r = exp(−m·|r|)` with mass
  `m = correlationMass (βJ) = −log tanh βJ` (the inverse correlation length).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304–306.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

/-- **Bilateral geometric sum of the two-point decay rate** (GJ §17.1): the
two-sided `ℤ`-sum of `(tanh a)^|n|` equals the closed-form susceptibility
`isingSusceptibility1D a = (1 + tanh a)/(1 − tanh a)`, for `a = βJ > 0`.  Split via
`ℤ = ℕ ⊔ ℕ` (`HasSum.int_rec`): the non-negative branch contributes
`∑ₖ (tanh a)ᵏ` and the negative branch `∑ₖ (tanh a)^{k+1}`. -/
theorem hasSum_tanh_pow_natAbs_int {a : ℝ} (ha : 0 < a) :
    HasSum (fun n : ℤ => Real.tanh a ^ n.natAbs) (isingSusceptibility1D a) := by
  have htanh_lt : Real.tanh a < 1 := Real.tanh_lt_one a
  have hne : (1 : ℝ) - Real.tanh a ≠ 0 := by linarith
  have hf : HasSum (fun k : ℕ => Real.tanh a ^ k) (1 - Real.tanh a)⁻¹ := by
    rw [← tsum_tanh_pow ha]; exact (summable_tanh_pow ha).hasSum
  have hg : HasSum (fun k : ℕ => Real.tanh a ^ (k + 1))
      (Real.tanh a * (1 - Real.tanh a)⁻¹) := by
    simpa only [pow_succ'] using hf.mul_left (Real.tanh a)
  have hsum := HasSum.int_rec hf hg
  have heq : (fun n : ℤ => Real.tanh a ^ n.natAbs)
      = Int.rec (fun k : ℕ => Real.tanh a ^ k) (fun k : ℕ => Real.tanh a ^ (k + 1)) := by
    funext n
    rcases n with k | k
    · rfl
    · rfl
  rw [heq, show isingSusceptibility1D a
      = (1 - Real.tanh a)⁻¹ + Real.tanh a * (1 - Real.tanh a)⁻¹ from by
        rw [isingSusceptibility1D]; field_simp]
  exact hsum

/-- The bilateral `ℤ`-sum of `(tanh a)^|n|` is summable, for `a = βJ > 0`. -/
theorem summable_tanh_pow_natAbs_int {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℤ => Real.tanh a ^ n.natAbs) :=
  (hasSum_tanh_pow_natAbs_int ha).summable

/-- The bilateral `ℤ`-sum of `(tanh a)^|n|` equals the susceptibility, for `a = βJ > 0`. -/
theorem tsum_tanh_pow_natAbs_int {a : ℝ} (ha : 0 < a) :
    ∑' n : ℤ, Real.tanh a ^ n.natAbs = isingSusceptibility1D a :=
  (hasSum_tanh_pow_natAbs_int ha).tsum_eq

/-- **Infinite-volume 1D Ising susceptibility** (Glimm–Jaffe §17.1): the lattice sum of
the two-point function over all separations equals the closed-form susceptibility,
`∑_{r : Fin 1 → ℤ} (tanh βJ)^(latticeDistance 1 0 r) = isingSusceptibility1D (βJ)
  = (1 + tanh βJ)/(1 − tanh βJ)`, for `βJ > 0`.  The summand equals the two-point
function `twoPointFunction 1 ⟨J,0,β⟩ r` for `r ≠ 0` (#3535) and `1 = ⟨σ₀²⟩` at the
diagonal `r = 0`. -/
theorem tsum_tanh_pow_latticeDistance_eq_susceptibility {J β : ℝ} (hβJ : 0 < β * J) :
    ∑' r : Fin 1 → ℤ, Real.tanh (β * J) ^ latticeDistance 1 0 r
      = isingSusceptibility1D (β * J) := by
  have hrw : ∀ r : Fin 1 → ℤ, latticeDistance 1 0 r = (r 0).natAbs := by
    intro r
    simp only [latticeDistance, Fin.sum_univ_one, Pi.zero_apply, zero_sub, Int.natAbs_neg]
  rw [← tsum_tanh_pow_natAbs_int hβJ,
    ← (Equiv.funUnique (Fin 1) ℤ).tsum_eq (fun n : ℤ => Real.tanh (β * J) ^ n.natAbs)]
  refine tsum_congr (fun r => ?_)
  rw [hrw]
  rfl

/-- **Mass form of the infinite-volume 1D two-point function** (Glimm–Jaffe §17.1, §17.5):
for `βJ > 0` and `r ≠ 0`, the infinite-volume two-point function is the pure exponential
`twoPointFunction 1 ⟨J,0,β⟩ r = exp(−m·|r|)` with mass
`m = correlationMass (βJ) = −log tanh βJ` (the inverse correlation length). -/
theorem twoPointFunction_one_eq_exp_neg_mass {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (r : Fin 1 → ℤ) (hr0 : r 0 ≠ 0) (hβJ : 0 < β * J) :
    Ambient.twoPointFunction 1 (⟨J, 0, β⟩ : IsingParams ℝ) r
      = Real.exp (-(correlationMass (β * J)) * (latticeDistance 1 0 r : ℝ)) := by
  rw [twoPointFunction_one_eq_tanh_pow hJ hβ r hr0, tanh_pow_eq_exp_neg_mass hβJ]

end TransferMatrix

end IsingModel
