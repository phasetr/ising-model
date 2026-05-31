import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassBasic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# No-go facts for all-displacement cubic tanh-profile families

The named predicate `cubicTanhProfileBound` is a pointwise profile condition:
`pseudoMassG α r (-log(βJ·2d)) ≤ tanh(βJ)^dist(0,w)`.  When
`0 < tanh(βJ) < 1` and the rate is nonnegative, `pseudoMassG` is a fixed
positive number while the right-hand side tends to zero along a coordinate
axis.  Hence the predicate cannot hold at every nonzero displacement.

This module records that obstruction explicitly so downstream Lemma 17.5.2
wrappers treat the all-displacement tanh-profile family as a conditional
interface, not as something discharged from the elementary high-temperature
condition alone.
-/

open scoped BigOperators

namespace IsingModel
namespace Ambient

/-- **Distance of a first-axis lattice point**: in positive dimension, the
point with first coordinate `n` and all other coordinates zero has
`latticeDistance` exactly `n` from the origin. -/
theorem latticeDistance_firstAxis_eq {d : ℕ} (hd : 0 < d) (n : ℕ) :
    IsingModel.latticeDistance d 0
        (fun j : Fin d => if j = (⟨0, hd⟩ : Fin d) then (n : ℤ) else 0) = n := by
  let i : Fin d := ⟨0, hd⟩
  change IsingModel.latticeDistance d 0
      (fun j : Fin d => if j = i then (n : ℤ) else 0) = n
  unfold IsingModel.latticeDistance
  rw [Finset.sum_eq_single i]
  · simp only [Pi.zero_apply, if_true]
    omega
  · intro b _ hbi
    simp [hbi]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- **Nonzero first-axis lattice point**: the first-axis point at `n + 1` is
not the origin. -/
theorem firstAxis_succ_ne_zero {d : ℕ} (hd : 0 < d) (n : ℕ) :
    (fun j : Fin d =>
        if j = (⟨0, hd⟩ : Fin d) then ((n + 1 : ℕ) : ℤ) else 0) ≠ 0 := by
  let i : Fin d := ⟨0, hd⟩
  change (fun j : Fin d => if j = i then ((n + 1 : ℕ) : ℤ) else 0) ≠ 0
  intro h
  have hcoord := congrArg (fun f : Fin d → ℤ => f i) h
  have hpos : ((n + 1 : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  simp only [Pi.zero_apply, if_true] at hcoord
  exact hpos hcoord

/-- **No all-displacement cubic tanh-profile family at a decaying tanh base**:
if `0 < tanh(βJ) < 1` and the Lean high-temperature rate is nonnegative, then
`cubicTanhProfileBound` cannot hold for every nonzero displacement.

The proof chooses a far enough point on a coordinate axis so that
`tanh(βJ)^dist` is smaller than the fixed positive value of `pseudoMassG` at the
rate `-log(βJ·2d)`. -/
theorem not_forall_cubicTanhProfileBound_of_tanh_pos_lt_one
    {α d : ℕ} {r β J : ℝ} (hd : 0 < d) (hr : 0 < r)
    (hrate_nonneg : 0 ≤ -Real.log (β * J * ↑(2 * d)))
    (htanh_pos : 0 < Real.tanh (β * J))
    (htanh_lt_one : Real.tanh (β * J) < 1) :
    ¬ ∀ w : Fin d → ℤ, w ≠ 0 → cubicTanhProfileBound α d r β J w := by
  intro hfamily
  let c : ℝ := pseudoMassG α r (-Real.log (β * J * ↑(2 * d)))
  have hc_pos : 0 < c := pseudoMassG_pos α hrate_nonneg hr
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hc_pos htanh_lt_one
  have hpow_succ_lt : Real.tanh (β * J) ^ (n + 1) < c := by
    calc
      Real.tanh (β * J) ^ (n + 1) =
          Real.tanh (β * J) ^ n * Real.tanh (β * J) := by
        rw [pow_succ]
      _ ≤ Real.tanh (β * J) ^ n * 1 := by
        exact mul_le_mul_of_nonneg_left htanh_lt_one.le (pow_nonneg htanh_pos.le n)
      _ = Real.tanh (β * J) ^ n := by ring
      _ < c := hn
  let i : Fin d := ⟨0, hd⟩
  let w : Fin d → ℤ := fun j => if j = i then ((n + 1 : ℕ) : ℤ) else 0
  have hw_ne : w ≠ 0 := by
    change (fun j : Fin d => if j = i then ((n + 1 : ℕ) : ℤ) else 0) ≠ 0
    exact firstAxis_succ_ne_zero hd n
  have hdist : IsingModel.latticeDistance d 0 w = n + 1 := by
    change IsingModel.latticeDistance d 0
      (fun j : Fin d => if j = i then ((n + 1 : ℕ) : ℤ) else 0) = n + 1
    exact latticeDistance_firstAxis_eq hd (n + 1)
  have hbound := hfamily w hw_ne
  rw [cubicTanhProfileBound_iff] at hbound
  change c ≤ Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 w at hbound
  rw [hdist] at hbound
  exact not_lt_of_ge hbound hpow_succ_lt

/-- **High-temperature positive-coupling no-go for all-displacement tanh
profiles**: under `0 < βJ` and `βJ·2d < 1`, the all-nonzero
`cubicTanhProfileBound` family is impossible in positive dimension.

This is the direct form relevant to the Lemma 17.5.2 cubic tanh-profile
wrappers: the `_forall` wrappers are conditional APIs and cannot be discharged
from the elementary high-temperature assumptions alone. -/
theorem not_forall_cubicTanhProfileBound_of_betaJ_pos_high_temp
    {α d : ℕ} {r β J : ℝ} (hd : 0 < d) (hr : 0 < r)
    (hβJ_pos : 0 < β * J) (hlt : β * J * ↑(2 * d) < 1) :
    ¬ ∀ w : Fin d → ℤ, w ≠ 0 → cubicTanhProfileBound α d r β J w := by
  have hq_nonneg : 0 ≤ β * J * ↑(2 * d) :=
    mul_nonneg hβJ_pos.le (Nat.cast_nonneg (2 * d))
  have hrate_nonneg : 0 ≤ -Real.log (β * J * ↑(2 * d)) :=
    neg_nonneg.mpr (Real.log_nonpos hq_nonneg hlt.le)
  have htanh_pos : 0 < Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hβJ_pos) (Real.cosh_pos _)
  have htanh_lt_one : Real.tanh (β * J) < 1 :=
    lt_of_abs_lt (Real.abs_tanh_lt_one _)
  exact not_forall_cubicTanhProfileBound_of_tanh_pos_lt_one
    hd hr hrate_nonneg htanh_pos htanh_lt_one

end Ambient
end IsingModel
