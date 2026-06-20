import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# A polynomial-moment bound for the geometric series (GJ §18.5)

The rooted-tree Kotecky--Preiss induction sums a leaf polymer into its parent,
leaving a `|parent|`-power factor; iterating accumulates polynomial moments of the
per-vertex polymer activity.  The analytic ingredient is the closed bound on the
`d`-th moment of a geometric series:
`∑_ℓ ℓ^d r^ℓ ≤ d!·(1−r)^{-(d+1)}` for `0 ≤ r < 1`.

`tsum_pow_mul_geometric_le`: bounds `ℓ^d` termwise by `d!·\binom{ℓ+d}{d}`
(`ℓ^d ≤ (ℓ+1)^d ≤ (ℓ+d)^{\underline d} = d!·\binom{ℓ+d}{d}`,
`Nat.pow_sub_le_descFactorial` + `Nat.descFactorial_eq_factorial_mul_choose`) and then
evaluates the negative-binomial geometric series
(`tsum_choose_mul_geometric_of_norm_lt_one`).

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

/-- **Polynomial-moment bound for the geometric series.**  For `0 ≤ r < 1` and any
`d`, the `d`-th moment of the geometric series is at most `d!·(1−r)^{-(d+1)}`:
`∑_ℓ ℓ^d r^ℓ ≤ d!/(1−r)^{d+1}`.  Each `ℓ^d` is dominated by `d!·\binom{ℓ+d}{d}`, and
the resulting negative-binomial series sums to `(1−r)^{-(d+1)}`. -/
theorem tsum_pow_mul_geometric_le (d : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    ∑' ℓ : ℕ, (ℓ : ℝ) ^ d * r ^ ℓ ≤ (d.factorial : ℝ) / (1 - r) ^ (d + 1) := by
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hterm : ∀ ℓ : ℕ, (ℓ : ℝ) ^ d * r ^ ℓ
      ≤ (d.factorial : ℝ) * ((ℓ + d).choose d : ℝ) * r ^ ℓ := by
    intro ℓ
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hr0 ℓ)
    have hnat : ℓ ^ d ≤ d.factorial * (ℓ + d).choose d := by
      have hsub : (ℓ + 1) ^ d ≤ (ℓ + d).descFactorial d := by
        have hpd := Nat.pow_sub_le_descFactorial (ℓ + d) d
        have he : ℓ + d + 1 - d = ℓ + 1 := by omega
        rwa [he] at hpd
      calc ℓ ^ d ≤ (ℓ + 1) ^ d := Nat.pow_le_pow_left (Nat.le_succ ℓ) d
        _ ≤ (ℓ + d).descFactorial d := hsub
        _ = d.factorial * (ℓ + d).choose d :=
            Nat.descFactorial_eq_factorial_mul_choose (ℓ + d) d
    calc (ℓ : ℝ) ^ d = ((ℓ ^ d : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((d.factorial * (ℓ + d).choose d : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (d.factorial : ℝ) * ((ℓ + d).choose d : ℝ) := by push_cast; ring
  have hsummL : Summable (fun ℓ : ℕ => (ℓ : ℝ) ^ d * r ^ ℓ) :=
    summable_pow_mul_geometric_of_norm_lt_one d hnorm
  have hsummR : Summable
      (fun ℓ : ℕ => (d.factorial : ℝ) * ((ℓ + d).choose d : ℝ) * r ^ ℓ) := by
    simp_rw [mul_assoc]
    exact (summable_choose_mul_geometric_of_norm_lt_one d hnorm).mul_left _
  refine (Summable.tsum_le_tsum hterm hsummL hsummR).trans_eq ?_
  simp_rw [mul_assoc]
  rw [tsum_mul_left, tsum_choose_mul_geometric_of_norm_lt_one d hnorm, mul_one_div]

/-- **Tail polynomial-moment bound for the geometric series.**  For `0 ≤ r < 1` and any
`d`, the `d`-th moment of the geometric series restricted to `ℓ ≥ 1` (reindexed
`ℓ ↦ ℓ + 1`) carries an extra factor `r`: `∑_ℓ (ℓ+1)^d r^{ℓ+1} ≤ r·d!/(1−r)^{d+1}`.  Each
`(ℓ+1)^d` is dominated by `d!·\binom{ℓ+d}{d}` directly
(`Nat.pow_sub_le_descFactorial`), and the factor `r` is pulled out of `r^{ℓ+1}`.  This is
the sharpening used when the summed objects (e.g. nonempty rooted polymers) have size at
least one, so the `ℓ = 0` term is absent. -/
theorem tsum_succ_pow_mul_geometric_succ_le (d : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    ∑' ℓ : ℕ, ((ℓ + 1 : ℕ) : ℝ) ^ d * r ^ (ℓ + 1)
      ≤ r * ((d.factorial : ℝ) / (1 - r) ^ (d + 1)) := by
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hterm : ∀ ℓ : ℕ, ((ℓ + 1 : ℕ) : ℝ) ^ d * r ^ (ℓ + 1)
      ≤ r * ((d.factorial : ℝ) * ((ℓ + d).choose d : ℝ)) * r ^ ℓ := by
    intro ℓ
    have hnat : (ℓ + 1) ^ d ≤ d.factorial * (ℓ + d).choose d := by
      have hpd := Nat.pow_sub_le_descFactorial (ℓ + d) d
      have he : ℓ + d + 1 - d = ℓ + 1 := by omega
      rw [he] at hpd
      calc (ℓ + 1) ^ d ≤ (ℓ + d).descFactorial d := hpd
        _ = d.factorial * (ℓ + d).choose d :=
            Nat.descFactorial_eq_factorial_mul_choose (ℓ + d) d
    have hb : ((ℓ + 1 : ℕ) : ℝ) ^ d ≤ (d.factorial : ℝ) * ((ℓ + d).choose d : ℝ) := by
      calc ((ℓ + 1 : ℕ) : ℝ) ^ d = (((ℓ + 1) ^ d : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((d.factorial * (ℓ + d).choose d : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = (d.factorial : ℝ) * ((ℓ + d).choose d : ℝ) := by push_cast; ring
    rw [pow_succ]
    calc ((ℓ + 1 : ℕ) : ℝ) ^ d * (r ^ ℓ * r)
        = r * (((ℓ + 1 : ℕ) : ℝ) ^ d * r ^ ℓ) := by ring
      _ ≤ r * (((d.factorial : ℝ) * ((ℓ + d).choose d : ℝ)) * r ^ ℓ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (pow_nonneg hr0 ℓ)) hr0
      _ = r * ((d.factorial : ℝ) * ((ℓ + d).choose d : ℝ)) * r ^ ℓ := by ring
  have hsummL : Summable (fun ℓ : ℕ => ((ℓ + 1 : ℕ) : ℝ) ^ d * r ^ (ℓ + 1)) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ d * r ^ n) 1).mpr
      (summable_pow_mul_geometric_of_norm_lt_one d hnorm)
  have hsummR : Summable
      (fun ℓ : ℕ => r * ((d.factorial : ℝ) * ((ℓ + d).choose d : ℝ)) * r ^ ℓ) := by
    simp_rw [mul_assoc]
    exact ((summable_choose_mul_geometric_of_norm_lt_one d hnorm).mul_left _).mul_left _
  refine (Summable.tsum_le_tsum hterm hsummL hsummR).trans_eq ?_
  simp_rw [mul_assoc]
  rw [tsum_mul_left, tsum_mul_left,
    tsum_choose_mul_geometric_of_norm_lt_one d hnorm, mul_one_div]

end IsingModel
