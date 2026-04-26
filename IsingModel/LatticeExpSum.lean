import IsingModel.Lattice
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Discrete exponential sum bounds on ℤ^d (Step 126)

Summability and exponential convolution bounds for exponentially-decaying functions
on the integer lattice ℤ^d. These provide the exponential decay estimates used in
GJ §17.5 Lemma 17.5.2 (continuity of the lattice mass) and Theorem 17.5.1.

Note: these are *exponential* bounds (for the Green's function decay), distinct from
the polynomial Hardy–Littlewood–Sobolev inequality in `discrete_hls_constant`.

## Main results

* `summable_exp_neg_int_natAbs` — `∑_{n:ℤ} exp(-m|n|)` converges for m > 0
* `summable_exp_neg_latticeDistance` — `∑_{z:Fin d→ℤ} exp(-m·‖z‖₁)` converges for m > 0
* `tsum_exp_neg_dist_eq` — translation invariance of the exponential sum
* `summable_exp_neg_dist` — summability for any basepoint
* `lattice_exp_sum_conv_le` — exponential convolution bound:
  `∑_z exp(-m·d(x,z))·exp(-m·d(y,z)) ≤ 2·C(m,d)·exp(-m·d(x,y)/2)`

## References

* Glimm–Jaffe, *Quantum Physics*, 1st ed., §17.5, Lemma 17.5.2, pp. 311–312.
-/

namespace IsingModel

set_option maxHeartbeats 400000 in
-- Geometric series reasoning over ℤ requires extra heartbeats for cast normalization.
/-- Summability of `n ↦ exp(-m · |n|)` over ℤ for m > 0.

Proof: split at 0; each half is a geometric series with ratio exp(-m) < 1. -/
theorem summable_exp_neg_int_natAbs {m : ℝ} (hm : 0 < m) :
    Summable (fun n : ℤ => Real.exp (-m * n.natAbs)) := by
  apply Summable.of_nat_of_neg_add_one
  · -- ℕ part: exp(-m*n) is summable as a geometric series
    have hlt : ‖Real.exp (-m)‖ < 1 := by
      rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hm)
    exact (summable_geometric_of_norm_lt_one hlt).congr fun n => by
      simp [← Real.exp_nat_mul, mul_comm]
  · -- negative part: exp(-m*(n+1)) is summable (same series, shifted by 1)
    have hlt : ‖Real.exp (-m)‖ < 1 := by
      rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hm)
    refine ((summable_geometric_of_norm_lt_one hlt).mul_left (Real.exp (-m))).congr fun n => ?_
    have hna : (-(↑n + 1) : ℤ).natAbs = n + 1 := by norm_cast
    simp only [hna]
    push_cast
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; ring

/-- First-coordinate decomposition of `latticeDistance`. -/
private lemma latticeDistance_cons (d : ℕ) (n : ℤ) (z : Fin d → ℤ) :
    latticeDistance (d + 1) 0 (Fin.cons n z) = n.natAbs + latticeDistance d 0 z := by
  simp [latticeDistance, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- The `exp(-m·d(0,·))` function over `Fin (d+1) → ℤ` factors under `Fin.cons`. -/
private lemma exp_neg_latticeDistance_cons (m : ℝ) (d : ℕ) (n : ℤ) (z : Fin d → ℤ) :
    Real.exp (-m * (latticeDistance (d + 1) 0 (Fin.cons n z) : ℝ))
    = Real.exp (-m * (n.natAbs : ℝ)) * Real.exp (-m * (latticeDistance d 0 z : ℝ)) := by
  rw [latticeDistance_cons]
  push_cast
  rw [mul_add, Real.exp_add]

set_option maxHeartbeats 400000 in
-- Fin.consEquiv rewriting under summable requires extra heartbeats for definitional normalization.
/-- Summability of `z ↦ exp(-m · latticeDistance d 0 z)` over Fin d → ℤ for m > 0.

Proof: induction on d; use the Fin.consEquiv decomposition and `summable_prod_of_nonneg`. -/
theorem summable_exp_neg_latticeDistance {m : ℝ} (hm : 0 < m) (d : ℕ) :
    Summable (fun z : Fin d → ℤ => Real.exp (-m * (latticeDistance d 0 z : ℝ))) := by
  induction d with
  | zero => exact (hasSum_fintype _).summable
  | succ d ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (d + 1) => ℤ)).summable_iff]
    simp_rw [Function.comp_def, Fin.consEquiv, Equiv.coe_fn_mk]
    simp_rw [exp_neg_latticeDistance_cons]
    rw [summable_prod_of_nonneg (fun p => mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))]
    refine ⟨fun n => Summable.congr (ih.mul_left (Real.exp (-m * ↑n.natAbs))) (fun z => rfl), ?_⟩
    simp_rw [tsum_mul_left]
    exact (summable_exp_neg_int_natAbs hm).mul_right _

/-- The tsum of `exp(-m·d(x,·))` is independent of the basepoint x. -/
theorem tsum_exp_neg_dist_eq (d : ℕ) {m : ℝ} (hm : 0 < m) (x : Fin d → ℤ) :
    ∑' z : Fin d → ℤ, Real.exp (-m * (latticeDistance d x z : ℝ))
    = ∑' z : Fin d → ℤ, Real.exp (-m * (latticeDistance d 0 z : ℝ)) := by
  have := hm.le
  rw [← (Equiv.addLeft x).tsum_eq]
  congr 1; ext z; congr 2
  simp [latticeDistance, Pi.add_apply]

/-- Summability of `z ↦ exp(-m·d(x,z))` for any basepoint x. -/
theorem summable_exp_neg_dist {m : ℝ} (hm : 0 < m) (d : ℕ) (x : Fin d → ℤ) :
    Summable (fun z : Fin d → ℤ => Real.exp (-m * (latticeDistance d x z : ℝ))) := by
  rw [← (Equiv.addLeft x).summable_iff]
  apply (summable_exp_neg_latticeDistance hm d).congr
  intro z; congr 2
  simp [latticeDistance, Pi.add_apply]

/-- **Discrete exponential convolution bound** (Step 126, GJ §17.5 prerequisite):
For m > 0 and x, y on ℤ^d,
`∑_{z ∈ ℤ^d} exp(-m·d(x,z)) · exp(-m·d(y,z)) ≤ 2 · C(m,d) · exp(-m·d(x,y)/2)`
where `C(m,d) = ∑_z exp(-m·d(0,z))`.

**References**: Glimm–Jaffe §17.5, Lemma 17.5.2 (pp. 311–312). -/
theorem lattice_exp_sum_conv_le {m : ℝ} (hm : 0 < m) (d : ℕ) (x y : Fin d → ℤ) :
    ∑' z : Fin d → ℤ,
        Real.exp (-m * (latticeDistance d x z : ℝ)) *
        Real.exp (-m * (latticeDistance d y z : ℝ))
    ≤ 2 * (∑' z : Fin d → ℤ, Real.exp (-m * (latticeDistance d 0 z : ℝ))) *
       Real.exp (-m * (latticeDistance d x y : ℝ) / 2) := by
  set C := ∑' z : Fin d → ℤ, Real.exp (-m * (latticeDistance d 0 z : ℝ))
  have hC_nonneg : 0 ≤ C := tsum_nonneg fun _ => Real.exp_nonneg _
  have hsumm_x := summable_exp_neg_dist hm d x
  have hsumm_y := summable_exp_neg_dist hm d y
  -- Summability of the product (bounded above by the x-term)
  have hsumm_conv : Summable (fun z : Fin d → ℤ =>
      Real.exp (-m * (latticeDistance d x z : ℝ)) *
      Real.exp (-m * (latticeDistance d y z : ℝ))) :=
    Summable.of_nonneg_of_le (fun z => mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
      (fun z => mul_le_of_le_one_right (Real.exp_nonneg _) (Real.exp_le_one_iff.mpr (by
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hm.le) (Nat.cast_nonneg _))))
      hsumm_x
  -- Pointwise bound: exp(-m*dx)*exp(-m*dy) ≤ exp(-m*d(x,y)/2)*exp(-m*min(dx,dy))
  have hpwise : ∀ z : Fin d → ℤ,
      Real.exp (-m * (latticeDistance d x z : ℝ)) *
      Real.exp (-m * (latticeDistance d y z : ℝ))
      ≤ Real.exp (-m * (latticeDistance d x y : ℝ) / 2) *
        Real.exp (-m * (min (latticeDistance d x z) (latticeDistance d y z) : ℝ)) := by
    intro z
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have htri : (latticeDistance d x y : ℝ) ≤ latticeDistance d x z + latticeDistance d y z := by
      have h := latticeDistance_triangle d x z y
      rw [latticeDistance_comm d z y] at h
      exact_mod_cast h
    have hmax_add_min : (latticeDistance d x z : ℝ) + latticeDistance d y z =
        (max (latticeDistance d x z) (latticeDistance d y z) : ℝ) +
        (min (latticeDistance d x z) (latticeDistance d y z) : ℝ) := by
      have := max_add_min (latticeDistance d x z) (latticeDistance d y z)
      exact_mod_cast this.symm
    have hmin_nn : (0 : ℝ) ≤ min (latticeDistance d x z : ℝ) (latticeDistance d y z : ℝ) :=
      le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hmax_ge_min : min (latticeDistance d x z : ℝ) (latticeDistance d y z : ℝ) ≤
        max (latticeDistance d x z : ℝ) (latticeDistance d y z : ℝ) := by simp
    have hmax_ge : (latticeDistance d x y : ℝ) / 2 ≤
        max (latticeDistance d x z : ℝ) (latticeDistance d y z : ℝ) := by
      nlinarith [hmax_add_min, hmax_ge_min]
    have hm_neg : -m < 0 := neg_lt_zero.mpr hm
    nlinarith [mul_le_mul_of_nonpos_left hmax_ge (le_of_lt hm_neg)]
  -- Helper: exp(-m*min(a,b)) ≤ exp(-m*a) + exp(-m*b)
  have hmin_le_sum : ∀ z : Fin d → ℤ,
      Real.exp (-m * (min (latticeDistance d x z) (latticeDistance d y z) : ℝ)) ≤
      Real.exp (-m * (latticeDistance d x z : ℝ)) +
      Real.exp (-m * (latticeDistance d y z : ℝ)) := by
    intro z
    rcases le_or_gt (latticeDistance d x z) (latticeDistance d y z) with h | h
    · have hm' : (min (latticeDistance d x z) (latticeDistance d y z) : ℝ) =
                 (latticeDistance d x z : ℝ) := by exact_mod_cast min_eq_left h
      rw [hm']; exact le_add_of_nonneg_right (Real.exp_nonneg _)
    · have hm' : (min (latticeDistance d x z) (latticeDistance d y z) : ℝ) =
                 (latticeDistance d y z : ℝ) := by exact_mod_cast min_eq_right (le_of_lt h)
      rw [hm']; exact le_add_of_nonneg_left (Real.exp_nonneg _)
  -- Summability of min-bound (bounded above by sum of x and y terms)
  have hsumm_min : Summable (fun z : Fin d → ℤ =>
      Real.exp (-m * (min (latticeDistance d x z) (latticeDistance d y z) : ℝ))) :=
    Summable.of_nonneg_of_le (fun z => Real.exp_nonneg _) hmin_le_sum (hsumm_x.add hsumm_y)
  -- The main chain of inequalities
  calc ∑' z, Real.exp (-m * (latticeDistance d x z : ℝ)) *
          Real.exp (-m * (latticeDistance d y z : ℝ))
      ≤ ∑' z, Real.exp (-m * (latticeDistance d x y : ℝ) / 2) *
           Real.exp (-m * (min (latticeDistance d x z) (latticeDistance d y z) : ℝ)) :=
        hsumm_conv.tsum_le_tsum hpwise (hsumm_min.mul_left _)
    _ = Real.exp (-m * (latticeDistance d x y : ℝ) / 2) *
         ∑' z, Real.exp (-m * (min (latticeDistance d x z) (latticeDistance d y z) : ℝ)) :=
        tsum_mul_left
    _ ≤ Real.exp (-m * (latticeDistance d x y : ℝ) / 2) *
         (∑' z, Real.exp (-m * (latticeDistance d x z : ℝ)) +
          ∑' z, Real.exp (-m * (latticeDistance d y z : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        calc ∑' z : Fin d → ℤ,
              Real.exp (-m * (min (latticeDistance d x z) (latticeDistance d y z) : ℝ))
            ≤ ∑' z : Fin d → ℤ,
              (Real.exp (-m * (latticeDistance d x z : ℝ)) +
               Real.exp (-m * (latticeDistance d y z : ℝ))) :=
              hsumm_min.tsum_le_tsum hmin_le_sum (hsumm_x.add hsumm_y)
          _ = ∑' z, Real.exp (-m * (latticeDistance d x z : ℝ)) +
              ∑' z, Real.exp (-m * (latticeDistance d y z : ℝ)) :=
              Summable.tsum_add hsumm_x hsumm_y
    _ = Real.exp (-m * (latticeDistance d x y : ℝ) / 2) * (C + C) := by
        rw [tsum_exp_neg_dist_eq d hm x, tsum_exp_neg_dist_eq d hm y]
    _ = 2 * C * Real.exp (-m * (latticeDistance d x y : ℝ) / 2) := by ring

end IsingModel
