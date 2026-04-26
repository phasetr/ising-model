import IsingModel.Lattice
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Polynomial decay summability and constant HLS bound over ℤ^d (Steps 128–130)

We prove summability of `z ↦ (1 + latticeDistance d 0 z)^{-γ}` for `γ > d` (Step 128),
and derive the constant Hardy–Littlewood–Sobolev (HLS) convolution bound (Step 130).

## Strategy

1. **ℤ summability** (`summable_pow_neg_Z`): For `β > 1`,
   `∑_{n : ℤ} (1 + n.natAbs)^{-β}` converges, via `summable_one_div_nat_add_rpow`.

2. **Product summability** (`summable_prod_pow_neg_lattice`): By induction on `d`,
   `∑_{z : Fin d → ℤ} ∏_i (1 + (z i).natAbs)^{-β}` is summable for `β > 1`.

3. **AM-GM comparison** (`one_add_dist_rpow_neg_le`):
   `(1 + d(0,z))^{-γ} ≤ ∏_i (1 + |z_i|)^{-γ/d}` for `d ≥ 1, γ > 0`.

4. **Main theorem** (`summable_pow_neg_latticeDistance`): Combine 2 and 3 with `β = γ/d > 1`.

5. **Translation invariance** (`tsum_pow_neg_translate`):
   `∑_z (1 + d(x,z))^{-γ} = ∑_z (1 + d(0,z))^{-γ}` for any `x`.

6. **Constant HLS bound** (`tsum_pow_neg_conv_le_const`, Step 130):
   `∑_z (1+d(x,z))^{-α}·(1+d(y,z))^{-α} ≤ ∑_z (1+d(0,z))^{-2α}` for `2α > d`.
   Proof: AM-GM (`a·b ≤ (a²+b²)/2`) + translation invariance.

## References

* Glimm–Jaffe, *Quantum Physics*, 1st ed., §17.5 (pp.310–312).
-/

namespace IsingModel

open Real Set Finset

/-! ## Step 128A: ℤ summability -/

/-- `(1 + n.natAbs)^{-β}` for ℤ is summable when β > 1. -/
theorem summable_pow_neg_Z {β : ℝ} (hβ : 1 < β) :
    Summable (fun n : ℤ => (1 + n.natAbs : ℝ) ^ (-β)) := by
  apply Summable.of_nat_of_neg_add_one
  · -- ℕ part: n : ℕ ↦ (1 + n)^{-β}; compare with 1/|↑n + 1|^β
    apply Summable.congr ((Real.summable_one_div_nat_add_rpow 1 β).mpr hβ)
    intro n
    simp only [Int.natAbs_natCast]
    have hn : (0 : ℝ) ≤ 1 + ↑n := by positivity
    rw [abs_of_pos (by linarith), show (↑n : ℝ) + 1 = 1 + ↑n from by ring,
        Real.rpow_neg hn, one_div]
  · -- neg part: n : ℕ ↦ (n+2)^{-β}; compare with 1/|↑n + 2|^β
    apply Summable.congr ((Real.summable_one_div_nat_add_rpow 2 β).mpr hβ)
    intro n
    have hna : (-(↑n + 1 : ℤ)).natAbs = n + 1 := by
      rw [Int.natAbs_neg, show (↑n + 1 : ℤ) = ↑(n + 1) from by push_cast; ring,
          Int.natAbs_natCast]
    simp only [hna]
    have hn : (0 : ℝ) ≤ 1 + ↑(n + 1) := by positivity
    rw [abs_of_pos (by positivity : (0 : ℝ) < ↑n + 2),
        show (↑n : ℝ) + 2 = 1 + ↑(n + 1) from by push_cast; ring,
        Real.rpow_neg hn, one_div]

/-! ## Step 128B: Product summability over ℤ^d -/

/-- **Product summability** (Step 128B): For β > 1,
`∑_{z : Fin d → ℤ} ∏_i (1 + (z i).natAbs)^{-β}` is summable.

Proof by induction on `d` using `summable_prod_of_nonneg`. -/
theorem summable_prod_pow_neg_lattice (d : ℕ) {β : ℝ} (hβ : 1 < β) :
    Summable (fun z : Fin d → ℤ => ∏ i : Fin d, (1 + (z i).natAbs : ℝ) ^ (-β)) := by
  induction d with
  | zero => exact (hasSum_fintype _).summable
  | succ d ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (d + 1) => ℤ)).summable_iff]
    simp_rw [Function.comp_def, Fin.consEquiv, Equiv.coe_fn_mk,
             Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [summable_prod_of_nonneg
      (fun p => mul_nonneg (Real.rpow_nonneg (by positivity) _)
                           (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (by positivity) _)))]
    exact ⟨fun n => Summable.congr (ih.mul_left ((1 + n.natAbs : ℝ) ^ (-β)))
                                    (fun _ => rfl),
           by simp_rw [tsum_mul_left]
              exact (summable_pow_neg_Z hβ).mul_right _⟩

/-! ## Step 128C: AM-GM comparison -/

/-- **AM-GM comparison**: For d ≥ 1, γ > 0, z : Fin d → ℤ:
`(1 + latticeDistance d 0 z)^{-γ} ≤ ∏_i (1 + |z_i|)^{-γ/d}`.

Proof: AM-GM gives `∏(1+|z_i|)^{1/d} ≤ 1 + ∑|z_i|/d ≤ 1 + ∑|z_i| = 1 + d(0,z)`.
Raising to the γ power and inverting. -/
private lemma one_add_dist_rpow_neg_le {d : ℕ} (hd : 0 < d) {γ : ℝ} (hγ : 0 < γ)
    (z : Fin d → ℤ) :
    (1 + latticeDistance d 0 z : ℝ) ^ (-γ)
    ≤ ∏ i : Fin d, (1 + (z i).natAbs : ℝ) ^ (-γ / d) := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hd1 : (1 : ℝ) ≤ d := by norm_cast
  have hsum_eq : ∑ i : Fin d, (z i).natAbs = latticeDistance d 0 z := by
    simp [latticeDistance]
  have ha : ∀ i : Fin d, (0 : ℝ) ≤ (z i).natAbs := fun i => Nat.cast_nonneg _
  have hA : (0 : ℝ) < 1 + latticeDistance d 0 z := by positivity
  -- AM-GM: ∏(1+|z_i|)^{1/d} ≤ ∑(1/d)*(1+|z_i|) = 1 + ∑|z_i|/d
  have hw : ∑ _i : Fin d, (1 : ℝ) / d = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel hdR.ne'
  have hamgm : ∏ i : Fin d, (1 + (z i).natAbs : ℝ) ^ ((1 : ℝ) / d) ≤
      ∑ i : Fin d, (1 : ℝ) / d * (1 + (z i).natAbs : ℝ) :=
    geom_mean_le_arith_mean_weighted Finset.univ (fun _ => (1 : ℝ) / d)
      (fun i => 1 + (z i).natAbs) (fun _ _ => by positivity) hw (fun i _ => by linarith [ha i])
  -- 1 + ∑|z_i|/d ≤ 1 + ∑|z_i| = 1 + d(0,z)
  have hle2 : ∑ i : Fin d, (1 : ℝ) / d * (1 + (z i).natAbs : ℝ) ≤
      1 + latticeDistance d 0 z := by
    rw [← hsum_eq]; push_cast
    calc ∑ i : Fin d, (1 : ℝ) / ↑d * (1 + ↑(z i).natAbs)
        = (1 : ℝ) / ↑d * ∑ i, (1 + ↑(z i).natAbs) := by rw [← Finset.mul_sum]
      _ = (1 : ℝ) / ↑d * (↑d + ∑ i, (↑(z i).natAbs : ℝ)) := by
            congr 1
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
                Fintype.card_fin, nsmul_eq_mul, mul_one]
      _ = 1 + (∑ i, (↑(z i).natAbs : ℝ)) / ↑d := by field_simp
      _ ≤ 1 + ∑ i, (↑(z i).natAbs : ℝ) := by
            have hnn : (0 : ℝ) ≤ ∑ i : Fin d, (↑(z i).natAbs : ℝ) :=
              Finset.sum_nonneg (fun i _ => ha i)
            linarith [div_le_self hnn hd1]
  -- Combine: ∏(1+|z_i|)^{1/d} ≤ 1 + d(0,z)
  have hprod_le : ∏ i : Fin d, (1 + (z i).natAbs : ℝ) ^ ((1 : ℝ) / d) ≤
      1 + latticeDistance d 0 z := hamgm.trans hle2
  have hprod_pos : (0 : ℝ) < ∏ i : Fin d, (1 + (z i).natAbs : ℝ) ^ ((1 : ℝ) / d) :=
    Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (by linarith [ha i]) _)
  -- Rewrite RHS: ∏(1+|z_i|)^{-γ/d} = (∏(1+|z_i|)^{1/d})^{-γ}
  have hrw : ∏ i : Fin d, (1 + (z i).natAbs : ℝ) ^ (-γ / ↑d) =
      (∏ i : Fin d, (1 + (z i).natAbs : ℝ) ^ ((1 : ℝ) / ↑d)) ^ (-γ) := by
    have hstep : ∀ i : Fin d, (1 + (z i).natAbs : ℝ) ^ (-γ / ↑d) =
        ((1 + (z i).natAbs : ℝ) ^ ((1 : ℝ) / ↑d)) ^ (-γ) := fun i => by
      rw [← Real.rpow_mul (by linarith [ha i])]; congr 1; ring
    simp_rw [hstep]
    exact Real.finset_prod_rpow Finset.univ _
      (fun i _ => Real.rpow_nonneg (by linarith [ha i]) _) (-γ)
  -- (1+d(0,z))^{-γ} ≤ (∏...)^{-γ} since ∏... ≤ 1+d(0,z) and x^{-γ} is antitone for γ > 0
  rw [hrw]
  exact (Real.rpow_le_rpow_iff_of_neg hA hprod_pos (by linarith)).mpr hprod_le

/-! ## Step 128D: Main summability theorem -/

set_option maxHeartbeats 800000 in
-- Increased heartbeats: `summable_prod_pow_neg_lattice` type unification is slow.
/-- **ℤ^d polynomial summability** (Step 128D):
`∑_{z : Fin d → ℤ} (1 + latticeDistance d 0 z)^{-γ}` is summable for `γ > d`.

Proof: Apply the AM-GM comparison to reduce to `summable_prod_pow_neg_lattice` with
exponent `β = γ/d > 1` (since `γ > d ≥ 1`).

**Reference**: GJ §17.5 (pp.310–312), prerequisite for discrete HLS.

**Usage**: `discrete_hls_constant` can be de-axiomatized using this theorem
(the tsum is a valid positive constant C for the HLS bound). -/
theorem summable_pow_neg_latticeDistance (d : ℕ) {γ : ℝ} (hγ : (d : ℝ) < γ) :
    Summable (fun z : Fin d → ℤ => (1 + latticeDistance d 0 z : ℝ) ^ (-γ)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact (hasSum_fintype _).summable
  · have hβ : 1 < γ / d :=
      (one_lt_div (Nat.cast_pos.mpr hd)).mpr (by linarith)
    apply Summable.of_nonneg_of_le
    · intro z; positivity
    · intro z; exact one_add_dist_rpow_neg_le hd (by linarith) z
    · exact (summable_prod_pow_neg_lattice d hβ).congr fun z =>
        Finset.prod_congr rfl (fun i _ => by congr 1; ring)

/-! ## Steps 130A–B: Translation invariance and constant HLS bound -/

/-- **Translation invariance** (Step 130A): For any `x : Fin d → ℤ`,
`∑_z (1 + d(x,z))^{-γ} = ∑_z (1 + d(0,z))^{-γ}`. -/
lemma latticeDistance_translate_eq (d : ℕ) (x z : Fin d → ℤ) :
    latticeDistance d x z = latticeDistance d 0 (z - x) := by
  simp [latticeDistance, Pi.sub_apply]

/-- Translation invariance of the polynomial lattice tsum. -/
lemma tsum_pow_neg_translate (d : ℕ) (x : Fin d → ℤ) {γ : ℝ} :
    ∑' z : Fin d → ℤ, (1 + latticeDistance d x z : ℝ) ^ (-γ) =
    ∑' z : Fin d → ℤ, (1 + latticeDistance d 0 z : ℝ) ^ (-γ) := by
  simp_rw [latticeDistance_translate_eq d x]
  exact (Equiv.addRight (-x)).tsum_eq (fun z => (1 + latticeDistance d 0 z : ℝ) ^ (-γ))

/-- Translation invariance for summability. -/
lemma summable_pow_neg_translate (d : ℕ) (x : Fin d → ℤ) {γ : ℝ} (hγ : (d : ℝ) < γ) :
    Summable (fun z : Fin d → ℤ => (1 + latticeDistance d x z : ℝ) ^ (-γ)) := by
  have hf : (fun z : Fin d → ℤ => (1 + latticeDistance d x z : ℝ) ^ (-γ)) =
            (fun z => (1 + latticeDistance d 0 z : ℝ) ^ (-γ)) ∘ (· - x) := by
    ext z; rw [Function.comp, latticeDistance_translate_eq]
  rw [hf]
  exact (summable_pow_neg_latticeDistance d hγ).comp_injective
    (fun a b h => by simpa using h)

/-- **Constant HLS bound** (Step 130B):
`∑_z (1 + d(x,z))^{-α}·(1 + d(y,z))^{-α} ≤ ∑_z (1 + d(0,z))^{-2α}` for `2α > d`.

Proof: AM-GM (`a·b ≤ (a² + b²)/2`) + translation invariance of both sums.

**Reference**: GJ §17.5 (pp.310–312); prerequisite for the full HLS inequality. -/
theorem tsum_pow_neg_conv_le_const (d : ℕ) {α : ℝ} (hαd : (d : ℝ) < 2 * α)
    (x y : Fin d → ℤ) :
    ∑' z : Fin d → ℤ,
        (1 + latticeDistance d x z : ℝ) ^ (-α) *
        (1 + latticeDistance d y z : ℝ) ^ (-α) ≤
    ∑' z : Fin d → ℤ, (1 + latticeDistance d 0 z : ℝ) ^ (-(2 * α)) := by
  have hSx := summable_pow_neg_translate d x hαd
  have hSy := summable_pow_neg_translate d y hαd
  have hbound : ∀ z : Fin d → ℤ,
      (1 + latticeDistance d x z : ℝ) ^ (-α) * (1 + latticeDistance d y z : ℝ) ^ (-α) ≤
      ((1 + latticeDistance d x z : ℝ) ^ (-(2 * α)) +
       (1 + latticeDistance d y z : ℝ) ^ (-(2 * α))) / 2 := fun z => by
    set a := (1 + latticeDistance d x z : ℝ) ^ (-α)
    set b := (1 + latticeDistance d y z : ℝ) ^ (-α)
    have ha2 : a ^ 2 = (1 + latticeDistance d x z : ℝ) ^ (-(2 * α)) := by
      simp only [a]
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
      congr 1; ring
    have hb2 : b ^ 2 = (1 + latticeDistance d y z : ℝ) ^ (-(2 * α)) := by
      simp only [b]
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
      congr 1; ring
    nlinarith [sq_nonneg (a - b), ha2, hb2]
  have hSsum := (hSx.add hSy).div_const 2
  calc ∑' z, (1 + latticeDistance d x z : ℝ) ^ (-α) * (1 + latticeDistance d y z : ℝ) ^ (-α)
      ≤ ∑' z, (((1 + latticeDistance d x z : ℝ) ^ (-(2 * α)) +
                  (1 + latticeDistance d y z : ℝ) ^ (-(2 * α))) / 2) :=
          (Summable.of_nonneg_of_le (fun z => by positivity) hbound hSsum).tsum_le_tsum
            hbound hSsum
    _ = (∑' z, (1 + latticeDistance d x z : ℝ) ^ (-(2 * α)) +
          ∑' z, (1 + latticeDistance d y z : ℝ) ^ (-(2 * α))) / 2 := by
          rw [tsum_div_const, hSx.tsum_add hSy]
    _ = ∑' z, (1 + latticeDistance d 0 z : ℝ) ^ (-(2 * α)) := by
          rw [tsum_pow_neg_translate d x, tsum_pow_neg_translate d y]; ring

end IsingModel
