import IsingModel.PseudoMass.HLSSharpPairBound

/-!
# GJ §17.5 Theorem 17.5.1 — PR-1b: the m⁻-scaled neighbour-shift (dart) HLS convolution

This module supplies the `t`-scaled (`t = m⁻`) neighbour-shifted sharp HLS convolution bound, the
edge/dart analog of `tsum_one_div_one_add_scaled_pow_pair_le` (#4329).  It is the convolution at the
heart of the GJ p.312 derivative-ratio estimate for the *Ising* β-derivative, whose Lebowitz
bound is an edge cross-sum (dart sum), not GJ's site sum.

The scaled kernel `1/(1+(t·d)^α)` reduces to the unscaled `(1+d)^{−α}` via the form
bridge
`one_div_one_add_M_t_pow_le_const_mul_one_div_one_add_pow_pow`, so the bound follows from the
unscaled neighbour-shift convolution `tsum_mul_neighborFinset_sum_pow_neg_le` (#4327) with constant
`Ct²·C₄₃₂₇`.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **`t`-scaled neighbour-shift sharp HLS convolution.**  For `t > 0` and `d/2 < α < d`,
`∃ C>0, ∀ x z, ∑'_u 1/(1+(t·d(x,u))^α)·(∑_{v∼u} 1/(1+(t·d(z,v))^α)) ≤ C·(1+d(x,z))^{−(2α−d)}`.

This is the `t = m⁻` scaled, edge/dart form of the HLS convolution (the Ising β-derivative Lebowitz
bound is a nearest-neighbour edge cross-sum).  Each scaled kernel is dominated by `Ct·(1+d)^{−α}`
(`one_div_one_add_M_t_pow_le_const_mul_one_div_one_add_pow_pow`, `Ct = max 1 (t^α)⁻¹·2^α`), reducing
to the unscaled neighbour-shift convolution `tsum_mul_neighborFinset_sum_pow_neg_le`;
`C = Ct²·C₄₃₂₇`. -/
theorem tsum_mul_neighborFinset_sum_scaled_le {d : ℕ} (hd : 1 ≤ d) {α : ℕ}
    (hαd : d < 2 * α) (hαd2 : α < d) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 < C ∧ ∀ x z : Fin d → ℤ,
      ∑' u : Fin d → ℤ, 1 / (1 + (t * (latticeDistance d x u : ℝ)) ^ α) *
          (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
            1 / (1 + (t * (latticeDistance d z v : ℝ)) ^ α))
        ≤ C * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ))) := by
  obtain ⟨C0, hC0, hC0bd⟩ := tsum_mul_neighborFinset_sum_pow_neg_le (d := d) hd
    (α := (α : ℝ)) (Nat.cast_nonneg α) (by exact_mod_cast hαd2) (by exact_mod_cast hαd)
  set Ct : ℝ := max 1 (t ^ α)⁻¹ * (2 : ℝ) ^ α with hCt
  have hCt_pos : 0 < Ct := by
    rw [hCt]; exact mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (by positivity)
  -- per-kernel scaled → unscaled bound: `1/(1+(t·s)^α) ≤ Ct·(1+s)^{−α}`.
  have hkernel : ∀ s : ℝ, 0 ≤ s →
      1 / (1 + (t * s) ^ α) ≤ Ct * (1 + s) ^ (-(α : ℝ)) := by
    intro s hs
    have h := one_div_one_add_M_t_pow_le_const_mul_one_div_one_add_pow_pow
      (M := t) (t := s) (α := α) ht hs
    rw [one_div_one_add_pow_eq_rpow_neg hs] at h
    rw [hCt]; exact h
  refine ⟨Ct ^ 2 * C0, by positivity, fun x z => ?_⟩
  -- pointwise: scaled summand ≤ Ct²·(unscaled summand).
  have hpt : ∀ u : Fin d → ℤ,
      1 / (1 + (t * (latticeDistance d x u : ℝ)) ^ α) *
          (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
            1 / (1 + (t * (latticeDistance d z v : ℝ)) ^ α))
        ≤ Ct ^ 2 * ((1 + (latticeDistance d x u : ℝ)) ^ (-(α : ℝ)) *
            (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
              (1 + (latticeDistance d z v : ℝ)) ^ (-(α : ℝ)))) := by
    intro u
    have hx := hkernel (latticeDistance d x u : ℝ) (by positivity)
    have hsumv : (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
            1 / (1 + (t * (latticeDistance d z v : ℝ)) ^ α))
        ≤ Ct * (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
            (1 + (latticeDistance d z v : ℝ)) ^ (-(α : ℝ))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun v _ => hkernel (latticeDistance d z v : ℝ) (by positivity))
    have hxnn : 0 ≤ 1 / (1 + (t * (latticeDistance d x u : ℝ)) ^ α) := by positivity
    have hsumv_nn : 0 ≤ ∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
        (1 + (latticeDistance d z v : ℝ)) ^ (-(α : ℝ)) := by positivity
    calc 1 / (1 + (t * (latticeDistance d x u : ℝ)) ^ α) *
            (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
              1 / (1 + (t * (latticeDistance d z v : ℝ)) ^ α))
        ≤ (Ct * (1 + (latticeDistance d x u : ℝ)) ^ (-(α : ℝ))) *
            (Ct * (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
              (1 + (latticeDistance d z v : ℝ)) ^ (-(α : ℝ)))) :=
          mul_le_mul hx hsumv (by positivity) (by positivity)
      _ = Ct ^ 2 * ((1 + (latticeDistance d x u : ℝ)) ^ (-(α : ℝ)) *
            (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
              (1 + (latticeDistance d z v : ℝ)) ^ (-(α : ℝ)))) := by ring
  -- summability of both sides.
  have hsum_unscaled := summable_mul_neighborFinset_sum_pow_neg (α := (α : ℝ)) x z
    (Nat.cast_nonneg α) (by exact_mod_cast hαd)
  have hsum_rhs : Summable (fun u : Fin d → ℤ => Ct ^ 2 *
      ((1 + (latticeDistance d x u : ℝ)) ^ (-(α : ℝ)) *
        (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
          (1 + (latticeDistance d z v : ℝ)) ^ (-(α : ℝ))))) := hsum_unscaled.mul_left _
  have hlhs_nn : ∀ u : Fin d → ℤ, 0 ≤
      1 / (1 + (t * (latticeDistance d x u : ℝ)) ^ α) *
        (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
          1 / (1 + (t * (latticeDistance d z v : ℝ)) ^ α)) := fun u => by positivity
  have hlhs_sum : Summable (fun u : Fin d → ℤ =>
      1 / (1 + (t * (latticeDistance d x u : ℝ)) ^ α) *
        (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
          1 / (1 + (t * (latticeDistance d z v : ℝ)) ^ α))) :=
    Summable.of_nonneg_of_le hlhs_nn hpt hsum_rhs
  calc ∑' u : Fin d → ℤ, 1 / (1 + (t * (latticeDistance d x u : ℝ)) ^ α) *
          (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
            1 / (1 + (t * (latticeDistance d z v : ℝ)) ^ α))
      ≤ ∑' u : Fin d → ℤ, Ct ^ 2 *
          ((1 + (latticeDistance d x u : ℝ)) ^ (-(α : ℝ)) *
            (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
              (1 + (latticeDistance d z v : ℝ)) ^ (-(α : ℝ)))) :=
        hlhs_sum.tsum_le_tsum hpt hsum_rhs
    _ = Ct ^ 2 * ∑' u : Fin d → ℤ,
          ((1 + (latticeDistance d x u : ℝ)) ^ (-(α : ℝ)) *
            (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
              (1 + (latticeDistance d z v : ℝ)) ^ (-(α : ℝ)))) := by rw [tsum_mul_left]
    _ ≤ Ct ^ 2 * (C0 * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ)))) :=
        mul_le_mul_of_nonneg_left (hC0bd x z) (by positivity)
    _ = Ct ^ 2 * C0 * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ))) := by ring

end Ambient
end IsingModel
