import IsingModel.PseudoMass.HLSSharpPairBound

/-!
# GJ §17.5 Theorem 17.5.1 — PR-1j-final: mass-uniform HLS convolution bound (p.312)

The m⁻-scaled HLS convolution bound (#4336) with the constant `C` made **uniform over all scales
`t ≥ mmin`** (for a fixed `mmin > 0`): `∃ C>0, ∀ t ≥ mmin, ∀ x z, ∑'_u s_t(x,u)·∑_{v∼u} s_t(z,v) ≤
C·(1+d(x,z))^{−(2α−d)}`.  This is needed because the GJ p.312 sharp Lipschitz constant uses the
convolution at the β-varying mass `m⁻(β)`, and the per-scale `Ct = max 1 (t^α)⁻¹·2^α` blows up as
`t → 0`; with `t ≥ mmin`, `Ct ≤ Ctmax = max 1 (mmin^α)⁻¹·2^α` makes `C = Ctmax²·C₀` uniform.

Same proof as `tsum_mul_neighborFinset_sum_scaled_le` (#4336) with `Ct` replaced by the
scale-independent `Ctmax`, using the per-kernel domination at the *fixed* `Ctmax` (valid for every
`t ≥ mmin` since `(t^α)⁻¹ ≤ (mmin^α)⁻¹`).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Mass-uniform m⁻-scaled HLS convolution bound** (GJ p.312): for `d < 2α < 2d` and a fixed
`mmin > 0`, `∃ C>0, ∀ t ≥ mmin, ∀ x z, ∑'_u (1/(1+(t·d(x,u))^α))·∑_{v∼u}(1/(1+(t·d(z,v))^α)) ≤
C·(1+d(x,z))^{−(2α−d)}` — the *same* `C` for every scale `t ≥ mmin`.  The per-kernel domination
`1/(1+(t·s)^α) ≤ Ctmax·(1+s)^{−α}` holds at the scale-independent `Ctmax = max 1 (mmin^α)⁻¹·2^α` for
all `t ≥ mmin` (since `(t^α)⁻¹ ≤ (mmin^α)⁻¹`); `C = Ctmax²·C₀`, `C₀` the unscaled HLS constant. -/
theorem tsum_mul_neighborFinset_sum_scaled_le_uniform {d : ℕ} (hd : 1 ≤ d) {α : ℕ}
    (hαd : d < 2 * α) (hαd2 : α < d) {mmin : ℝ} (hmmin : 0 < mmin) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ), mmin ≤ t → ∀ x z : Fin d → ℤ,
      ∑' u : Fin d → ℤ, 1 / (1 + (t * (latticeDistance d x u : ℝ)) ^ α) *
          (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
            1 / (1 + (t * (latticeDistance d z v : ℝ)) ^ α))
        ≤ C * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ))) := by
  obtain ⟨C0, hC0, hC0bd⟩ := tsum_mul_neighborFinset_sum_pow_neg_le (d := d) hd
    (α := (α : ℝ)) (Nat.cast_nonneg α) (by exact_mod_cast hαd2) (by exact_mod_cast hαd)
  set Ctmax : ℝ := max 1 (mmin ^ α)⁻¹ * (2 : ℝ) ^ α with hCtmax
  have hCtmax_pos : 0 < Ctmax := by
    rw [hCtmax]; exact mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (by positivity)
  refine ⟨Ctmax ^ 2 * C0, by positivity, fun t ht x z => ?_⟩
  have ht_pos : 0 < t := lt_of_lt_of_le hmmin ht
  -- per-kernel scaled → unscaled bound at the *scale-independent* `Ctmax`.
  have hkernel : ∀ s : ℝ, 0 ≤ s →
      1 / (1 + (t * s) ^ α) ≤ Ctmax * (1 + s) ^ (-(α : ℝ)) := by
    intro s hs
    have h := one_div_one_add_M_t_pow_le_const_mul_one_div_one_add_pow_pow
      (M := t) (t := s) (α := α) ht_pos hs
    rw [one_div_one_add_pow_eq_rpow_neg hs] at h
    refine le_trans h (mul_le_mul_of_nonneg_right ?_ (by positivity))
    rw [hCtmax]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ α)
    exact max_le_max (le_refl 1)
      (inv_anti₀ (by positivity) (pow_le_pow_left₀ hmmin.le ht α))
  -- pointwise: scaled summand ≤ Ctmax²·(unscaled summand).
  have hpt : ∀ u : Fin d → ℤ,
      1 / (1 + (t * (latticeDistance d x u : ℝ)) ^ α) *
          (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
            1 / (1 + (t * (latticeDistance d z v : ℝ)) ^ α))
        ≤ Ctmax ^ 2 * ((1 + (latticeDistance d x u : ℝ)) ^ (-(α : ℝ)) *
            (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
              (1 + (latticeDistance d z v : ℝ)) ^ (-(α : ℝ)))) := by
    intro u
    have hx := hkernel (latticeDistance d x u : ℝ) (by positivity)
    have hsumv : (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
            1 / (1 + (t * (latticeDistance d z v : ℝ)) ^ α))
        ≤ Ctmax * (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
            (1 + (latticeDistance d z v : ℝ)) ^ (-(α : ℝ))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun v _ => hkernel (latticeDistance d z v : ℝ) (by positivity))
    calc 1 / (1 + (t * (latticeDistance d x u : ℝ)) ^ α) *
            (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
              1 / (1 + (t * (latticeDistance d z v : ℝ)) ^ α))
        ≤ (Ctmax * (1 + (latticeDistance d x u : ℝ)) ^ (-(α : ℝ))) *
            (Ctmax * (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
              (1 + (latticeDistance d z v : ℝ)) ^ (-(α : ℝ)))) :=
          mul_le_mul hx hsumv (by positivity) (by positivity)
      _ = Ctmax ^ 2 * ((1 + (latticeDistance d x u : ℝ)) ^ (-(α : ℝ)) *
            (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
              (1 + (latticeDistance d z v : ℝ)) ^ (-(α : ℝ)))) := by ring
  have hsum_unscaled := summable_mul_neighborFinset_sum_pow_neg (α := (α : ℝ)) x z
    (Nat.cast_nonneg α) (by exact_mod_cast hαd)
  have hsum_rhs : Summable (fun u : Fin d → ℤ => Ctmax ^ 2 *
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
      ≤ ∑' u : Fin d → ℤ, Ctmax ^ 2 *
          ((1 + (latticeDistance d x u : ℝ)) ^ (-(α : ℝ)) *
            (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
              (1 + (latticeDistance d z v : ℝ)) ^ (-(α : ℝ)))) :=
        hlhs_sum.tsum_le_tsum hpt hsum_rhs
    _ = Ctmax ^ 2 * ∑' u : Fin d → ℤ,
          ((1 + (latticeDistance d x u : ℝ)) ^ (-(α : ℝ)) *
            (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
              (1 + (latticeDistance d z v : ℝ)) ^ (-(α : ℝ)))) := by rw [tsum_mul_left]
    _ ≤ Ctmax ^ 2 * (C0 * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ)))) :=
        mul_le_mul_of_nonneg_left (hC0bd x z) (by positivity)
    _ = Ctmax ^ 2 * C0 * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ))) := by ring

end Ambient
end IsingModel
