import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityDartScaledHLS
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityDartProfileBoxVertex

/-!
# GJ §17.5 Theorem 17.5.1 — PR-1i: summability of the m⁻-scaled HLS convolution summand

Exposes the summability of the scaled neighbour-shift convolution summand
`u ↦ 1/(1+(t·d(x,u))^α)·∑_{v∼u} 1/(1+(t·d(z,v))^α)` (proven internally inside
`tsum_mul_neighborFinset_sum_scaled_le`, #4336) as a standalone lemma.  It is needed to bound the
finite box-vertex sum (#4349) by the infinite-lattice tsum via `Summable.sum_le_tsum`.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Summability of the m⁻-scaled HLS convolution summand.**  For `d < 2α` and `t > 0`,
`u ↦ 1/(1+(t·d(x,u))^α)·∑_{v∈neighborFinset u} 1/(1+(t·d(z,v))^α)` is summable over `Fin d → ℤ`.
Each scaled kernel is dominated by `Ct·(1+s)^{−α}` (the `one_div_one_add_M_t_pow_…` bound), so the
summand is `≤ Ct²·` the unscaled summand, which is summable
(`summable_mul_neighborFinset_sum_pow_neg`); `Summable.of_nonneg_of_le` closes it. -/
theorem summable_mul_neighborFinset_sum_scaled {d : ℕ} {α : ℕ} (hαd : d < 2 * α)
    {t : ℝ} (ht : 0 < t) (x z : Fin d → ℤ) :
    Summable (fun u : Fin d → ℤ => 1 / (1 + (t * (latticeDistance d x u : ℝ)) ^ α) *
      (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
        1 / (1 + (t * (latticeDistance d z v : ℝ)) ^ α))) := by
  set Ct : ℝ := max 1 (t ^ α)⁻¹ * (2 : ℝ) ^ α with hCt
  have hkernel : ∀ s : ℝ, 0 ≤ s →
      1 / (1 + (t * s) ^ α) ≤ Ct * (1 + s) ^ (-(α : ℝ)) := by
    intro s hs
    have h := one_div_one_add_M_t_pow_le_const_mul_one_div_one_add_pow_pow
      (M := t) (t := s) (α := α) ht hs
    rw [one_div_one_add_pow_eq_rpow_neg hs] at h
    rw [hCt]; exact h
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
  have hsum_unscaled := summable_mul_neighborFinset_sum_pow_neg (α := (α : ℝ)) x z
    (Nat.cast_nonneg α) (by exact_mod_cast hαd)
  have hlhs_nn : ∀ u : Fin d → ℤ, 0 ≤
      1 / (1 + (t * (latticeDistance d x u : ℝ)) ^ α) *
        (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
          1 / (1 + (t * (latticeDistance d z v : ℝ)) ^ α)) := fun u => by positivity
  exact Summable.of_nonneg_of_le hlhs_nn hpt (hsum_unscaled.mul_left _)

/-- **Cross-sum dart-profile convolution bound** (GJ p.312): for `d < 2α < 2d` and `m > 0`, the
PR-1i cross-sum dart-profile sum decays as `(1+d(x,z))^{−(2α−d)}`:
`∃ C>0, ∀ x z, ∑_{dt:Dart} s(x,dt.fst)·s(z,dt.snd) ≤ C·(1+d(x,z))^{−(2α−d)}`,
`s(a,b) = 1/(1+(m·d(a,b))^α)`.  Composes the dart-profile ≤ box-vertex bound (#4349), the
box-vertex sum ≤ infinite-lattice tsum (`Finset.sum_coe_sort` + `Summable.sum_le_tsum`, using the
scaled summability above), and the m⁻-scaled HLS convolution bound (#4336
`tsum_mul_neighborFinset_sum_scaled_le`). -/
theorem dart_profile_sum_le_convolution {d : ℕ} (hd : 1 ≤ d) {α : ℕ} (hαd : d < 2 * α)
    (hαd2 : α < d) {m : ℝ} (hm_pos : 0 < m) {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ x z : Fin d → ℤ,
      ∑ dt : (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).Dart,
          (1 / (1 + (m * (latticeDistance d x dt.fst.val : ℝ)) ^ α))
            * (1 / (1 + (m * (latticeDistance d z dt.snd.val : ℝ)) ^ α))
        ≤ C * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ))) := by
  obtain ⟨C, hC, hCbd⟩ := tsum_mul_neighborFinset_sum_scaled_le hd hαd hαd2 hm_pos
  refine ⟨C, hC, fun x z => ?_⟩
  refine (dart_profile_sum_le_box_vertex_sum hm_pos.le x z).trans (le_trans ?_ (hCbd x z))
  -- box-vertex sum ≤ infinite-lattice tsum.
  have hf_nn : ∀ w : Fin d → ℤ, 0 ≤ 1 / (1 + (m * (latticeDistance d x w : ℝ)) ^ α)
      * ∑ u ∈ (latticeGraph d).neighborFinset w,
          1 / (1 + (m * (latticeDistance d z u : ℝ)) ^ α) := by
    intro w
    have hden : ∀ y v : Fin d → ℤ, (0 : ℝ) < 1 + (m * (latticeDistance d y v : ℝ)) ^ α := by
      intro y v
      have : (0 : ℝ) ≤ (m * (latticeDistance d y v : ℝ)) ^ α :=
        pow_nonneg (mul_nonneg hm_pos.le (by positivity)) α
      linarith
    exact mul_nonneg (le_of_lt (one_div_pos.mpr (hden x w)))
      (Finset.sum_nonneg (fun u _ => le_of_lt (one_div_pos.mpr (hden z u))))
  rw [Finset.sum_coe_sort ((cubicExhaustion d).volume n)
    (fun w => 1 / (1 + (m * (latticeDistance d x w : ℝ)) ^ α)
      * ∑ u ∈ (latticeGraph d).neighborFinset w, 1 / (1 + (m * (latticeDistance d z u : ℝ)) ^ α))]
  exact Summable.sum_le_tsum _ (fun w _ => hf_nn w)
    (summable_mul_neighborFinset_sum_scaled hαd hm_pos x z)

end Ambient
end IsingModel
