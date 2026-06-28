import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityScaledSummable
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityConvolutionMassUniform

/-!
# GJ §17.5 Theorem 17.5.1 — PR-FV4b-uniformC: mass-uniform dart-profile convolution (p.312)

The **mass-uniform** version of `dart_profile_sum_le_convolution` (#4350): the convolution constant
`C` is pulled out in front of **both** the `∀ m ≥ mmin` and the `∀ n` quantifiers (using the
mass-uniform HLS convolution #4362 `tsum_mul_neighborFinset_sum_scaled_le_uniform`).  Whereas
`dart_profile_sum_le_convolution_uniform` (#4357) fixes a single scale `m` and is uniform only in
`n`, this version gives one `C` valid for **every scale `m ≥ mmin` and every stage `n`**.

This is exactly what the finite-volume uniform-in-`β` Lipschitz estimate needs: the FV sharp
β-derivative bound uses the convolution at the β-varying scale `m⁻_FV(σ, volume n)`, which (by the
two-sided mass bounds #4380/#4381) ranges in `[mmin, Mwitness]`; with `m⁻_FV ≥ mmin` the convolution
constant is β-independent.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Mass-uniform cross-sum dart-profile convolution bound** (GJ p.312): for `d<2α<2d` and a fixed
`mmin>0`, `∃ C>0, ∀ m ≥ mmin, ∀ n x z, ∑_{dt:Dart_n} s_m(x,dt.fst)·s_m(z,dt.snd) ≤ C(1+d)^{−(2α−d)}`
— the *same* `C` for every scale `m ≥ mmin` and every stage `n` (`s_m(a,b)=1/(1+(m·d(a,b))^α)`).
Same proof as `dart_profile_sum_le_convolution` (#4350) with `C`
obtained from the mass-uniform tsum bound `tsum_mul_neighborFinset_sum_scaled_le_uniform` (#4362)
and the `∀ m ≥ mmin, ∀ n x z` quantifiers moved inside. -/
theorem dart_profile_sum_le_convolution_mass_uniform {d : ℕ} (hd : 1 ≤ d) {α : ℕ} (hαd : d < 2 * α)
    (hαd2 : α < d) {mmin : ℝ} (hmmin : 0 < mmin) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℝ), mmin ≤ m → ∀ (n : ℕ) (x z : Fin d → ℤ),
      ∑ dt : (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).Dart,
          (1 / (1 + (m * (latticeDistance d x dt.fst.val : ℝ)) ^ α))
            * (1 / (1 + (m * (latticeDistance d z dt.snd.val : ℝ)) ^ α))
        ≤ C * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ))) := by
  obtain ⟨C, hC, hCbd⟩ := tsum_mul_neighborFinset_sum_scaled_le_uniform hd hαd hαd2 hmmin
  refine ⟨C, hC, fun m hm n x z => ?_⟩
  have hm_pos : 0 < m := lt_of_lt_of_le hmmin hm
  refine (dart_profile_sum_le_box_vertex_sum (n := n) hm_pos.le x z).trans
    (le_trans ?_ (hCbd m hm x z))
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
