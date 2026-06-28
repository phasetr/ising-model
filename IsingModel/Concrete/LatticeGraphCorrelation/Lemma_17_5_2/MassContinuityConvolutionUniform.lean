import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityScaledSummable

/-!
# GJ §17.5 Theorem 17.5.1 — PR-1j: n-uniform cross-sum dart-profile convolution bound (p.312)

The n-uniform version of `dart_profile_sum_le_convolution` (#4350): the convolution constant `C` is
pulled out in front of the `∀ n` quantifier (it is the n-independent infinite-lattice tsum const).
This is required to take the `n → ∞` limit of the finite-stage β-derivative bound while keeping the
RHS fixed (the limit argument needs a single `C` valid for all stages `n`).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **n-uniform cross-sum dart-profile convolution bound** (GJ p.312): for `d<2α<2d`, `m>0`,
`∃ C>0, ∀ n x z, ∑_{dt:Dart_n} s(x,dt.fst)·s(z,dt.snd) ≤ C·(1+d(x,z))^{−(2α−d)}` — the *same* `C`
for every stage `n` (the n-independent infinite-lattice convolution constant of #4336).
Same proof as `dart_profile_sum_le_convolution` (#4350) with `C` obtained from the n-free tsum bound
`tsum_mul_neighborFinset_sum_scaled_le` and the `∀ n x z` quantifier moved inside. -/
theorem dart_profile_sum_le_convolution_uniform {d : ℕ} (hd : 1 ≤ d) {α : ℕ} (hαd : d < 2 * α)
    (hαd2 : α < d) {m : ℝ} (hm_pos : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (x z : Fin d → ℤ),
      ∑ dt : (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).Dart,
          (1 / (1 + (m * (latticeDistance d x dt.fst.val : ℝ)) ^ α))
            * (1 / (1 + (m * (latticeDistance d z dt.snd.val : ℝ)) ^ α))
        ≤ C * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ))) := by
  obtain ⟨C, hC, hCbd⟩ := tsum_mul_neighborFinset_sum_scaled_le hd hαd hαd2 hm_pos
  refine ⟨C, hC, fun n x z => ?_⟩
  refine (dart_profile_sum_le_box_vertex_sum (n := n) hm_pos.le x z).trans (le_trans ?_ (hCbd x z))
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
