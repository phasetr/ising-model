import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityCrossSumFiniteBridge
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityConvolutionUniform
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityIncidentSumTight
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityCrossSumProfile

/-!
# GJ §17.5 Theorem 17.5.1 — PR-1j: n-uniform combined β-derivative `/c` bound (p.312)

The n-uniform version of `combined_derivative_div_c_bound_tight` (#4356): the convolution constant
`C` is pulled out in front of the `∀ n` quantifier (using the n-uniform convolution #4357 and the
n-independent bounded incident #4355).  This gives a single bound on the finite-stage β-derivative
valid for *every* exhaustion stage `n` (with `{x,z} ⊆ volume n`), which is what the `n → ∞` limit
(toward the infinite-volume `m⁻` derivative) consumes.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **n-uniform combined β-derivative `/c` bound** (GJ p.312): for `1≤α`, `1≤d`, `d<2α<2d`, `0<J`,
`0<β`, a non-adjacent binding pair `x≠z` with `m⁻(x,z)=globalPseudoMassDist>0`,
`∃ C>0, ∀ n, {x,z}⊆vol n → ∂_β c_n/c ≤ J·[2(1+(m⁻r)^α)e^{m⁻}C(1+r)^{−(2α−d)}] + J·[4d(1+2^α)e^{m⁻}]`
(`r=d(x,z)`) — the *same* `C` for every stage `n`.  Same as #4356 but with
`C` from the n-uniform convolution (#4357) and the `∀ n` quantifier inside, enabling the `n→∞`
limit. -/
theorem combined_derivative_div_c_bound_tight_uniform {α d : ℕ} (hα : 1 ≤ α) (hd : 1 ≤ d)
    (hαd : d < 2 * α) (hαd2 : α < d) {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    {x z : Fin d → ℤ} (hxz : x ≠ z) (hxz_nonadj : ¬ (latticeGraph d).Adj x z)
    (hm_pos : 0 < globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ))
    (hbind : pseudoMassFromParamsAtPairDist hα (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      = globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ),
      ({x, z} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n →
      deriv (fun β' => correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β
        / correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
      ≤ J * (2 * (1 + (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              * (latticeDistance d x z : ℝ)) ^ α)
            * Real.exp (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ))
            * (C * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ)))))
        + J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α)
            * Real.exp (globalPseudoMassDist hα (cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ)))) := by
  classical
  have hm_nn : 0 ≤ globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) :=
    hm_pos.le
  have hc_pos : 0 < correlationInfinite (latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} :=
    (correlationInfinite_pair_active_of_betaJ_pos_exhaustion
      (cubicExhaustion d) hβ (mul_pos hβ hJ) x z hxz).1
  have hpow : (0 : ℝ) ≤ (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      * (latticeDistance d x z : ℝ)) ^ α := pow_nonneg (mul_nonneg hm_nn (by positivity)) α
  have hcoef_nn : (0 : ℝ) ≤ 2 * (1 + (globalPseudoMassDist hα (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) * (latticeDistance d x z : ℝ)) ^ α)
      * Real.exp (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)) :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (Real.exp_nonneg _)
  obtain ⟨C, hC, hCbd⟩ :=
    dart_profile_sum_le_convolution_uniform (d := d) hd hαd hαd2 hm_pos
  refine ⟨C, hC, fun n hsub => ?_⟩
  have hx : x ∈ (cubicExhaustion d).volume n := hsub (Finset.mem_insert_self x {z})
  have hz : z ∈ (cubicExhaustion d).volume n :=
    hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self z))
  have hcross := (div_le_div_of_nonneg_right
      (cross_sum_finite_le_infinite d J β hJ.le hβ hx hz) hc_pos.le).trans
    ((cross_sum_div_c_le_dart_profile hα hJ hβ hxz hbind).trans
      (mul_le_mul_of_nonneg_left (hCbd n x z) hcoef_nn))
  have hinc := incident_sum_corr_fin_div_c_le_tight hα hJ hβ hx hz hxz hxz_nonadj hbind
  rw [div_le_iff₀ hc_pos]
  refine (derivative_profile_cubic_le_lebowitz_cancelling d J β hJ.le hβ hxz hsub).trans ?_
  have hSc := (div_le_iff₀ hc_pos).mp hcross
  have hSi := (div_le_iff₀ hc_pos).mp hinc
  calc J * _ + J * _
      ≤ J * ((2 * (1 + (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              * (latticeDistance d x z : ℝ)) ^ α)
            * Real.exp (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ))
            * (C * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ))))) *
          correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z})
        + J * (((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α)
            * Real.exp (globalPseudoMassDist hα (cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ)))) *
          correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :=
        add_le_add (mul_le_mul_of_nonneg_left hSc hJ.le)
          (mul_le_mul_of_nonneg_left hSi hJ.le)
    _ = (J * (2 * (1 + (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              * (latticeDistance d x z : ℝ)) ^ α)
            * Real.exp (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ))
            * (C * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ)))))
          + J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α)
            * Real.exp (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)))))
          * correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} := by ring

end Ambient
end IsingModel
