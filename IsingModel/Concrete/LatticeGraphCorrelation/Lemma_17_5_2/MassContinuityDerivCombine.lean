import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityCrossSumFiniteBridge
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityScaledSummable
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityIncidentSum
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityCrossSumProfile

/-!
# GJ §17.5 Theorem 17.5.1 — PR-1i: the combined β-derivative `/c` bound (p.312)

Combines all PR-1i ingredients into the GJ p.312 bound for the finite-volume β-derivative of the
two-point profile divided by `c = ⟨φ_x φ_z⟩`.  From the finite c-cancelling Lebowitz deriv bound
(#4340) — `∂_β c_n ≤ J·(finite cross-sum) + J·(finite incident-sum)` — dividing by `c`:

* the cross-sum `/c` is routed through the finite ≤ infinite bridge (#4351), the dart-profile
  reduction (#4347) and the m⁻-scaled HLS convolution (#4350):
  `(cross-sum)/c ≤ 2·(1+(m⁻·d(x,z))^α)·e^{m⁻}·C·(1+d(x,z))^{−(2α−d)}`;
* the incident-sum `/c` uses the tight c-cancelling bound (#4344):
  `(incident-sum)/c ≤ 4d·(1+(m⁻·d(x,z))^α)·e^{m⁻}`.

The remaining step (rpow bookkeeping to the `Cnum·d(x,z)·c/(m⁻)^{2α}` Lipschitz form) feeds the
per-pair Lipschitz consumer.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Combined β-derivative `/c` bound** (GJ p.312): for `1≤α`, `1≤d`, `d<2α<2d`, `0<J`, `0<β`, a
non-adjacent binding pair `x≠z` with `{x,z}⊆box`, `m⁻(x,z)=globalPseudoMassDist>0`,
`∃ C>0, ∂_β c_n / c ≤ J·[2(1+(m⁻r)^α)e^{m⁻}·C(1+r)^{−(2α−d)}] + J·[4d(1+(m⁻r)^α)e^{m⁻}]`
(`r=d(x,z)`, `c = ⟨φ_x φ_z⟩^∞`).  Composes the finite c-cancelling deriv bound (#4340), the
finite≤infinite
cross bridge (#4351), the dart-profile reduction (#4347), the HLS convolution (#4350), and the tight
incident `/c` bound (#4344). -/
theorem combined_derivative_div_c_bound {α d : ℕ} (hα : 1 ≤ α) (hd : 1 ≤ d)
    (hαd : d < 2 * α) (hαd2 : α < d) {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    {n : ℕ} {x z : Fin d → ℤ} (hxz : x ≠ z) (hxz_nonadj : ¬ (latticeGraph d).Adj x z)
    (hsub : ({x, z} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n)
    (hm_pos : 0 < globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ))
    (hbind : pseudoMassFromParamsAtPairDist hα (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      = globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)) :
    ∃ C : ℝ, 0 < C ∧
      deriv (fun β' => correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β
        / correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
      ≤ J * (2 * (1 + (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              * (latticeDistance d x z : ℝ)) ^ α)
            * Real.exp (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ))
            * (C * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ)))))
        + J * ((4 * d : ℝ) * ((1 + (globalPseudoMassDist hα (cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) * (latticeDistance d x z : ℝ)) ^ α)
            * Real.exp (globalPseudoMassDist hα (cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ)))) := by
  classical
  have hm_nn : 0 ≤ globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) :=
    hm_pos.le
  have hx : x ∈ (cubicExhaustion d).volume n := hsub (Finset.mem_insert_self x {z})
  have hz : z ∈ (cubicExhaustion d).volume n :=
    hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self z))
  have hc_pos : 0 < correlationInfinite (latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} :=
    (correlationInfinite_pair_active_of_betaJ_pos_exhaustion
      (cubicExhaustion d) hβ (mul_pos hβ hJ) x z hxz).1
  obtain ⟨C, hC, hCconv⟩ :=
    dart_profile_sum_le_convolution (d := d) hd hαd hαd2 hm_pos (n := n)
  refine ⟨C, hC, ?_⟩
  have hpow : (0 : ℝ) ≤ (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      * (latticeDistance d x z : ℝ)) ^ α := pow_nonneg (mul_nonneg hm_nn (by positivity)) α
  have hcoef_nn : (0 : ℝ) ≤ 2 * (1 + (globalPseudoMassDist hα (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) * (latticeDistance d x z : ℝ)) ^ α)
      * Real.exp (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)) :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (Real.exp_nonneg _)
  have hcross := (div_le_div_of_nonneg_right
      (cross_sum_finite_le_infinite d J β hJ.le hβ hx hz) hc_pos.le).trans
    ((cross_sum_div_c_le_dart_profile hα hJ hβ hxz hbind).trans
      (mul_le_mul_of_nonneg_left (hCconv x z) hcoef_nn))
  have hinc := incident_sum_corr_fin_div_c_le hα hJ hβ hx hz hxz hxz_nonadj hbind
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
        + J * (((4 * d : ℝ) * ((1 + (globalPseudoMassDist hα (cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) * (latticeDistance d x z : ℝ)) ^ α)
            * Real.exp (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)))) *
          correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :=
        add_le_add (mul_le_mul_of_nonneg_left hSc hJ.le)
          (mul_le_mul_of_nonneg_left hSi hJ.le)
    _ = (J * (2 * (1 + (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              * (latticeDistance d x z : ℝ)) ^ α)
            * Real.exp (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ))
            * (C * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ)))))
          + J * ((4 * d : ℝ) * ((1 + (globalPseudoMassDist hα (cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) * (latticeDistance d x z : ℝ)) ^ α)
            * Real.exp (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)))))
          * correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} := by ring

end Ambient
end IsingModel
