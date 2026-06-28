import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.UnconditionalProfileLower
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.GlobalPseudoMassDist

/-!
# GJ §17.5 Theorem 17.5.1 — PR-1j-prep: interval-uniform per-pair m⁻ upper bound (p.312)

The per-pair distance pseudo-mass is bounded **above by a single constant** on a closed interval
`Icc β₁ β₂` inside the convergence window: for a distinct pair `x ≠ z`,
`pseudoMassFromParamsAtPairDist … ⟨J,0,β⟩ x z ≤ −log tanh(β₁·J)` for all `β ∈ Icc β₁ β₂`.

This is the interval-uniform **upper** bound (companion to the lower bound #4360), needed to bound
the `m^{2α}` factor in the GJ p.312 uniform Lipschitz constant.  Per-β `m⁻(x,z) ≤ −log tanh(βJ)`
(from the faithful correlation lower bound #4333 + `pseudoMass_le_iff_pseudoMassG_le`); the rate
`−log tanh(βJ)` is decreasing in β (tanh increasing), so `≤ −log tanh(β₁J)` on the interval.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Interval-uniform per-pair m⁻ upper bound** (GJ p.312): for a distinct pair `x ≠ z` and
`β ∈ Icc β₁ β₂` with `0 < β₁` and `Icc β₁ β₂ ⊆ ConvergenceRegion.window d J`,
`pseudoMassFromParamsAtPairDist hα (cubicExhaustion d) ⟨J,0,β⟩ x z ≤ −log tanh(β₁·J)` — a single
constant upper bound uniform over the interval.  Per-β `m⁻(x,z) ≤ −log tanh(βJ)` (faithful rate
#4333 + `pseudoMass_le_iff_pseudoMassG_le`); the rate is antitone in β. -/
theorem pseudoMassFromParamsAtPairDist_le_neg_log_tanh_beta1_on_Icc {α d : ℕ} (hα : 1 ≤ α)
    {J β₁ β₂ : ℝ} (hJ : 0 < J) (hβ₁ : 0 < β₁)
    (hIcc : Set.Icc β₁ β₂ ⊆ ConvergenceRegion.window d J)
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    ∀ β ∈ Set.Icc β₁ β₂,
      pseudoMassFromParamsAtPairDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) x z
        ≤ -Real.log (Real.tanh (β₁ * J)) := by
  intro β hβ
  have hβwin : β ∈ ConvergenceRegion.window d J := hIcc hβ
  have hβ_pos : 0 < β := lt_of_lt_of_le hβ₁ hβ.1
  have hpos : (0 : ℝ) < (IsingModel.latticeDistance d x z : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (fun h => hxz ((IsingModel.latticeDistance_eq_zero_iff d x z).mp h))
  have hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2 :=
    correlationInfinite_pair_active_of_betaJ_pos_exhaustion
      (cubicExhaustion d) hβ_pos (mul_pos hβ_pos hJ) x z hxz
  have hrate_nn : (0 : ℝ) ≤ -Real.log (Real.tanh (β * J)) :=
    le_trans zero_le_one (one_le_neg_log_tanh_betaJ_of_window hJ hβwin)
  -- per-β: m⁻(x,z) ≤ −log tanh(βJ).
  have hupper_beta : pseudoMassFromParamsAtPairDist hα (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ -Real.log (Real.tanh (β * J)) := by
    rw [pseudoMassFromParamsAtPairDist_of_ne hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      hxz hpos, pseudoMassExt_of_mem hα hpos hcorr]
    exact (pseudoMass_le_iff_pseudoMassG_le hα hpos hcorr hrate_nn).mpr
      (pseudoMassG_dist_tanh_rate_le_correlationInfinite_cubic hJ hβ_pos hxz hβwin)
  -- antitone: −log tanh(βJ) ≤ −log tanh(β₁J) since β₁ ≤ β.
  have htanh_pos : 0 < Real.tanh (β₁ * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hβ₁ hJ)) (Real.cosh_pos _)
  have htanh_le : Real.tanh (β₁ * J) ≤ Real.tanh (β * J) :=
    Real.tanh_strictMono.monotone (mul_le_mul_of_nonneg_right hβ.1 hJ.le)
  have hanti : -Real.log (Real.tanh (β * J)) ≤ -Real.log (Real.tanh (β₁ * J)) :=
    neg_le_neg (Real.log_le_log htanh_pos htanh_le)
  exact le_trans hupper_beta hanti

end Ambient
end IsingModel
