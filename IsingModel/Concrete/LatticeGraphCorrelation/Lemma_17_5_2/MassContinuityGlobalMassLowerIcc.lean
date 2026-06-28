import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.GlobalPseudoMassDistUpper

/-!
# GJ §17.5 Theorem 17.5.1 — PR-1j-prep: interval-uniform m⁻ lower bound (p.312)

The system pseudo-mass `m⁻(β) = globalPseudoMassDist` is bounded **below by a single positive
constant** on a closed interval `Icc β₁ β₂` inside the strict high-temperature window
`β₂·J·(2d) < 1/2`: `globalPseudoMassDistRestrictedRate α d J β₂ ≤ m⁻(β)` for all `β ∈ Icc β₁ β₂`.

This is the interval-uniform lower bound needed for the uniform convolution constant `C` of the GJ
p.312 sharp Lipschitz estimate (the convolution `Ct = max 1 (m⁻^α)⁻¹·2^α` blows up as `m⁻→0`, so a
uniform `mmin > 0` is required).  Per-β `m⁻(β) ≥ RestrictedRate(β)`
(`globalPseudoMassDistRestrictedRate_le_globalPseudoMassDist`); `RestrictedRate` is antitone in `β`
(`−log(B/(1−B))` and `simonLiebRate = −log B` both decrease as `B = βJ2d` increases), so
`RestrictedRate(β) ≥ RestrictedRate(β₂)`.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Interval-uniform m⁻ lower bound** (GJ p.312): for `β ∈ Icc β₁ β₂` with `0 < β₁`, `β₁ ≤ β₂`,
`β₂·J·(2d) < 1/2` (strict high-temp window), the system pseudo-mass is bounded below by the single
positive constant `globalPseudoMassDistRestrictedRate α d J β₂`:
`globalPseudoMassDistRestrictedRate α d J β₂ ≤ globalPseudoMassDist hα (cubicExhaustion d) ⟨J,0,β⟩`.
Per-β `m⁻(β) ≥ RestrictedRate(β)`, and `RestrictedRate` is antitone in `β`. -/
theorem globalPseudoMassDist_ge_restrictedRate_beta2 {α d : ℕ} (hα : 1 ≤ α) (hd : 0 < d)
    {J β₁ β₂ : ℝ} (hJ : 0 < J) (hβ₁ : 0 < β₁)
    (hβ₂_half : β₂ * J * (2 * d) < 1 / 2) :
    ∀ β ∈ Set.Icc β₁ β₂,
      globalPseudoMassDistRestrictedRate α d J β₂
        ≤ globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) := by
  intro β hβ
  have hβ_pos : 0 < β := lt_of_lt_of_le hβ₁ hβ.1
  have hβJ_pos : 0 < β * J := mul_pos hβ_pos hJ
  have hd2_pos : (0 : ℝ) < 2 * d := by positivity
  have hβJd_pos : 0 < β * J * (2 * d) := mul_pos hβJ_pos hd2_pos
  have hβJd_le : β * J * (2 * d) ≤ β₂ * J * (2 * d) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hβ.2 hJ.le) hd2_pos.le
  have hβJd_half : β * J * (2 * d) < 1 / 2 := lt_of_le_of_lt hβJd_le hβ₂_half
  have hB2_pos : 0 < β₂ * J * (2 * d) := lt_of_lt_of_le hβJd_pos hβJd_le
  -- per-β: `m⁻(β) ≥ RestrictedRate(β)`.
  have h1 := globalPseudoMassDistRestrictedRate_le_globalPseudoMassDist
    hα hd hJ.le hβ_pos hβJ_pos hβJd_pos hβJd_half
  refine le_trans ?_ h1
  -- antitone: `RestrictedRate(β₂) ≤ RestrictedRate(β)`.
  unfold globalPseudoMassDistRestrictedRate simonLiebRate
  have h1mB_pos : (0 : ℝ) < 1 - β * J * (2 * d) := by linarith
  have h1mB2_pos : (0 : ℝ) < 1 - β₂ * J * (2 * d) := by linarith
  have hfrac_pos : (0 : ℝ) < β * J * (2 * d) / (1 - β * J * (2 * d)) :=
    div_pos hβJd_pos h1mB_pos
  have hfrac_le : β * J * (2 * d) / (1 - β * J * (2 * d))
      ≤ β₂ * J * (2 * d) / (1 - β₂ * J * (2 * d)) := by
    rw [div_le_div_iff₀ h1mB_pos h1mB2_pos]; nlinarith [hβJd_le]
  have hneglog : -Real.log (β₂ * J * (2 * d) / (1 - β₂ * J * (2 * d)))
      ≤ -Real.log (β * J * (2 * d) / (1 - β * J * (2 * d))) :=
    neg_le_neg (Real.log_le_log hfrac_pos hfrac_le)
  have hSL : -Real.log (β₂ * J * (2 * d)) ≤ -Real.log (β * J * (2 * d)) :=
    neg_le_neg (Real.log_le_log hβJd_pos hβJd_le)
  exact min_le_min (min_le_min (le_refl 1) hneglog)
    (div_le_div_of_nonneg_right hSL (by positivity))

end Ambient
end IsingModel
