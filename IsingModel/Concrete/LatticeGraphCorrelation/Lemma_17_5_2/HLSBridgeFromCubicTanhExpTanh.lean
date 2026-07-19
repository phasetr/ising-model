import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeFromCubicTanhCore
import IsingModel.Conditioning.CorrelationRates.ExpRate

/-!
# Conditional PseudoMassLatticeDistanceBridge constructor: exp / tanh composers

`exp` / `tanh` correlation-upper-bound composers (Step 119 plan Steps 5.7e,
5.7f, 5.7i) for the conditional `PseudoMassLatticeDistanceBridge` constructor:
the small/large-regime `bridge.bound` composers from `exp` and `tanh` inputs,
the `hbase` quantifier composers via the small/large trichotomy, and the
asymmetric tanh/exp combined composer.

This is a structural child of `HLSBridgeFromCubicTanh.lean`; see that umbrella
module for the full overview.

**Reference:** Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/

namespace IsingModel
namespace Ambient

open Real

/-! ## Step 119 plan Step 5.7e: `exp / tanh` correlation-upper-bound composers -/

/-- **`bridge.bound` from an `exp(-(M·d(0,w)))` correlation upper bound, small
regime** (Step 119 plan Step 5.7e small-`t·r`).

Given the active range and the analytic input
`correlation {0, w} ≤ exp(-(M · d(0, w)))` together with the small-`t·r`
constraint `M · d(0, w) ≤ 1` and `α ≥ 1`, conclude the zero-anchored
`bridge.bound` shape `M · d(0, w) ≤ pseudoMassFromParamsAtPair 0 w · r`.

Proof chain:
1. `pseudoMassG_ge_exp_of_tr_le_one` (small-`t·r`, with `t := M · d(0,w) / r`,
   `t · r = M · d(0,w) ≤ 1`) yields
   `exp(-(M · d(0,w))) ≤ pseudoMassG α r (M · d(0,w) / r)`.
2. Transitivity with the input gives
   `correlation ≤ pseudoMassG α r (M · d(0,w) / r)`.
3. `pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_pseudoMassG` (#3173)
   produces the bridge-shape conclusion. -/
theorem pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_smallReg
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {M : ℝ} (hM : 0 ≤ M) (w : Fin d → ℤ)
    (hsmall : M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
              ∈ Set.Ioo (0 : ℝ) 2)
    (h_exp_upper :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ≤ Real.exp (-(M * (latticeDistance d 0 w : ℝ)))) :
    M * (latticeDistance d 0 w : ℝ) ≤
      pseudoMassFromParamsAtPair hα hr d Λ p 0 w * r := by
  set t : ℝ := M * (latticeDistance d 0 w : ℝ) / r with ht_def
  have hdist_nn : (0 : ℝ) ≤ (latticeDistance d 0 w : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have ht_nn : 0 ≤ t := by
    apply div_nonneg
    · exact mul_nonneg hM hdist_nn
    · exact hr.le
  have htr_eq : t * r = M * (latticeDistance d 0 w : ℝ) := by
    rw [ht_def, div_mul_cancel₀ _ (ne_of_gt hr)]
  have htr_le_one : t * r ≤ 1 := by rw [htr_eq]; exact hsmall
  have hpm_ge_exp : Real.exp (-(t * r)) ≤ pseudoMassG α r t :=
    pseudoMassG_ge_exp_of_tr_le_one hα ht_nn hr htr_le_one
  have hcorr_le_pm : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
      ≤ pseudoMassG α r t := by
    have heq : Real.exp (-(t * r)) = Real.exp (-(M * (latticeDistance d 0 w : ℝ))) := by
      rw [htr_eq]
    rw [← heq] at h_exp_upper
    exact h_exp_upper.trans hpm_ge_exp
  exact pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_pseudoMassG
    hα hr d Λ p hM w hcorr hcorr_le_pm

/-- **`bridge.bound` from an `exp(-(M·d(0,w))) / (M·d(0,w))^α` correlation
upper bound, large regime** (Step 119 plan Step 5.7e large-`t·r`).

Given the active range and the analytic input
`correlation {0, w} ≤ exp(-(M · d(0, w))) / (M · d(0, w))^α` together with the
large-`t·r` constraint `1 ≤ M · d(0, w)` and `α ≥ 1`, conclude the zero-anchored
`bridge.bound` shape `M · d(0, w) ≤ pseudoMassFromParamsAtPair 0 w · r`.

Proof chain:
1. `pseudoMassG_ge_exp_div_pow_of_tr_ge_one` (large-`t·r`, with
   `t := M · d(0,w) / r`, `t · r = M · d(0,w) ≥ 1`) yields
   `exp(-(M · d(0,w))) / (M · d(0,w))^α ≤ pseudoMassG α r (M · d(0,w) / r)`.
2. Transitivity with the input gives
   `correlation ≤ pseudoMassG α r (M · d(0,w) / r)`.
3. `pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_pseudoMassG` (#3173)
   produces the bridge-shape conclusion. -/
theorem pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_div_pow_largeReg
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {M : ℝ} (w : Fin d → ℤ)
    (hlarge : 1 ≤ M * (latticeDistance d 0 w : ℝ))
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
              ∈ Set.Ioo (0 : ℝ) 2)
    (h_exp_upper :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ≤ Real.exp (-(M * (latticeDistance d 0 w : ℝ))) /
            (M * (latticeDistance d 0 w : ℝ)) ^ α) :
    M * (latticeDistance d 0 w : ℝ) ≤
      pseudoMassFromParamsAtPair hα hr d Λ p 0 w * r := by
  have hdist_nn : (0 : ℝ) ≤ (latticeDistance d 0 w : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have hMd_nn : 0 ≤ M * (latticeDistance d 0 w : ℝ) := le_trans zero_le_one hlarge
  have hM : 0 ≤ M := by
    by_contra hMneg
    push Not at hMneg
    have : M * (latticeDistance d 0 w : ℝ) ≤ 0 :=
      mul_nonpos_iff.mpr (Or.inr ⟨hMneg.le, hdist_nn⟩)
    linarith
  set t : ℝ := M * (latticeDistance d 0 w : ℝ) / r with ht_def
  have ht_nn : 0 ≤ t := div_nonneg hMd_nn hr.le
  have htr_eq : t * r = M * (latticeDistance d 0 w : ℝ) := by
    rw [ht_def, div_mul_cancel₀ _ (ne_of_gt hr)]
  have htr_ge_one : 1 ≤ t * r := by rw [htr_eq]; exact hlarge
  have hpm_ge_exp_div_pow :
      Real.exp (-(t * r)) / (t * r) ^ α ≤ pseudoMassG α r t :=
    pseudoMassG_ge_exp_div_pow_of_tr_ge_one α htr_ge_one
  have hcorr_le_pm : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
      ≤ pseudoMassG α r t := by
    have heq : Real.exp (-(t * r)) / (t * r) ^ α =
        Real.exp (-(M * (latticeDistance d 0 w : ℝ))) /
          (M * (latticeDistance d 0 w : ℝ)) ^ α := by
      rw [htr_eq]
    rw [← heq] at h_exp_upper
    exact h_exp_upper.trans hpm_ge_exp_div_pow
  exact pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_pseudoMassG
    hα hr d Λ p hM w hcorr hcorr_le_pm

/-- **`bridge.bound` from a `tanh(βJ)^d(0,w)` correlation upper bound, small
regime** (Step 119 plan Step 5.7e tanh-input small-`t·r`).

Given:

- `0 ≤ β·J` (ferromagnetic phase / nonneg coupling);
- `M ≤ highTempExpRate β J = -log(tanh(β·J))`;
- `0 ≤ M` and the small-distance constraint `M · d(0,w) ≤ 1`;
- the active range for the correlation;
- the cubic-path tanh-decay upper bound
  `correlation {0, w} ≤ tanh(β·J)^(latticeDistance d 0 w)`,

conclude the zero-anchored `bridge.bound` shape
`M · d(0, w) ≤ pseudoMassFromParamsAtPair 0 w · r`.

Proof chain:
1. Step 5.7d `tanh_pow_le_exp_neg_M_dist_r_of_M_r_le_highTempExpRate`
   with `r := 1` yields `tanh(β·J)^k ≤ exp(-(M · k))` for every `k : ℕ`
   (using `M · 1 = M ≤ highTempExpRate β J`).
2. Transitivity gives `correlation ≤ exp(-(M · d(0,w)))`.
3. The small-regime composer
   `pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_smallReg`
   produces the bridge-shape conclusion. -/
theorem pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_tanh_pow_smallReg
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {β J : ℝ} (hβJ : 0 ≤ β * J)
    {M : ℝ} (hM : 0 ≤ M) (hMrate : M ≤ highTempExpRate β J)
    (w : Fin d → ℤ)
    (hsmall : M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
              ∈ Set.Ioo (0 : ℝ) 2)
    (h_tanh_upper :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ≤ Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 w) :
    M * (latticeDistance d 0 w : ℝ) ≤
      pseudoMassFromParamsAtPair hα hr d Λ p 0 w * r := by
  have hMrate_one : M * (1 : ℝ) ≤ highTempExpRate β J := by
    rw [mul_one]; exact hMrate
  have h_tanh_le_exp :
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 w ≤
        Real.exp (-(M * (IsingModel.latticeDistance d 0 w : ℝ) * 1)) :=
    tanh_pow_le_exp_neg_M_dist_r_of_M_r_le_highTempExpRate hβJ hMrate_one _
  have h_exp_upper :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ≤ Real.exp (-(M * (IsingModel.latticeDistance d 0 w : ℝ))) := by
    have h := h_tanh_upper.trans h_tanh_le_exp
    have heq : Real.exp (-(M * (IsingModel.latticeDistance d 0 w : ℝ) * 1)) =
        Real.exp (-(M * (IsingModel.latticeDistance d 0 w : ℝ))) := by
      rw [mul_one]
    rw [heq] at h
    exact h
  exact pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_smallReg
    hα hr d Λ p hM w hsmall hcorr h_exp_upper

/-! ## Step 119 plan Step 5.7f: `hbase` quantifier composers -/

/-- **`hbase` quantifier composer via small/large trichotomy on `M · d(0, w)`**
(Step 119 plan Step 5.7f).

Given `0 ≤ M` and per-nonzero-`w` analytic-input families for both regimes of
`M · d(0, w)`, the trichotomy dispatches each `w ≠ 0` to either the
small-regime composer
`pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_smallReg` or the
large-regime composer
`pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_div_pow_largeReg`,
producing the universally-quantified shape required by the `hbase` field of
`PseudoMassLatticeDistanceBridge_of_cubicTanh_family` (#3172).

The two analytic-input families:
- `h_corr_small`: for each `w ≠ 0` with `M · d(0, w) ≤ 1`,
  `correlation {0, w} ≤ exp(-(M · d(0, w)))`.
- `h_corr_large`: for each `w ≠ 0` with `1 ≤ M · d(0, w)`,
  `correlation {0, w} ≤ exp(-(M · d(0, w))) / (M · d(0, w))^α`.

The trichotomy is by `le_or_lt (M · d(0, w)) 1`: if `≤ 1`, apply the
small-regime composer; otherwise `1 < M · d(0, w)` ⇒ `1 ≤ M · d(0, w)`, apply
the large-regime composer. -/
theorem pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_trichotomy
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {M : ℝ} (hM : 0 ≤ M)
    (h_corr_active : ∀ w : Fin d → ℤ, w ≠ 0 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ∈ Set.Ioo (0 : ℝ) 2)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ≤ Real.exp (-(M * (latticeDistance d 0 w : ℝ))))
    (h_corr_large : ∀ w : Fin d → ℤ, w ≠ 0 →
      1 ≤ M * (latticeDistance d 0 w : ℝ) →
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ≤ Real.exp (-(M * (latticeDistance d 0 w : ℝ))) /
            (M * (latticeDistance d 0 w : ℝ)) ^ α) :
    ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d Λ p 0 w * r := by
  intro w hw_ne
  by_cases hsmall : M * (latticeDistance d 0 w : ℝ) ≤ 1
  · exact pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_smallReg
      hα hr d Λ p hM w hsmall (h_corr_active w hw_ne)
      (h_corr_small w hw_ne hsmall)
  · push Not at hsmall
    have hlarge_le : 1 ≤ M * (latticeDistance d 0 w : ℝ) := hsmall.le
    exact pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_div_pow_largeReg
      hα hr d Λ p w hlarge_le (h_corr_active w hw_ne)
      (h_corr_large w hw_ne hlarge_le)

/-- **`hbase` quantifier composer from a uniform `exp(-(M·d))/max(1, M·d)^α`
correlation upper bound** (Step 119 plan Step 5.7f, unified-input variant).

Convenience wrapper for
`pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_trichotomy` taking a
single uniform correlation upper bound in the unified form
`correlation {0, w} ≤ exp(-(M · d(0, w))) / max 1 (M · d(0, w))^α`,
which is automatically both:
- ≤ `exp(-(M · d(0, w)))` in the small regime (where `max 1 (M·d) = 1`,
  hence the denominator is 1);
- ≤ `exp(-(M · d(0, w))) / (M · d(0, w))^α` in the large regime (where
  `max 1 (M·d) = M·d`).

Useful when the caller has a single uniform-shape bound, e.g., a Simon-Lieb
exponential decay augmented with polynomial correction. -/
theorem pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_div_max_pow
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {M : ℝ} (hM : 0 ≤ M)
    (h_corr_active : ∀ w : Fin d → ℤ, w ≠ 0 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ∈ Set.Ioo (0 : ℝ) 2)
    (h_corr_upper : ∀ w : Fin d → ℤ, w ≠ 0 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ≤ Real.exp (-(M * (latticeDistance d 0 w : ℝ))) /
            max 1 (M * (latticeDistance d 0 w : ℝ)) ^ α) :
    ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d Λ p 0 w * r := by
  apply pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_trichotomy
    hα hr d Λ p hM h_corr_active
  · intro w hw_ne hsmall
    have hbound := h_corr_upper w hw_ne
    have hmax_eq : max (1 : ℝ) (M * (latticeDistance d 0 w : ℝ)) = 1 :=
      max_eq_left hsmall
    rw [hmax_eq, one_pow, div_one] at hbound
    exact hbound
  · intro w hw_ne hlarge
    have hbound := h_corr_upper w hw_ne
    have hmax_eq : max (1 : ℝ) (M * (latticeDistance d 0 w : ℝ)) =
        M * (latticeDistance d 0 w : ℝ) :=
      max_eq_right hlarge
    rw [hmax_eq] at hbound
    exact hbound

/-! ## Step 119 plan Step 5.7i: tanh + exp/pow combined hbase composer -/

/-- **`hbase` quantifier composer with asymmetric tanh / exp inputs**
(Step 119 plan Step 5.7i).

Takes the small-regime analytic input in `tanh(β·J)^d(0,w)` form (the natural
output of cubic-path tanh decay infrastructure) and the large-regime input
in `exp(-(M·d))/(M·d)^α` form, dispatching by case-split on
`M · d(0,w) ≤ 1`.

In the small regime, applies Step 5.7e tanh-input variant
`pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_tanh_pow_smallReg`
(PR #3176), which internally uses Step 5.7d (PR #3175) to convert tanh form
to exp form. In the large regime, applies Step 5.7e large-input variant
`pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_div_pow_largeReg`
directly.

This asymmetric composer matches the natural shape of analytic inputs
arising from GJ §17.5 derivations: tanh-typed small-regime cubic-path
estimates combined with exp/polynomial-typed large-regime decay. -/
theorem pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_tanh_exp_trichotomy
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {β J : ℝ} (hβJ : 0 ≤ β * J)
    {M : ℝ} (hM : 0 ≤ M) (hMrate : M ≤ highTempExpRate β J)
    (h_corr_active : ∀ w : Fin d → ℤ, w ≠ 0 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ∈ Set.Ioo (0 : ℝ) 2)
    (h_corr_tanh_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ≤ Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 w)
    (h_corr_exp_large : ∀ w : Fin d → ℤ, w ≠ 0 →
      1 ≤ M * (latticeDistance d 0 w : ℝ) →
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ≤ Real.exp (-(M * (latticeDistance d 0 w : ℝ))) /
            (M * (latticeDistance d 0 w : ℝ)) ^ α) :
    ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d Λ p 0 w * r := by
  intro w hw_ne
  by_cases hsmall : M * (latticeDistance d 0 w : ℝ) ≤ 1
  · exact pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_tanh_pow_smallReg
      hα hr d Λ p hβJ hM hMrate w hsmall (h_corr_active w hw_ne)
      (h_corr_tanh_small w hw_ne hsmall)
  · push Not at hsmall
    have hlarge_le : 1 ≤ M * (latticeDistance d 0 w : ℝ) := hsmall.le
    exact pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_div_pow_largeReg
      hα hr d Λ p w hlarge_le (h_corr_active w hw_ne)
      (h_corr_exp_large w hw_ne hlarge_le)

end Ambient
end IsingModel
