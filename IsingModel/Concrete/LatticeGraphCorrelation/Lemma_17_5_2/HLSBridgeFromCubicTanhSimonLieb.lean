import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeFromCubicTanhExpTanh
import IsingModel.Concrete.LatticeGraphCorrelation.SimonLiebDistanceDecay

/-!
# Conditional PseudoMassLatticeDistanceBridge constructor: Simon-Lieb composers

Simon-Lieb direct `bridge.bound` composers (Step 119 plan Steps 5.7j, 5.7k,
5.7l, 5.7m, 5.7n) for the conditional `PseudoMassLatticeDistanceBridge`
constructor: the `dist ≥ 2` small- and large-regime composers, the adjacent
`dist = 1` specialization, the combined per-`w` composers, the uniform
zero-anchored quantifier composers, and the all-pair bound lifts, including the
full adjacent/small/large Simon-Lieb trichotomy.

This is a structural child of `HLSBridgeFromCubicTanh.lean`; see that umbrella
module for the full overview.

**Reference:** Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/

namespace IsingModel
namespace Ambient

open Real

/-! ## Step 119 plan Step 5.7j: Simon-Lieb dist ≥ 2 direct bridge.bound -/

/-- **Simon-Lieb dist ≥ 2 direct `bridge.bound` composer in the
small-`M·d` regime** (Step 119 plan Step 5.7j).

Combines Step 5.7h (PR #3179)'s `correlationInfinite ≤
exp(-(simonLiebRate/2 · dist))` for `dist ≥ 2` with Step 5.7e small-regime
(PR #3176) for `M · d(0,w) ≤ 1`, yielding the per-`w` zero-anchored
`bridge.bound` shape `M · d(0, w) ≤ pseudoMass · r` directly from
Simon-Lieb infrastructure.

Hypotheses:
- `1 ≤ α`, `0 < r` (pseudoMass parameters).
- `0 ≤ β·J`, `0 < β·J·(2d)`, `β·J·(2d) ≤ 1` for the Simon-Lieb exp-form
  bound from Step 5.7g/h.
- `0 ≤ M` and `M ≤ simonLiebRate β J d / 2` for rate-domination.
- `M · d(0, w) ≤ 1` for the small-`t·r` regime of pseudoMassG.
- `2 ≤ latticeDistance d 0 w` to exclude the adjacent `dist = 1` case.
- Active range `correlationInfinite ∈ Ioo 0 2` at `{0, w}`.

The adjacent `dist = 1` and large-`M·d` regimes require separate inputs. -/
theorem pseudoMassFromParamsAtPair_M_dist_zero_le_of_simonLieb_smallReg
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hMrate : M ≤ simonLiebRate β J d / 2)
    {w : Fin d → ℤ} (hdist : 2 ≤ latticeDistance d 0 w)
    (hsmall : M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d)
                (Ambient.cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
              ∈ Set.Ioo (0 : ℝ) 2) :
    M * (latticeDistance d 0 w : ℝ) ≤
      pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 w * r := by
  have h_simonLieb :=
    correlationInfinite_latticeGraph_le_exp_neg_half_simonLiebRate_dist_of_dist_ge_two
      hβJ hβJd_pos hβJd_le hdist (i := 0) (j := w)
  have hdist_nn : (0 : ℝ) ≤ (latticeDistance d 0 w : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have h_exp_upper :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-(M * (latticeDistance d 0 w : ℝ))) := by
    refine h_simonLieb.trans ?_
    apply Real.exp_le_exp.mpr
    have hrate_mul : -(simonLiebRate β J d / 2) * (latticeDistance d 0 w : ℝ) ≤
        -(M * (latticeDistance d 0 w : ℝ)) := by
      have hmono : M ≤ simonLiebRate β J d / 2 := hMrate
      nlinarith [hdist_nn, hmono]
    exact hrate_mul
  exact pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_smallReg
    hα hr d (Ambient.cubicExhaustion d)
    (⟨J, 0, β⟩ : IsingParams ℝ) hM w hsmall hcorr h_exp_upper

/-! ## Step 119 plan Step 5.7j-large: Simon-Lieb large-regime bridge.bound -/

/-- **Polynomial absorption into an exponential rate gap**.

If `1 ≤ t`, then the polynomial factor `t^α` is bounded by `exp(α * t)`.
This is the elementary analytic estimate used to convert a stronger
Simon-Lieb exponential rate into the large-regime
`exp(-(M*d))/(M*d)^α` input expected by `pseudoMassG`. -/
private theorem pow_le_exp_nat_mul_self_of_one_le
    (α : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    t ^ α ≤ Real.exp ((α : ℝ) * t) := by
  have ht_pos : 0 < t := zero_lt_one.trans_le ht
  rw [← Real.exp_log (pow_pos ht_pos α)]
  apply Real.exp_le_exp.mpr
  rw [Real.log_pow]
  have hlog_le_t : Real.log t ≤ t := by
    have hlog_le_sub := Real.log_le_sub_one_of_pos ht_pos
    linarith
  exact mul_le_mul_of_nonneg_left hlog_le_t (by positivity)

/-- **Large-regime Simon-Lieb exponential-to-polynomial input**.

For `dist ≥ 2`, Simon-Lieb gives
`correlation ≤ exp(-(simonLiebRate/2) * dist)`. If `M` is small enough that
`((α:ℝ)+1) * M ≤ simonLiebRate/2`, then on the large regime
`1 ≤ M * dist` the polynomial denominator `(M*dist)^α` is absorbed by the
exponential rate gap, yielding the exact input shape consumed by
`pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_div_pow_largeReg`. -/
theorem correlationInfinite_latticeGraph_le_exp_neg_M_dist_div_pow_of_simonLieb_largeReg
    {α d : ℕ} {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hMrate : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2)
    {w : Fin d → ℤ} (hdist : 2 ≤ latticeDistance d 0 w)
    (hlarge : 1 ≤ M * (latticeDistance d 0 w : ℝ)) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
      ≤ Real.exp (-(M * (latticeDistance d 0 w : ℝ))) /
          (M * (latticeDistance d 0 w : ℝ)) ^ α := by
  let R : ℝ := simonLiebRate β J d / 2
  let D : ℝ := (latticeDistance d 0 w : ℝ)
  let T : ℝ := M * D
  have h_simonLieb :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-(R * D)) := by
    simpa [R, D] using
      correlationInfinite_latticeGraph_le_exp_neg_half_simonLiebRate_dist_of_dist_ge_two
        hβJ hβJd_pos hβJd_le hdist (i := 0) (j := w)
  have hD_nn : 0 ≤ D := by
    dsimp [D]
    exact_mod_cast Nat.zero_le _
  have hT_large : 1 ≤ T := by simpa [T, D] using hlarge
  have hT_pos : 0 < T := zero_lt_one.trans_le hT_large
  have hT_pow_pos : 0 < T ^ α := pow_pos hT_pos α
  have hcoef : (α : ℝ) * M ≤ R - M := by
    change (α : ℝ) * M ≤ simonLiebRate β J d / 2 - M
    linarith
  have hgap_arg : (α : ℝ) * T ≤ (R - M) * D := by
    have hmul := mul_le_mul_of_nonneg_right hcoef hD_nn
    nlinarith [hmul]
  have hpoly_gap : T ^ α ≤ Real.exp ((R - M) * D) :=
    (pow_le_exp_nat_mul_self_of_one_le α hT_large).trans
      (Real.exp_le_exp.mpr hgap_arg)
  have hmul_gap :
      Real.exp (-(R * D)) * T ^ α ≤ Real.exp (-(M * D)) := by
    calc
      Real.exp (-(R * D)) * T ^ α
          ≤ Real.exp (-(R * D)) * Real.exp ((R - M) * D) :=
            mul_le_mul_of_nonneg_left hpoly_gap (Real.exp_nonneg _)
      _ = Real.exp (-(M * D)) := by
            rw [← Real.exp_add]
            congr 1
            ring
  have h_exp_div :
      Real.exp (-(R * D)) ≤ Real.exp (-(M * D)) / T ^ α := by
    exact (le_div_iff₀ hT_pow_pos).mpr hmul_gap
  exact h_simonLieb.trans (by simpa [T, D] using h_exp_div)

/-- **Simon-Lieb dist ≥ 2 direct `bridge.bound` composer in the
large-`M·d` regime**.

This removes the earlier small-regime-only bottleneck for non-adjacent pairs:
when `1 ≤ M · d(0,w)` and `M` is small enough relative to the Simon-Lieb rate,
the polynomial denominator required by the large-regime `pseudoMassG` lower
bound is absorbed by the exponential rate gap. -/
theorem pseudoMassFromParamsAtPair_M_dist_zero_le_of_simonLieb_largeReg
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hMrate : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2)
    {w : Fin d → ℤ} (hdist : 2 ≤ latticeDistance d 0 w)
    (hlarge : 1 ≤ M * (latticeDistance d 0 w : ℝ))
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d)
                (Ambient.cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
              ∈ Set.Ioo (0 : ℝ) 2) :
    M * (latticeDistance d 0 w : ℝ) ≤
      pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 w * r := by
  have h_exp_large :=
    correlationInfinite_latticeGraph_le_exp_neg_M_dist_div_pow_of_simonLieb_largeReg
      (α := α) hβJ hβJd_pos hβJd_le hMrate hdist hlarge
  exact pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_div_pow_largeReg
    hα hr d (Ambient.cubicExhaustion d)
    (⟨J, 0, β⟩ : IsingParams ℝ) w hlarge hcorr h_exp_large

/-! ## Step 119 plan Step 5.7k: adjacent dist = 1 specialization -/

/-- **Adjacent (`dist = 1`) `bridge.bound` composer in the small-`M` regime**
(Step 119 plan Step 5.7k).

Specialization of `pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_smallReg`
(PR #3176) to `latticeDistance d 0 w = 1`. With `M ≤ 1`, the small-regime
constraint `M · d(0, w) ≤ 1` is automatic, and the bound shape collapses to
`M ≤ pseudoMass · r`.

Hypotheses:
- `1 ≤ α`, `0 < r` (pseudoMass parameters).
- `0 ≤ M`, `M ≤ 1`.
- `latticeDistance d 0 w = 1` (adjacent pair).
- Active range `correlationInfinite ∈ Ioo 0 2`.
- Adjacent exp bound `correlationInfinite ≤ exp(-M)`.

Conclusion: `M ≤ pseudoMass · r`. Used to close the adjacent slot of a
full `dist ≥ 1` `hbase` quantifier, complementing Step 5.7j (PR #3181)'s
`dist ≥ 2` Simon-Lieb composer. -/
theorem pseudoMassFromParamsAtPair_zero_le_of_corr_le_exp_adjacent
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {M : ℝ} (hM : 0 ≤ M) (hM_le_one : M ≤ 1)
    {w : Fin d → ℤ} (hdist : latticeDistance d 0 w = 1)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
              ∈ Set.Ioo (0 : ℝ) 2)
    (h_exp_upper :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ≤ Real.exp (-M)) :
    M ≤ pseudoMassFromParamsAtPair hα hr d Λ p 0 w * r := by
  have hdist_cast : (latticeDistance d 0 w : ℝ) = 1 := by
    rw [hdist]; norm_cast
  have hsmall : M * (latticeDistance d 0 w : ℝ) ≤ 1 := by
    rw [hdist_cast, mul_one]; exact hM_le_one
  have h_exp_upper' :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ≤ Real.exp (-(M * (latticeDistance d 0 w : ℝ))) := by
    rw [hdist_cast, mul_one]; exact h_exp_upper
  have h := pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_smallReg
    hα hr d Λ p hM w hsmall hcorr h_exp_upper'
  rw [hdist_cast, mul_one] at h
  exact h

/-! ## Step 119 plan Step 5.7l: combined hbase composer (Simon-Lieb + adjacent) -/

/-- **Combined small-regime `bridge.bound` composer for `dist ≥ 1`**
(Step 119 plan Step 5.7l).

Per-`w` composer dispatching by `latticeDistance d 0 w = 1` (adjacent)
vs `≥ 2`:
- adjacent: Step 5.7k (PR #3182).
- non-adjacent: Step 5.7j (PR #3181, Simon-Lieb direct).

Hypotheses:
- `1 ≤ α`, `0 < r` (pseudoMass parameters).
- `0 ≤ β·J`, `0 < β·J·(2d)`, `β·J·(2d) ≤ 1` for Simon-Lieb.
- `0 ≤ M`, `M ≤ 1`, `M ≤ simonLiebRate β J d / 2` for rate-domination.
- `M · d(0, w) ≤ 1` (small-`t·r` regime).
- Active range `correlation {0, w} ∈ Ioo 0 2`.
- Per-pair `correlation`-upper-bound family:
  - adjacent: `correlation {0, w} ≤ exp(-M)` at `dist = 1`.
  - non-adjacent: implicit via Simon-Lieb #3179 / #3181.

Conclusion: `M · d(0, w) ≤ pseudoMass · r`.

This completes the per-`w` `bridge.bound` API for `dist ≥ 1` in the
small-`M` regime, with Simon-Lieb supplying the non-adjacent exp form
and a separately-provided adjacent input. -/
theorem pseudoMassFromParamsAtPair_M_dist_zero_le_simonLieb_smallReg_combined
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hMrate : M ≤ simonLiebRate β J d / 2)
    {w : Fin d → ℤ} (hw_ne : w ≠ 0)
    (hsmall : M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d)
                (Ambient.cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
              ∈ Set.Ioo (0 : ℝ) 2)
    (h_adj_exp : latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M)) :
    M * (latticeDistance d 0 w : ℝ) ≤
      pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 w * r := by
  have hdist_pos : 0 < latticeDistance d 0 w := by
    apply Nat.pos_of_ne_zero
    intro h_eq_zero
    exact hw_ne ((IsingModel.latticeDistance_eq_zero_iff d 0 w).mp h_eq_zero).symm
  by_cases h_eq_one : latticeDistance d 0 w = 1
  · have h_adj_bound : Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
          ≤ Real.exp (-M) := h_adj_exp h_eq_one
    have hdist_cast : (latticeDistance d 0 w : ℝ) = 1 := by
      rw [h_eq_one]; norm_cast
    have hM_le_one : M ≤ 1 := by
      have := hsmall
      rw [hdist_cast, mul_one] at this
      exact this
    have h := pseudoMassFromParamsAtPair_zero_le_of_corr_le_exp_adjacent
      hα hr d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) hM hM_le_one h_eq_one hcorr h_adj_bound
    rw [hdist_cast, mul_one]
    exact h
  · have h_ge_two : 2 ≤ latticeDistance d 0 w := by omega
    exact pseudoMassFromParamsAtPair_M_dist_zero_le_of_simonLieb_smallReg
      hα hr d hβJ hβJd_pos hβJd_le hM hMrate h_ge_two hsmall hcorr

/-! ## Step 119 plan Step 5.7m: ∀ w ≠ 0 hbase quantifier composer -/

/-- **`hbase` quantifier composer from Step 5.7l per-`w` composer**
(Step 119 plan Step 5.7m).

Lifts `pseudoMassFromParamsAtPair_M_dist_zero_le_simonLieb_smallReg_combined`
(Step 5.7l, PR #3183) to the universally-quantified
`∀ w ≠ 0, M · d(0, w) ≤ pseudoMass · r` shape, the zero-anchored input
required by `pseudoMassFromParamsAtPair_lower_bound_of_zero_anchored`
(existing).

Hypotheses (per `w ≠ 0` and uniform):
- `1 ≤ α`, `0 < r` (pseudoMass parameters).
- `0 ≤ β·J`, `0 < β·J·(2d) ≤ 1` for Simon-Lieb.
- `0 ≤ M`, `M ≤ simonLiebRate β J d / 2` for rate-domination.
- `h_corr_active`: per-`w ≠ 0` active range.
- `h_corr_small`: per-`w ≠ 0`, `M · d(0, w) ≤ 1` (small-`t·r` regime).
  Restrictive — for arbitrary `w` forces `M = 0` unless bounded support.
- `h_adj_exp`: per-`w` with `dist(0, w) = 1`, `correlation ≤ exp(-M)`.

Conclusion: `∀ w ≠ 0, M · d(0, w) ≤ pseudoMass · r`. Suitable input for
`pseudoMassFromParamsAtPair_lower_bound_of_zero_anchored` lifting to all
distinct pairs. -/
theorem pseudoMassFromParamsAtPair_zero_anchored_simonLieb_smallReg_uniform
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hMrate : M ≤ simonLiebRate β J d / 2)
    (h_corr_active : ∀ w : Fin d → ℤ, w ≠ 0 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ∈ Set.Ioo (0 : ℝ) 2)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M)) :
    ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) 0 w * r := by
  intro w hw_ne
  exact pseudoMassFromParamsAtPair_M_dist_zero_le_simonLieb_smallReg_combined
    hα hr d hβJ hβJd_pos hβJd_le hM hMrate hw_ne
    (h_corr_small w hw_ne) (h_corr_active w hw_ne)
    (h_adj_exp w)

/-! ## Step 119 plan Step 5.7n: all-pair bound lift from Step 5.7m -/

/-- **All-pair `bridge.bound` from Step 5.7m via the translation lift**
(Step 119 plan Step 5.7n).

Composes Step 5.7m (`...zero_anchored_simonLieb_smallReg_uniform`, PR #3184)
with the existing `pseudoMassFromParamsAtPair_lower_bound_of_zero_anchored`
to produce the all-pair shape
`∀ x z, x ≠ z → M · d(x, z) ≤ pseudoMass · r`, matching the `bound` field
signature of `PseudoMassLatticeDistanceBridge`.

Hypotheses (uniform per `w ≠ 0`; only `bound` is lifted to all pairs here —
active range remains the zero-anchored input consumed by Step 5.7m):
- `1 ≤ α`, `0 < r`, `0 ≤ J`, `0 < β` (pseudoMass / ferromagnetic).
- `0 < β·J·(2d) ≤ 1` for Simon-Lieb.
- `0 ≤ M`, `M ≤ simonLiebRate β J d / 2` for rate-domination.
- `h_corr_active`: per-`w ≠ 0` active range at `{0, w}`.
- `h_corr_small`: per-`w ≠ 0`, `M · d(0, w) ≤ 1`.
- `h_adj_exp`: per-`w` with `dist(0, w) = 1`, `correlation ≤ exp(-M)`.

This is the final structural step in the Step 5.7 plumbing chain. -/
theorem pseudoMassFromParamsAtPair_all_pair_simonLieb_smallReg_bound
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hMrate : M ≤ simonLiebRate β J d / 2)
    (h_corr_active : ∀ w : Fin d → ℤ, w ≠ 0 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ∈ Set.Ioo (0 : ℝ) 2)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M)) :
    ∀ x z : Fin d → ℤ, x ≠ z →
      M * (latticeDistance d x z : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z * r := by
  have hβJ : 0 ≤ β * J := mul_nonneg hβ.le hJ
  have h_zero_anchored :=
    pseudoMassFromParamsAtPair_zero_anchored_simonLieb_smallReg_uniform
      hα hr d hβJ hβJd_pos hβJd_le hM hMrate
      h_corr_active h_corr_small h_adj_exp
  exact pseudoMassFromParamsAtPair_lower_bound_of_zero_anchored
    hα hr d hJ hβ h_zero_anchored

/-! ## Step 119 plan Step 5.7j-large: full Simon-Lieb trichotomy composer -/

/-- **Combined Simon-Lieb `bridge.bound` composer by adjacent/small/large cases**.

For a single nonzero anchored displacement `w`, this removes the impossible
uniform small-regime assumption by splitting into:

- `dist(0,w) = 1`: use the adjacent input;
- `2 ≤ dist(0,w)` and `M * dist(0,w) ≤ 1`: use the Simon-Lieb small-regime
  composer;
- `2 ≤ dist(0,w)` and `1 ≤ M * dist(0,w)`: use the Simon-Lieb large-regime
  rate-gap composer.

The rate condition `((α:ℝ)+1) * M ≤ simonLiebRate β J d / 2` is stronger than
the small-regime domination `M ≤ simonLiebRate β J d / 2`, so it feeds both
non-adjacent branches. -/
theorem pseudoMassFromParamsAtPair_M_dist_zero_le_simonLieb_trichotomy_combined
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M) (hM_le_one : M ≤ 1)
    (hMrate : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2)
    {w : Fin d → ℤ} (hw_ne : w ≠ 0)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d)
                (Ambient.cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
              ∈ Set.Ioo (0 : ℝ) 2)
    (h_adj_exp : latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M)) :
    M * (latticeDistance d 0 w : ℝ) ≤
      pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 w * r := by
  have hMrate_small : M ≤ simonLiebRate β J d / 2 := by
    have hfactor : (1 : ℝ) ≤ (α : ℝ) + 1 := by
      exact le_add_of_nonneg_left (Nat.cast_nonneg α)
    have hM_le_scaled : M ≤ ((α : ℝ) + 1) * M := by
      nlinarith [hfactor, hM_pos.le]
    exact hM_le_scaled.trans hMrate
  have hdist_pos : 0 < latticeDistance d 0 w := by
    apply Nat.pos_of_ne_zero
    intro h_eq_zero
    exact hw_ne ((IsingModel.latticeDistance_eq_zero_iff d 0 w).mp h_eq_zero).symm
  by_cases h_eq_one : latticeDistance d 0 w = 1
  · have hdist_cast : (latticeDistance d 0 w : ℝ) = 1 := by
      rw [h_eq_one]; norm_cast
    have h := pseudoMassFromParamsAtPair_zero_le_of_corr_le_exp_adjacent
      hα hr d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) hM_pos.le hM_le_one h_eq_one hcorr
      (h_adj_exp h_eq_one)
    rw [hdist_cast, mul_one]
    exact h
  · have h_ge_two : 2 ≤ latticeDistance d 0 w := by omega
    by_cases hsmall : M * (latticeDistance d 0 w : ℝ) ≤ 1
    · exact pseudoMassFromParamsAtPair_M_dist_zero_le_of_simonLieb_smallReg
        hα hr d hβJ hβJd_pos hβJd_le hM_pos.le hMrate_small
        h_ge_two hsmall hcorr
    · have hlarge : 1 ≤ M * (latticeDistance d 0 w : ℝ) :=
        (lt_of_not_ge hsmall).le
      exact pseudoMassFromParamsAtPair_M_dist_zero_le_of_simonLieb_largeReg
        hα hr d hβJ hβJd_pos hβJd_le hMrate h_ge_two hlarge hcorr

/-- **Uniform zero-anchored bound from the full Simon-Lieb trichotomy**.

This is the replacement for
`pseudoMassFromParamsAtPair_zero_anchored_simonLieb_smallReg_uniform` when
`M > 0`: it no longer assumes `∀ w ≠ 0, M * dist(0,w) ≤ 1`. -/
theorem pseudoMassFromParamsAtPair_zero_anchored_simonLieb_trichotomy_uniform
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M) (hM_le_one : M ≤ 1)
    (hMrate : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2)
    (h_corr_active : ∀ w : Fin d → ℤ, w ≠ 0 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ∈ Set.Ioo (0 : ℝ) 2)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M)) :
    ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) 0 w * r := by
  intro w hw_ne
  exact pseudoMassFromParamsAtPair_M_dist_zero_le_simonLieb_trichotomy_combined
    hα hr d hβJ hβJd_pos hβJd_le hM_pos hM_le_one hMrate hw_ne
    (h_corr_active w hw_ne) (h_adj_exp w)

/-- **All-pair bound from the full Simon-Lieb trichotomy**.

Composes the uniform zero-anchored trichotomy with the translation lift
`pseudoMassFromParamsAtPair_lower_bound_of_zero_anchored`, producing the
`PseudoMassLatticeDistanceBridge.bound` field without the globally impossible
small-regime hypothesis. -/
theorem pseudoMassFromParamsAtPair_all_pair_simonLieb_trichotomy_bound
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M) (hM_le_one : M ≤ 1)
    (hMrate : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2)
    (h_corr_active : ∀ w : Fin d → ℤ, w ≠ 0 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ∈ Set.Ioo (0 : ℝ) 2)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M)) :
    ∀ x z : Fin d → ℤ, x ≠ z →
      M * (latticeDistance d x z : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z * r := by
  have hβJ : 0 ≤ β * J := mul_nonneg hβ.le hJ
  have h_zero_anchored :=
    pseudoMassFromParamsAtPair_zero_anchored_simonLieb_trichotomy_uniform
      hα hr d hβJ hβJd_pos hβJd_le hM_pos hM_le_one hMrate
      h_corr_active h_adj_exp
  exact pseudoMassFromParamsAtPair_lower_bound_of_zero_anchored
    hα hr d hJ hβ h_zero_anchored

end Ambient
end IsingModel
