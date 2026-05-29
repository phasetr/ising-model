import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CEConditionalCapstone
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CEConditionalCapstoneTrivialQ

/-!
# Geometric-form CE-route bundle convenience constructors

Split from `CEConditionalCapstone.lean` (Issue #3054, refactor PR #3130 per
codex strategic review). This file contains the geometric-form convenience
constructors built on top of the base `CERouteIccGeometricIncrement` bundle
and its `_of_canonical_radius_circle` auto-radius variant (which remain in
`CEConditionalCapstone.lean`):

* `sphere_circle_bound_of_real_inc_and_lipschitz` — triangle-inequality
  bridge from real-axis increment + per-stage Lipschitz to sphere bound.
* `CERouteIccGeometricIncrement_of_canonical_radius_R_inc_lipschitz` and
  `_R_inc_uniform_C` — R_inc + Lipschitz parametric forms.
* `CERouteIccGeometricIncrement_of_canonical_radius_sequence` and
  `_canonical_radius_geometric` — sequence-form and geometric-form parametric
  specialisations.
* `lemma_17_5_2_{upper_bound,sandwich}_of_R_inc_lipschitz`,
  `_R_inc_uniform_C`, `_sequence`, `_geometric` — corresponding one-step
  Lemma 17.5.2 wrappers.

The poly-geometric counterparts live in `CEConditionalCapstonePolyGeometric.lean`.
The `_and_pseudoMass_le_rate` fully-concrete capstones for both forms live in
`CEConditionalCapstonePseudoMassLeRate.lean`.

References:

* Glimm-Jaffe, *Quantum Physics* (2nd ed.), §17.5, Lemma 17.5.2, pp. 311-312.
* Issue #3054 (CE-route bundle framework).
-/

namespace IsingModel
namespace Ambient

open Complex Metric


/-- **Sphere circle bound via direct triangle inequality with per-stage
Lipschitz and real-axis values** (Issue #3054). For each `w` on
`Metric.sphere ((β₀:ℝ):ℂ) r`, the cross-stage value increment satisfies:
`‖corr_ℂ G_k(w) - corr_ℂ G_{k+1}(w)‖ ≤ R_inc + (C_k + C_k1) · r`.

Proof: direct triangle inequality
`‖a - d‖ ≤ ‖a - b‖ + ‖b - c‖ + ‖c - d‖`
where `a := corr_ℂ G_k(w)`, `b := corr_ℂ G_k(w.re)`,
`c := corr_ℂ G_{k+1}(w.re)`, `d := corr_ℂ G_{k+1}(w)`. Per-stage Lipschitz
hypotheses bound `‖a - b‖` and `‖c - d‖`; the real-axis identity
`corr_ℂ G((w.re:ℝ):ℂ) = (correlation G ⟨J,0,w.re⟩ : ℂ)` makes `b - c` a cast
of a real difference, with `‖b - c‖` equal to the absolute value of the real
increment; sphere geometry gives `‖w - w.re‖ ≤ r`. Bypasses vertex-type
incompatibility that prevents direct use of
`correlationComplex_diff_norm_le_real_diff_plus_lipschitz` (#3050). -/
theorem sphere_circle_bound_of_real_inc_and_lipschitz
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (k : ℕ)
    (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k)
    (β₀ r R_inc C_k C_k1 : ℝ)
    (h_real_inc : ∀ β_re : ℝ, β_re ∈ Set.Icc (β₀ - r) (β₀ + r) →
      |correlation
            (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
            (⟨J, 0, β_re⟩ : IsingParams ℝ)
            (Ambient.liftFinset {x, z} hk) -
          correlation
            (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
            (⟨J, 0, β_re⟩ : IsingParams ℝ)
            (Ambient.liftFinset {x, z}
              (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc)
    (h_lip_k : ∀ β ∈ Metric.sphere ((β₀ : ℝ) : ℂ) r,
      ‖correlationComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
            (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 β -
          correlationComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
            (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((β.re : ℝ) : ℂ)‖
        ≤ C_k * ‖β - ((β.re : ℝ) : ℂ)‖)
    (h_lip_k1 : ∀ β ∈ Metric.sphere ((β₀ : ℝ) : ℂ) r,
      ‖correlationComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
            (Ambient.liftFinset {x, z}
              (hk.trans (Λ.mono (Nat.le_succ k)))) (J : ℂ) 0 β -
          correlationComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
            (Ambient.liftFinset {x, z}
              (hk.trans (Λ.mono (Nat.le_succ k)))) (J : ℂ) 0 ((β.re : ℝ) : ℂ)‖
        ≤ C_k1 * ‖β - ((β.re : ℝ) : ℂ)‖)
    (hC_k_nn : 0 ≤ C_k) (hC_k1_nn : 0 ≤ C_k1) :
    ∀ w ∈ Metric.sphere ((β₀ : ℝ) : ℂ) r,
      ‖correlationComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
            (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 w -
          correlationComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
            (Ambient.liftFinset {x, z}
              (hk.trans (Λ.mono (Nat.le_succ k))))
            (J : ℂ) 0 w‖ ≤ R_inc + (C_k + C_k1) * r := by
  intro w hw
  have hb_aux := IsingModel.correlation_ofReal_eq_correlationComplex
    (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
    (⟨J, 0, w.re⟩ : IsingParams ℝ) (Ambient.liftFinset {x, z} hk)
  simp only [Complex.ofReal_zero] at hb_aux
  have hb_real : correlationComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((w.re : ℝ) : ℂ) =
      ((correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
        (⟨J, 0, w.re⟩ : IsingParams ℝ)
        (Ambient.liftFinset {x, z} hk) : ℝ) : ℂ) := hb_aux.symm
  have hc_aux := IsingModel.correlation_ofReal_eq_correlationComplex
    (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
    (⟨J, 0, w.re⟩ : IsingParams ℝ)
    (Ambient.liftFinset {x, z} (hk.trans (Λ.mono (Nat.le_succ k))))
  simp only [Complex.ofReal_zero] at hc_aux
  have hc_real : correlationComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
      (Ambient.liftFinset {x, z}
        (hk.trans (Λ.mono (Nat.le_succ k)))) (J : ℂ) 0 ((w.re : ℝ) : ℂ) =
      ((correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
        (⟨J, 0, w.re⟩ : IsingParams ℝ)
        (Ambient.liftFinset {x, z}
          (hk.trans (Λ.mono (Nat.le_succ k)))) : ℝ) : ℂ) := hc_aux.symm
  rw [Metric.mem_sphere] at hw
  have h_w_β₀_norm_eq : ‖w - ((β₀ : ℝ) : ℂ)‖ = r := by
    rw [← Complex.dist_eq]; exact hw
  have h_w_wre_norm_le_r : ‖w - ((w.re : ℝ) : ℂ)‖ ≤ r := by
    have h_im_abs : |w.im| ≤ ‖w - ((β₀ : ℝ) : ℂ)‖ := by
      have h_sub_im : (w - ((β₀ : ℝ) : ℂ)).im = w.im := by simp
      have := Complex.abs_im_le_norm (w - ((β₀ : ℝ) : ℂ))
      rw [h_sub_im] at this; exact this
    have h_im_abs_eq : ‖w - ((w.re : ℝ) : ℂ)‖ = |w.im| := by
      have h_sub_w_wre : w - ((w.re : ℝ) : ℂ) = w.im • Complex.I :=
        Complex.ext (by simp) (by simp)
      rw [h_sub_w_wre]; simp
    linarith [h_im_abs_eq, h_im_abs, h_w_β₀_norm_eq]
  have h_re_abs : |w.re - β₀| ≤ r := by
    have h_re_sub : (w - ((β₀ : ℝ) : ℂ)).re = w.re - β₀ := by simp
    have := Complex.abs_re_le_norm (w - ((β₀ : ℝ) : ℂ))
    rw [h_re_sub] at this; linarith
  have h_real_mem : w.re ∈ Set.Icc (β₀ - r) (β₀ + r) := by
    refine ⟨?_, ?_⟩
    · linarith [abs_le.mp h_re_abs |>.1]
    · linarith [abs_le.mp h_re_abs |>.2]
  have h_ab := h_lip_k w hw
  have h_dc_norm := h_lip_k1 w hw
  have h_cd : ‖correlationComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
        (Ambient.liftFinset {x, z} (hk.trans (Λ.mono (Nat.le_succ k))))
        (J : ℂ) 0 ((w.re : ℝ) : ℂ) -
      correlationComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
        (Ambient.liftFinset {x, z} (hk.trans (Λ.mono (Nat.le_succ k))))
        (J : ℂ) 0 w‖ ≤ C_k1 * ‖w - ((w.re : ℝ) : ℂ)‖ := by
    have h_neg : (correlationComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
        (Ambient.liftFinset {x, z} (hk.trans (Λ.mono (Nat.le_succ k))))
        (J : ℂ) 0 ((w.re : ℝ) : ℂ) -
      correlationComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
        (Ambient.liftFinset {x, z} (hk.trans (Λ.mono (Nat.le_succ k))))
        (J : ℂ) 0 w) = -(correlationComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
        (Ambient.liftFinset {x, z} (hk.trans (Λ.mono (Nat.le_succ k))))
        (J : ℂ) 0 w -
      correlationComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
        (Ambient.liftFinset {x, z} (hk.trans (Λ.mono (Nat.le_succ k))))
        (J : ℂ) 0 ((w.re : ℝ) : ℂ)) := by ring
    rw [h_neg, norm_neg]
    exact h_dc_norm
  have h_real_bound := h_real_inc w.re h_real_mem
  set a := correlationComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 w
  set b := correlationComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((w.re : ℝ) : ℂ)
  set c := correlationComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
      (Ambient.liftFinset {x, z} (hk.trans (Λ.mono (Nat.le_succ k))))
      (J : ℂ) 0 ((w.re : ℝ) : ℂ)
  set d_ := correlationComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
      (Ambient.liftFinset {x, z} (hk.trans (Λ.mono (Nat.le_succ k))))
      (J : ℂ) 0 w
  have h_tri : ‖a - d_‖ ≤ ‖a - b‖ + ‖b - c‖ + ‖c - d_‖ := by
    have h_decomp : a - d_ = (a - b) + ((b - c) + (c - d_)) := by ring
    rw [h_decomp]
    have h1 := norm_add_le (a - b) ((b - c) + (c - d_))
    have h2 := norm_add_le (b - c) (c - d_)
    linarith
  have h_bc_eq : ‖b - c‖ = |correlation
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
      (⟨J, 0, w.re⟩ : IsingParams ℝ)
      (Ambient.liftFinset {x, z} hk) -
      correlation
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
      (⟨J, 0, w.re⟩ : IsingParams ℝ)
      (Ambient.liftFinset {x, z} (hk.trans (Λ.mono (Nat.le_succ k))))| := by
    rw [show b - c = (((correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
        (⟨J, 0, w.re⟩ : IsingParams ℝ)
        (Ambient.liftFinset {x, z} hk) -
      correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
        (⟨J, 0, w.re⟩ : IsingParams ℝ)
        (Ambient.liftFinset {x, z}
          (hk.trans (Λ.mono (Nat.le_succ k))))) : ℝ) : ℂ) from by
      rw [hb_real, hc_real]; push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [h_bc_eq] at h_tri
  have h_ab_le_r : ‖a - b‖ ≤ C_k * r :=
    le_trans h_ab (mul_le_mul_of_nonneg_left h_w_wre_norm_le_r hC_k_nn)
  have h_cd_le_r : ‖c - d_‖ ≤ C_k1 * r :=
    le_trans h_cd (mul_le_mul_of_nonneg_left h_w_wre_norm_le_r hC_k1_nn)
  nlinarith [h_tri, h_real_bound, h_ab_le_r, h_cd_le_r]

/-- **Canonical-radius bundle from real-axis value increment + Lipschitz**
(Issue #3054). Composes `sphere_circle_bound_of_real_inc_and_lipschitz`
(PR #3089) with `CERouteIccGeometricIncrement_of_canonical_radius_circle`
(PR #3086). User supplies, per (β ∈ Icc, k covered), `(R_inc, C_k, C_k1)`
satisfying
`(R_inc + (C_k + C_k1) · canonicalTrivialQRadiusPair) / canonicalTrivialQRadiusPair ≤ M · ratio^k`,
the real-axis value increment bound `R_inc` on `[β - r, β + r]`, and per-stage
Lipschitz hypotheses. Produces the bundle directly — **no smallness witness,
no ne-zero hypothesis, no sphere circle bound**; just the Cauchy-route
mathematical inputs. -/
theorem CERouteIccGeometricIncrement_of_canonical_radius_R_inc_lipschitz
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ)
    (h_inputs : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ R_inc C_k C_k1 : ℝ,
              0 ≤ C_k ∧ 0 ≤ C_k1 ∧
              (R_inc + (C_k + C_k1) * canonicalTrivialQRadiusPair Λ J k)
                / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k ∧
              (∀ β_re : ℝ, β_re ∈ Set.Icc
                  (β - canonicalTrivialQRadiusPair Λ J k)
                  (β + canonicalTrivialQRadiusPair Λ J k) →
                |correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z} hk) -
                    correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C_k * ‖b - ((b.re : ℝ) : ℂ)‖) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C_k1 * ‖b - ((b.re : ℝ) : ℂ)‖)) :
    CERouteIccGeometricIncrement Λ J x z M ratio := by
  refine CERouteIccGeometricIncrement_of_canonical_radius_circle
    Λ J x z M ratio ?_
  intro β₁ β₂ hIcc β hβ k hk
  obtain ⟨R_inc, C_k, C_k1, hC_k_nn, hC_k1_nn, hBR, h_real_inc, h_lip_k, h_lip_k1⟩ :=
    h_inputs β₁ β₂ hIcc β hβ k hk
  refine ⟨R_inc + (C_k + C_k1) * canonicalTrivialQRadiusPair Λ J k, hBR, ?_⟩
  exact sphere_circle_bound_of_real_inc_and_lipschitz Λ J x z k hk
    β (canonicalTrivialQRadiusPair Λ J k) R_inc C_k C_k1
    h_real_inc h_lip_k h_lip_k1 hC_k_nn hC_k1_nn

/-- **One-step Lemma 17.5.2 upper bound from R_inc + Lipschitz** (Issue #3054).
Composition of `CERouteIccGeometricIncrement_of_canonical_radius_R_inc_lipschitz`
(PR #3090) with `lemma_17_5_2_upper_bound_of_CERouteIccGeometricIncrement`
(PR #3075). Delivers `Lemma_17_5_2_UpperBound` directly from per-(β, k)
Cauchy-route mathematical inputs (R_inc + per-stage Lipschitz). -/
theorem lemma_17_5_2_upper_bound_of_R_inc_lipschitz
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h_inputs : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ R_inc C_k C_k1 : ℝ,
              0 ≤ C_k ∧ 0 ≤ C_k1 ∧
              (R_inc + (C_k + C_k1) * canonicalTrivialQRadiusPair Λ J k)
                / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k ∧
              (∀ β_re : ℝ, β_re ∈ Set.Icc
                  (β - canonicalTrivialQRadiusPair Λ J k)
                  (β + canonicalTrivialQRadiusPair Λ J k) →
                |correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z} hk) -
                    correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C_k * ‖b - ((b.re : ℝ) : ℂ)‖) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C_k1 * ‖b - ((b.re : ℝ) : ℂ)‖)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) :=
  lemma_17_5_2_upper_bound_of_CERouteIccGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccGeometricIncrement_of_canonical_radius_R_inc_lipschitz
      Λ J x z M ratio h_inputs)

/-- **One-step Lemma 17.5.2 sandwich from R_inc + Lipschitz + decay**
(Issue #3054). Sandwich analogue. -/
theorem lemma_17_5_2_sandwich_of_R_inc_lipschitz
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h_inputs : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ R_inc C_k C_k1 : ℝ,
              0 ≤ C_k ∧ 0 ≤ C_k1 ∧
              (R_inc + (C_k + C_k1) * canonicalTrivialQRadiusPair Λ J k)
                / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k ∧
              (∀ β_re : ℝ, β_re ∈ Set.Icc
                  (β - canonicalTrivialQRadiusPair Λ J k)
                  (β + canonicalTrivialQRadiusPair Λ J k) →
                |correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z} hk) -
                    correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C_k * ‖b - ((b.re : ℝ) : ℂ)‖) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C_k1 * ‖b - ((b.re : ℝ) : ℂ)‖))
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_sandwich_of_CERouteIccGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccGeometricIncrement_of_canonical_radius_R_inc_lipschitz
      Λ J x z M ratio h_inputs)
    hdecay

/-- **Uniform-C bundle constructor: single Lipschitz for both stages** (Issue
#3054). Convenience specialisation of
`CERouteIccGeometricIncrement_of_canonical_radius_R_inc_lipschitz` (PR #3090)
where a single `C ≥ 0` bounds both stages' Lipschitz. User supplies
`(R_inc, C)` (instead of `(R_inc, C_k, C_k1)`) with
`(R_inc + 2·C·canonicalTrivialQRadiusPair) / canonicalTrivialQRadiusPair ≤ M·ratio^k`. -/
theorem CERouteIccGeometricIncrement_of_canonical_radius_R_inc_uniform_C
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ)
    (h_inputs : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ R_inc C : ℝ,
              0 ≤ C ∧
              (R_inc + 2 * C * canonicalTrivialQRadiusPair Λ J k)
                / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k ∧
              (∀ β_re : ℝ, β_re ∈ Set.Icc
                  (β - canonicalTrivialQRadiusPair Λ J k)
                  (β + canonicalTrivialQRadiusPair Λ J k) →
                |correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z} hk) -
                    correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖)) :
    CERouteIccGeometricIncrement Λ J x z M ratio := by
  refine CERouteIccGeometricIncrement_of_canonical_radius_R_inc_lipschitz
    Λ J x z M ratio ?_
  intro β₁ β₂ hIcc β hβ k hk
  obtain ⟨R_inc, C, hC_nn, hBR, h_real_inc, h_lip_k, h_lip_k1⟩ :=
    h_inputs β₁ β₂ hIcc β hβ k hk
  refine ⟨R_inc, C, C, hC_nn, hC_nn, ?_, h_real_inc, h_lip_k, h_lip_k1⟩
  have hsimp : C + C = 2 * C := by ring
  rw [hsimp]
  exact hBR

/-- **One-step Lemma 17.5.2 upper bound from R_inc + uniform-C** (Issue #3054).
Composition of `CERouteIccGeometricIncrement_of_canonical_radius_R_inc_uniform_C`
(PR #3092) with `lemma_17_5_2_upper_bound_of_CERouteIccGeometricIncrement`
(PR #3075). Delivers `Lemma_17_5_2_UpperBound` directly from per-(β, k) inputs
`(R_inc, C)` with a single Lipschitz `C` covering both stages. -/
theorem lemma_17_5_2_upper_bound_of_R_inc_uniform_C
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h_inputs : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ R_inc C : ℝ,
              0 ≤ C ∧
              (R_inc + 2 * C * canonicalTrivialQRadiusPair Λ J k)
                / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k ∧
              (∀ β_re : ℝ, β_re ∈ Set.Icc
                  (β - canonicalTrivialQRadiusPair Λ J k)
                  (β + canonicalTrivialQRadiusPair Λ J k) →
                |correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z} hk) -
                    correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) :=
  lemma_17_5_2_upper_bound_of_CERouteIccGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccGeometricIncrement_of_canonical_radius_R_inc_uniform_C
      Λ J x z M ratio h_inputs)

/-- **One-step Lemma 17.5.2 sandwich from R_inc + uniform-C + decay** (Issue #3054). -/
theorem lemma_17_5_2_sandwich_of_R_inc_uniform_C
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (h_inputs : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∃ R_inc C : ℝ,
              0 ≤ C ∧
              (R_inc + 2 * C * canonicalTrivialQRadiusPair Λ J k)
                / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k ∧
              (∀ β_re : ℝ, β_re ∈ Set.Icc
                  (β - canonicalTrivialQRadiusPair Λ J k)
                  (β + canonicalTrivialQRadiusPair Λ J k) →
                |correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z} hk) -
                    correlation
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (⟨J, 0, β_re⟩ : IsingParams ℝ)
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume k))
                      (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖) ∧
              (∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                  (canonicalTrivialQRadiusPair Λ J k),
                ‖correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 b -
                    correlationComplex
                      (Ambient.inducedGraph (IsingModel.latticeGraph d)
                        (Λ.volume (k + 1)))
                      (Ambient.liftFinset {x, z}
                        (hk.trans (Λ.mono (Nat.le_succ k))))
                      (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                  ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖))
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_sandwich_of_CERouteIccGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccGeometricIncrement_of_canonical_radius_R_inc_uniform_C
      Λ J x z M ratio h_inputs)
    hdecay

/-- **Explicit `latticeGraph` lower bound for `trivialQRadius`** (Issue #3054).
For the induced lattice graph `inducedGraph (latticeGraph d) Λ`,
`trivialQRadius G J = √2 / (|J| · |E| + 1) ≥ √2 / (|J| · d · |Λ| + 1)` via
`inducedLatticeGraph_card_edgeFinset_le` (`|E| ≤ d · |Λ|`). -/
theorem trivialQRadius_inducedLatticeGraph_lower_bound
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) :
    Real.sqrt 2 / (|J| * (d * Fintype.card (↑Λ : Type _)) + 1) ≤
      IsingModel.trivialQRadius
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J := by
  unfold IsingModel.trivialQRadius
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h_edge_le : ((Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      : ℝ) ≤ d * Fintype.card (↑Λ : Type _) :=
    inducedLatticeGraph_card_edgeFinset_le d Λ
  have hJ_abs_nn : (0 : ℝ) ≤ |J| := abs_nonneg J
  have hJE_le : |J| * ((Ambient.inducedGraph (IsingModel.latticeGraph d)
      Λ).edgeFinset.card : ℝ) ≤ |J| * (d * Fintype.card (↑Λ : Type _)) :=
    mul_le_mul_of_nonneg_left h_edge_le hJ_abs_nn
  have h_denom_le : |J| * ((Ambient.inducedGraph (IsingModel.latticeGraph d)
      Λ).edgeFinset.card : ℝ) + 1 ≤
      |J| * (d * Fintype.card (↑Λ : Type _)) + 1 := by linarith
  have h_denom_rhs_pos :
      (0 : ℝ) < |J| * ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          Λ).edgeFinset.card : ℝ) + 1 := by positivity
  exact div_le_div_of_nonneg_left hsqrt2_pos.le h_denom_rhs_pos h_denom_le

/-- **Per-stage canonical-radius lower bound from `|Λ_{k+1}|`** (Issue #3054).
`canonicalTrivialQRadiusPair Λ J k ≥ √2 / (|J| · d · |Λ.volume (k+1)| + 1)`,
using `inducedLatticeGraph_card_edgeFinset_le` and the exhaustion monotonicity
`Λ.volume k ⊆ Λ.volume (k+1)` (so `|Λ.volume k| ≤ |Λ.volume (k+1)|`). -/
theorem canonicalTrivialQRadiusPair_lower_bound_volume_succ
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ)) (J : ℝ) (k : ℕ) :
    Real.sqrt 2 / (|J| * (d * Fintype.card (↑(Λ.volume (k + 1)) : Type _)) + 1)
      ≤ canonicalTrivialQRadiusPair Λ J k := by
  unfold canonicalTrivialQRadiusPair
  have h_stage_k1_lb := trivialQRadius_inducedLatticeGraph_lower_bound d
    (Λ.volume (k + 1)) J
  have h_stage_k_lb : Real.sqrt 2 /
      (|J| * (d * Fintype.card (↑(Λ.volume (k + 1)) : Type _)) + 1) ≤
      IsingModel.trivialQRadius
        (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k)) J := by
    have h_mono : Λ.volume k ⊆ Λ.volume (k + 1) := Λ.mono (Nat.le_succ k)
    have h_card_le : Fintype.card (↑(Λ.volume k) : Type _) ≤
        Fintype.card (↑(Λ.volume (k + 1)) : Type _) := by
      simpa using Finset.card_le_card h_mono
    have h_card_le_R : (Fintype.card (↑(Λ.volume k) : Type _) : ℝ) ≤
        Fintype.card (↑(Λ.volume (k + 1)) : Type _) := by exact_mod_cast h_card_le
    have hJ_nn : (0 : ℝ) ≤ |J| := abs_nonneg J
    have hd_nn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have h_inner_le : (d : ℝ) * Fintype.card (↑(Λ.volume k) : Type _) ≤
        (d : ℝ) * Fintype.card (↑(Λ.volume (k + 1)) : Type _) :=
      mul_le_mul_of_nonneg_left h_card_le_R hd_nn
    have h_outer_le : |J| * ((d : ℝ) * Fintype.card (↑(Λ.volume k) : Type _)) ≤
        |J| * ((d : ℝ) * Fintype.card (↑(Λ.volume (k + 1)) : Type _)) :=
      mul_le_mul_of_nonneg_left h_inner_le hJ_nn
    have h_denom_le : |J| * ((d : ℝ) * Fintype.card (↑(Λ.volume k) : Type _)) + 1 ≤
        |J| * ((d : ℝ) * Fintype.card (↑(Λ.volume (k + 1)) : Type _)) + 1 := by
      linarith
    have h_sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h_lhs_denom_pos : (0 : ℝ) <
        |J| * ((d : ℝ) * Fintype.card (↑(Λ.volume k) : Type _)) + 1 := by positivity
    have h_decrease : Real.sqrt 2 /
        (|J| * ((d : ℝ) * Fintype.card (↑(Λ.volume (k + 1)) : Type _)) + 1) ≤
        Real.sqrt 2 /
        (|J| * ((d : ℝ) * Fintype.card (↑(Λ.volume k) : Type _)) + 1) :=
      div_le_div_of_nonneg_left h_sqrt2_pos.le h_lhs_denom_pos h_denom_le
    exact le_trans h_decrease
      (trivialQRadius_inducedLatticeGraph_lower_bound d (Λ.volume k) J)
  exact le_min h_stage_k_lb h_stage_k1_lb

/-- **Sequence-form uniform-C bundle constructor** (Issue #3054). Convenience
specialisation of `CERouteIccGeometricIncrement_of_canonical_radius_R_inc_uniform_C`
(PR #3092) where `R_inc` and `C` are sequences `ℕ → ℝ` depending only on
the stage `k` (not on `β`). Closes the per-(β, k) existential by exhibiting
`R_inc := R_inc_seq k` and `C := C_seq k`. -/
theorem CERouteIccGeometricIncrement_of_canonical_radius_sequence
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ)
    (R_inc_seq C_seq : ℕ → ℝ)
    (hC_seq_nn : ∀ k, 0 ≤ C_seq k)
    (h_smallness : ∀ k,
      (R_inc_seq k + 2 * C_seq k * canonicalTrivialQRadiusPair Λ J k)
        / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k)
    (h_real_inc : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ β_re : ℝ, β_re ∈ Set.Icc
                (β - canonicalTrivialQRadiusPair Λ J k)
                (β + canonicalTrivialQRadiusPair Λ J k) →
              |correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z} hk) -
                  correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc_seq k)
    (h_lip_k : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C_seq k * ‖b - ((b.re : ℝ) : ℂ)‖)
    (h_lip_k1 : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C_seq k * ‖b - ((b.re : ℝ) : ℂ)‖) :
    CERouteIccGeometricIncrement Λ J x z M ratio := by
  refine CERouteIccGeometricIncrement_of_canonical_radius_R_inc_uniform_C
    Λ J x z M ratio ?_
  intro β₁ β₂ hIcc β hβ k hk
  refine ⟨R_inc_seq k, C_seq k, hC_seq_nn k, h_smallness k,
    h_real_inc β₁ β₂ hIcc β hβ k hk,
    h_lip_k β₁ β₂ hIcc β hβ k hk,
    h_lip_k1 β₁ β₂ hIcc β hβ k hk⟩

/-- **One-step Lemma 17.5.2 upper bound from sequence-form (R_inc, C)** (Issue
#3054). Composition of `CERouteIccGeometricIncrement_of_canonical_radius_sequence`
(PR #3095) with `lemma_17_5_2_upper_bound_of_CERouteIccGeometricIncrement`
(PR #3075). Delivers `Lemma_17_5_2_UpperBound` directly from sequences
`R_inc_seq, C_seq : ℕ → ℝ`. -/
theorem lemma_17_5_2_upper_bound_of_sequence
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (R_inc_seq C_seq : ℕ → ℝ)
    (hC_seq_nn : ∀ k, 0 ≤ C_seq k)
    (h_smallness : ∀ k,
      (R_inc_seq k + 2 * C_seq k * canonicalTrivialQRadiusPair Λ J k)
        / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k)
    (h_real_inc : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ β_re : ℝ, β_re ∈ Set.Icc
                (β - canonicalTrivialQRadiusPair Λ J k)
                (β + canonicalTrivialQRadiusPair Λ J k) →
              |correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z} hk) -
                  correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc_seq k)
    (h_lip_k : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C_seq k * ‖b - ((b.re : ℝ) : ℂ)‖)
    (h_lip_k1 : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C_seq k * ‖b - ((b.re : ℝ) : ℂ)‖) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) :=
  lemma_17_5_2_upper_bound_of_CERouteIccGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccGeometricIncrement_of_canonical_radius_sequence
      Λ J x z M ratio R_inc_seq C_seq hC_seq_nn h_smallness
      h_real_inc h_lip_k h_lip_k1)

/-- **One-step Lemma 17.5.2 sandwich from sequence-form + decay** (Issue #3054). -/
theorem lemma_17_5_2_sandwich_of_sequence
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (R_inc_seq C_seq : ℕ → ℝ)
    (hC_seq_nn : ∀ k, 0 ≤ C_seq k)
    (h_smallness : ∀ k,
      (R_inc_seq k + 2 * C_seq k * canonicalTrivialQRadiusPair Λ J k)
        / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k)
    (h_real_inc : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ β_re : ℝ, β_re ∈ Set.Icc
                (β - canonicalTrivialQRadiusPair Λ J k)
                (β + canonicalTrivialQRadiusPair Λ J k) →
              |correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z} hk) -
                  correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ R_inc_seq k)
    (h_lip_k : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C_seq k * ‖b - ((b.re : ℝ) : ℂ)‖)
    (h_lip_k1 : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C_seq k * ‖b - ((b.re : ℝ) : ℂ)‖)
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_sandwich_of_CERouteIccGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccGeometricIncrement_of_canonical_radius_sequence
      Λ J x z M ratio R_inc_seq C_seq hC_seq_nn h_smallness
      h_real_inc h_lip_k h_lip_k1)
    hdecay

/-- **Geometric-form bundle constructor: `R_inc_k = M_R · ρ_R^k`, `C` constant**
(Issue #3054). Convenience specialisation of
`CERouteIccGeometricIncrement_of_canonical_radius_sequence` (PR #3095) where
`R_inc` is geometric and `C` is stage-independent. Matches the typical scenario
where axiom-free Simon-Lieb gives geometric real-axis decay and Cauchy estimate
gives a stage-uniform Lipschitz constant. -/
theorem CERouteIccGeometricIncrement_of_canonical_radius_geometric
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio M_R ρ_R C : ℝ)
    (hC_nn : 0 ≤ C)
    (h_smallness : ∀ k,
      (M_R * ρ_R ^ k + 2 * C * canonicalTrivialQRadiusPair Λ J k)
        / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k)
    (h_real_inc : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ β_re : ℝ, β_re ∈ Set.Icc
                (β - canonicalTrivialQRadiusPair Λ J k)
                (β + canonicalTrivialQRadiusPair Λ J k) →
              |correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z} hk) -
                  correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ M_R * ρ_R ^ k)
    (h_lip_k : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖)
    (h_lip_k1 : ∀ β₁ β₂ : ℝ,
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁ β₂,
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖) :
    CERouteIccGeometricIncrement Λ J x z M ratio :=
  CERouteIccGeometricIncrement_of_canonical_radius_sequence
    Λ J x z M ratio (fun k => M_R * ρ_R ^ k) (fun _ => C)
    (fun _ => hC_nn) h_smallness h_real_inc h_lip_k h_lip_k1

/-- **One-step Lemma 17.5.2 upper bound from geometric-form (M_R, ρ_R, C)**
(Issue #3054). Composition of `CERouteIccGeometricIncrement_of_canonical_radius_geometric`
(PR #3097) with `lemma_17_5_2_upper_bound_of_CERouteIccGeometricIncrement`
(PR #3075). Simplest parametric form: geometric R_inc + uniform C. -/
theorem lemma_17_5_2_upper_bound_of_geometric
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio M_R ρ_R C : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hC_nn : 0 ≤ C)
    (h_smallness : ∀ k,
      (M_R * ρ_R ^ k + 2 * C * canonicalTrivialQRadiusPair Λ J k)
        / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k)
    (h_real_inc : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ β_re : ℝ, β_re ∈ Set.Icc
                (β - canonicalTrivialQRadiusPair Λ J k)
                (β + canonicalTrivialQRadiusPair Λ J k) →
              |correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z} hk) -
                  correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ M_R * ρ_R ^ k)
    (h_lip_k : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖)
    (h_lip_k1 : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      Lemma_17_5_2_UpperBound hα hrho Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho)) :=
  lemma_17_5_2_upper_bound_of_CERouteIccGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccGeometricIncrement_of_canonical_radius_geometric
      Λ J x z M ratio M_R ρ_R C hC_nn h_smallness
      h_real_inc h_lip_k h_lip_k1)

/-- **One-step Lemma 17.5.2 sandwich from geometric-form + decay** (Issue #3054). -/
theorem lemma_17_5_2_sandwich_of_geometric
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ_pos : 0 < J)
    (x z : Fin d → ℤ) (hxz : x ≠ z)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (M ratio M_R ρ_R C : ℝ) (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hC_nn : 0 ≤ C)
    (h_smallness : ∀ k,
      (M_R * ρ_R ^ k + 2 * C * canonicalTrivialQRadiusPair Λ J k)
        / canonicalTrivialQRadiusPair Λ J k ≤ M * ratio ^ k)
    (h_real_inc : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ β_re : ℝ, β_re ∈ Set.Icc
                (β - canonicalTrivialQRadiusPair Λ J k)
                (β + canonicalTrivialQRadiusPair Λ J k) →
              |correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z} hk) -
                  correlation
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (⟨J, 0, β_re⟩ : IsingParams ℝ)
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))| ≤ M_R * ρ_R ^ k)
    (h_lip_k : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume k))
                    (Ambient.liftFinset {x, z} hk) (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖)
    (h_lip_k1 : ∀ β₁' β₂' : ℝ,
      Set.Icc β₁' β₂' ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
        ∀ β ∈ Set.Icc β₁' β₂',
          ∀ k : ℕ, (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) →
            ∀ b ∈ Metric.sphere ((β : ℝ) : ℂ)
                (canonicalTrivialQRadiusPair Λ J k),
              ‖correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 b -
                  correlationComplex
                    (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume (k + 1)))
                    (Ambient.liftFinset {x, z}
                      (hk.trans (Λ.mono (Nat.le_succ k))))
                    (J : ℂ) 0 ((b.re : ℝ) : ℂ)‖
                ≤ C * ‖b - ((b.re : ℝ) : ℂ)‖)
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hrho d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_sandwich_of_CERouteIccGeometricIncrement
    hα hαd hd hrho Λ J hJ_pos x z hxz hβ₁ hβ₁₂ hIcc M ratio hratio0 hratio1
    (CERouteIccGeometricIncrement_of_canonical_radius_geometric
      Λ J x z M ratio M_R ρ_R C hC_nn h_smallness
      h_real_inc h_lip_k h_lip_k1)
    hdecay


end Ambient
end IsingModel
