import IsingModel.ComplexAnalyticity.Locus

/-!
# Fugacity and Normalization Calculus

This module is part of the split `IsingModel.ComplexAnalyticity` development.
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Complex

/-- `partitionFunctionComplex` is continuous on `leeYangDomain`
(restriction of entire continuity). -/
theorem partitionFunctionComplex_continuousOn_leeYangDomain
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℂ) :
    ContinuousOn (fun h => partitionFunctionComplex G J h β) leeYangDomain :=
  (continuous_partitionFunctionComplex_h G J β).continuousOn

/-- `partitionFunctionComplex` is AnalyticOn on `leeYangDomain`
(restriction of entire analyticity). -/
theorem partitionFunctionComplex_analyticOn_leeYangDomain
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℂ) :
    AnalyticOn ℂ (fun h => partitionFunctionComplex G J h β) leeYangDomain :=
  (partitionFunctionComplex_analyticOnNhd_leeYangDomain G J β).analyticOn

/-- `leeYangFugacity β` is continuous (everywhere on `ℂ`). Restatement
of `continuous_leeYangFugacity`. -/
theorem continuous_leeYangFugacity' (β : ℂ) :
    Continuous (leeYangFugacity β) := continuous_leeYangFugacity β

/-- `leeYangFugacity β` is `AnalyticOn` on any set. -/
theorem leeYangFugacity_analyticOn (β : ℂ) (U : Set ℂ) :
    AnalyticOn ℂ (leeYangFugacity β) U :=
  (analyticOnNhd_leeYangFugacity β).mono (Set.subset_univ U) |>.analyticOn

/-- `leeYangFugacity β` is `DifferentiableOn` on any set. -/
theorem leeYangFugacity_differentiableOn (β : ℂ) (U : Set ℂ) :
    DifferentiableOn ℂ (leeYangFugacity β) U :=
  ((analyticOnNhd_leeYangFugacity β).mono (Set.subset_univ U)).differentiableOn

/-- `leeYangFugacity β` is `Differentiable` on all of `ℂ`. -/
theorem leeYangFugacity_differentiable (β : ℂ) :
    Differentiable ℂ (leeYangFugacity β) :=
  differentiableOn_univ.mp (leeYangFugacity_differentiableOn β Set.univ)

/-- `leeYangFugacity β` is `HasDerivAt` at every point. -/
theorem leeYangFugacity_hasDerivAt (β : ℂ) (h : ℂ) :
    HasDerivAt (leeYangFugacity β)
      (-2 * β * Complex.exp (-2 * β * h)) h := by
  unfold leeYangFugacity
  have h1 : HasDerivAt (fun z : ℂ => -2 * β * z) (-2 * β) h := by
    simpa using ((hasDerivAt_id h).const_mul (-2 * β))
  exact h1.cexp.congr_deriv (by ring)

/-- `leeYangFugacity_deriv`: `deriv (leeYangFugacity β) h
  = -2·β·exp(-2·β·h)`. -/
theorem leeYangFugacity_deriv (β h : ℂ) :
    deriv (leeYangFugacity β) h = -2 * β * Complex.exp (-2 * β * h) :=
  (leeYangFugacity_hasDerivAt β h).deriv

/-- Logarithmic derivative of `leeYangFugacity β`: `(d/dh log z(h))
  = -2β`. In particular, the relative change in the fugacity is
constant. -/
theorem leeYangFugacity_logDeriv (β h : ℂ) :
    deriv (leeYangFugacity β) h / leeYangFugacity β h = -2 * β := by
  rw [leeYangFugacity_deriv]
  unfold leeYangFugacity
  field_simp

/-- `leeYangNormalization` has entire analyticity in `h` (for any β, J). -/
theorem leeYangNormalization_analyticAt_h
    (β J : ℂ) (h₀ : ℂ) (edgeCount siteCount : ℕ) :
    AnalyticAt ℂ (fun h => leeYangNormalization β J h edgeCount siteCount) h₀ := by
  unfold leeYangNormalization
  refine AnalyticAt.cexp' ?_
  fun_prop

/-- `leeYangNormalization` analytic in `β`. -/
theorem leeYangNormalization_analyticAt_beta
    (β₀ J h : ℂ) (edgeCount siteCount : ℕ) :
    AnalyticAt ℂ (fun β => leeYangNormalization β J h edgeCount siteCount) β₀ := by
  unfold leeYangNormalization
  refine AnalyticAt.cexp' ?_
  fun_prop

/-- `leeYangNormalization` analytic in `J`. -/
theorem leeYangNormalization_analyticAt_J
    (β : ℂ) (J₀ : ℂ) (h : ℂ) (edgeCount siteCount : ℕ) :
    AnalyticAt ℂ (fun J => leeYangNormalization β J h edgeCount siteCount) J₀ := by
  unfold leeYangNormalization
  refine AnalyticAt.cexp' ?_
  fun_prop

/-- `leeYangNormalization β J h 0 0 = exp(0) = 1`. -/
theorem leeYangNormalization_zero_zero (β J h : ℂ) :
    leeYangNormalization β J h 0 0 = 1 := by
  unfold leeYangNormalization
  simp

/-- `leeYangNormalization β 0 0 |E| |ι| = exp(0) = 1` (at J = h = 0). -/
theorem leeYangNormalization_zero_params (β : ℂ) (edgeCount siteCount : ℕ) :
    leeYangNormalization β 0 0 edgeCount siteCount = 1 := by
  unfold leeYangNormalization
  simp

/-- `leeYangNormalization 0 J h |E| |ι| = exp(0) = 1` (at β = 0). -/
theorem leeYangNormalization_beta_zero (J h : ℂ) (edgeCount siteCount : ℕ) :
    leeYangNormalization 0 J h edgeCount siteCount = 1 := by
  unfold leeYangNormalization
  simp

/-- `‖leeYangNormalization (β:ℝ) J h |E| |ι|‖ = exp(β·Re(J·|E| + h·|ι|))`
at real `β`. -/
theorem norm_leeYangNormalization_real_beta
    (β : ℝ) (J h : ℂ) (edgeCount siteCount : ℕ) :
    ‖leeYangNormalization (β : ℂ) J h edgeCount siteCount‖
      = Real.exp (β * (J * (edgeCount : ℂ) + h * (siteCount : ℂ))).re := by
  unfold leeYangNormalization
  rw [Complex.norm_exp]
  congr 1
  ring_nf

/-- **Finite-volume `Z_ℂ` lower bound from the Lee-Yang polynomial factor**:
if the Lee-Yang polynomial factor is bounded below by `ε` at `h`, and
`|Re h| ≤ R`, then the Friedli-Velenik factorisation gives the corresponding
finite-volume lower bound on the complex partition function.

The bound is finite-graph dependent through `ε`; it is not a stage-uniform
lower normalised-log estimate along an exhaustion. -/
theorem norm_partitionFunctionComplex_ge_exp_mul_isingEdgePoly_lower
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J R ε : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) {h : ℂ}
    (hR : |h.re| ≤ R) (hε : 0 ≤ ε)
    (hpoly :
      ε ≤ ‖(isingEdgePoly (graphToEdgeList G (Real.exp (-2 * β * J)))).eval
          (leeYangFugacityVec (β : ℂ) h)‖) :
    Real.exp (-β * R * Fintype.card ι) * ε
      ≤ ‖partitionFunctionComplex G (J : ℂ) h (β : ℂ)‖ := by
  rw [partitionFunctionComplex_eq_normalization_mul_isingEdgePoly G β J h]
  rw [norm_mul]
  have hR_lower : -R ≤ h.re := by
    exact neg_le.mp (neg_le_abs h.re |>.trans hR)
  have hnorm :
      Real.exp (-β * R * Fintype.card ι)
        ≤ ‖leeYangNormalization (β : ℂ) (J : ℂ) h
            G.edgeFinset.card (Fintype.card ι)‖ := by
    rw [norm_leeYangNormalization_real_beta]
    refine Real.exp_le_exp.mpr ?_
    have hcast :
        (β * ((J : ℂ) * (G.edgeFinset.card : ℂ)
              + h * (Fintype.card ι : ℂ))).re
          =
        β * (J * G.edgeFinset.card + h.re * Fintype.card ι) := by
      simp [Complex.mul_re, Complex.add_re]
    rw [hcast]
    have hJedge : 0 ≤ J * (G.edgeFinset.card : ℝ) := by positivity
    have hfield : -R * (Fintype.card ι : ℝ) ≤ h.re * (Fintype.card ι : ℝ) := by
      exact mul_le_mul_of_nonneg_right hR_lower (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hfield hβ, mul_nonneg hβ hJedge]
  exact mul_le_mul hnorm hpoly hε (norm_nonneg _)

/-- At real `β, J, h`, `leeYangNormalization` is a positive real number
(cast). -/
theorem leeYangNormalization_ofReal_eq (β J h : ℝ) (edgeCount siteCount : ℕ) :
    leeYangNormalization (β : ℂ) (J : ℂ) (h : ℂ) edgeCount siteCount
      = ((Real.exp (β * J * edgeCount + β * h * siteCount) : ℝ) : ℂ) := by
  unfold leeYangNormalization
  rw [show ((β : ℂ) * (J : ℂ) * (edgeCount : ℂ) + (β : ℂ) * (h : ℂ) *
            (siteCount : ℂ))
          = ((β * J * edgeCount + β * h * siteCount : ℝ) : ℂ) from by
    push_cast; ring]
  rw [Complex.ofReal_exp]

/-- `leeYangNormalization` at real params is always a positive real. -/
theorem leeYangNormalization_real_pos (β J h : ℝ) (edgeCount siteCount : ℕ) :
    ∃ x : ℝ, 0 < x ∧
      leeYangNormalization (β : ℂ) (J : ℂ) (h : ℂ) edgeCount siteCount
        = (x : ℂ) :=
  ⟨Real.exp (β * J * edgeCount + β * h * siteCount), Real.exp_pos _,
    leeYangNormalization_ofReal_eq β J h edgeCount siteCount⟩

/-- `leeYangNormalization` norm at real parameters. -/
theorem norm_leeYangNormalization_ofReal (β J h : ℝ) (edgeCount siteCount : ℕ) :
    ‖leeYangNormalization (β : ℂ) (J : ℂ) (h : ℂ) edgeCount siteCount‖
      = Real.exp (β * J * edgeCount + β * h * siteCount) := by
  rw [leeYangNormalization_ofReal_eq, Complex.norm_real]
  exact abs_of_pos (Real.exp_pos _)

/-- Norm positivity of `leeYangNormalization`. -/
theorem leeYangNormalization_norm_pos
    (β J h : ℂ) (edgeCount siteCount : ℕ) :
    0 < ‖leeYangNormalization β J h edgeCount siteCount‖ :=
  norm_pos_iff.mpr (leeYangNormalization_ne_zero β J h edgeCount siteCount)

end IsingModel
