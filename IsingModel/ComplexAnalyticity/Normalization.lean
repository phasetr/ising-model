import IsingModel.ComplexAnalyticity.LeeYangDomain
import IsingModel.ComplexAnalyticity.Polynomial

/-!
# Lee-Yang Normalization and Polynomial Bounds

This module is part of the split `IsingModel.ComplexAnalyticity` development.
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Complex

/-- **Lee-Yang normalization factor**: `exp(β·J·|E| + β·h·|ι|)`.

The Ising partition function factorises (Friedli–Velenik (3.63)) as
`Z = exp(β·J·|E| + β·h·|ι|) · P(z)` with `z_k = e^{-2β h_k}`.
This is the scalar prefactor, used in the Lee-Yang nonvanishing bridge
from the polynomial nonvanishing (`isingEdgePoly_eval_leeYangFugacityVec_ne_zero`)
to `partitionFunctionComplex ≠ 0`. -/
noncomputable def leeYangNormalization (β J h : ℂ) (edgeCount siteCount : ℕ) : ℂ :=
  Complex.exp (β * J * (edgeCount : ℂ) + β * h * (siteCount : ℂ))

/-- The Lee-Yang normalization factor is never zero (product of complex
exponentials, hence non-vanishing). -/
theorem leeYangNormalization_ne_zero
    (β J h : ℂ) (edgeCount siteCount : ℕ) :
    leeYangNormalization β J h edgeCount siteCount ≠ 0 := by
  unfold leeYangNormalization
  exact Complex.exp_ne_zero _

/-- The Lee-Yang normalization factor is jointly entire in `(β, J, h)`. -/
theorem leeYangNormalization_analyticAt_joint
    (edgeCount siteCount : ℕ) (z₀ : ℂ × ℂ × ℂ) :
    AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ =>
      leeYangNormalization z.2.2 z.1 z.2.1 edgeCount siteCount) z₀ := by
  unfold leeYangNormalization
  refine AnalyticAt.cexp' ?_
  have hJ : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => z.1) z₀ := analyticAt_fst
  have hhβ : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => z.2) z₀ := analyticAt_snd
  have hh : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => z.2.1) z₀ :=
    analyticAt_fst.comp hhβ
  have hβ : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => z.2.2) z₀ :=
    analyticAt_snd.comp hhβ
  exact (hβ.mul hJ |>.mul analyticAt_const).add (hβ.mul hh |>.mul analyticAt_const)

/-- At real parameters, `leeYangNormalization` is a positive real number.
This matches the `exp(β J |E| + β h |ι|)` prefactor of the real-valued
partition function, which is always strictly positive. -/
theorem leeYangNormalization_ofReal_pos
    (β J h : ℝ) (edgeCount siteCount : ℕ) :
    0 < (leeYangNormalization (β : ℂ) (J : ℂ) (h : ℂ)
            edgeCount siteCount).re := by
  unfold leeYangNormalization
  have heq : (β : ℂ) * (J : ℂ) * (edgeCount : ℂ)
              + (β : ℂ) * (h : ℂ) * (siteCount : ℂ)
            = ((β * J * edgeCount + β * h * siteCount : ℝ) : ℂ) := by
    push_cast; ring
  rw [heq, ← Complex.ofReal_exp, Complex.ofReal_re]
  exact Real.exp_pos _

/-- **Lee-Yang nonvanishing of the Ising partition polynomial on the
Lee-Yang domain** (uniform field, real ferromagnetic coupling).

For a graph `G`, a coupling parameter `t ∈ [0, 1)`, real `β > 0`,
and `h ∈ leeYangDomain`, the Ising partition polynomial
`P_E(z)` does not vanish at the uniform fugacity
`z_k = e^{-2β h}`:
  `(isingEdgePoly (graphToEdgeList G t)).eval (leeYangFugacityVec β h) ≠ 0`.

Direct consequence of `isingEdgePoly_nonvanishing_of_graph`
(FreeEnergy.lean, which wraps the Lee-Yang circle theorem) together
with the unit-disk bound `leeYangFugacityVec_norm_lt_one`. -/
theorem isingEdgePoly_eval_leeYangFugacityVec_ne_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1)
    {β : ℝ} (hβ : 0 < β) {h : ℂ} (hh : h ∈ leeYangDomain) :
    (isingEdgePoly (graphToEdgeList G t)).eval
        (leeYangFugacityVec (β : ℂ) h) ≠ 0 :=
  isingEdgePoly_nonvanishing_of_graph G t ht₀ ht₁
    (leeYangFugacityVec (β : ℂ) h)
    (fun k => leeYangFugacityVec_norm_lt_one hβ hh k)

/-- **Product of Lee-Yang prefactor and polynomial is non-zero on the
Lee-Yang domain**. This is the final form that matches the
Friedli–Velenik identity `Z = leeYangNormalization · P(z)`:
the RHS is non-zero, hence so is `Z` (once the identity is formally
established). -/
theorem leeYangNormalization_mul_isingEdgePoly_eval_ne_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1)
    (J : ℂ) {β : ℝ} (hβ : 0 < β) {h : ℂ} (hh : h ∈ leeYangDomain)
    (edgeCount siteCount : ℕ) :
    leeYangNormalization (β : ℂ) J h edgeCount siteCount
        * (isingEdgePoly (graphToEdgeList G t)).eval
            (leeYangFugacityVec (β : ℂ) h) ≠ 0 :=
  mul_ne_zero (leeYangNormalization_ne_zero _ _ _ _ _)
    (isingEdgePoly_eval_leeYangFugacityVec_ne_zero G ht₀ ht₁ hβ hh)

/-- **Finite-volume compact lower bound for the Lee-Yang polynomial factor**:
on a compact subset of the Lee-Yang domain, the finite-volume polynomial factor
at the uniform fugacity has a positive lower bound.

This is a compactness consequence of continuity and finite-volume Lee-Yang
nonvanishing. The constant is finite-volume dependent; this theorem does not
provide stage-uniform lower normalised-log control. -/
theorem exists_pos_le_norm_isingEdgePoly_eval_leeYangFugacityVec_on_isCompact
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1)
    {β : ℝ} (hβ : 0 < β) {K : Set ℂ}
    (hK : IsCompact K) (hKsub : K ⊆ leeYangDomain) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ h ∈ K,
        ε ≤ ‖(isingEdgePoly (graphToEdgeList G t)).eval
          (leeYangFugacityVec (β : ℂ) h)‖ := by
  let F : ℂ → ℝ := fun h =>
    ‖(isingEdgePoly (graphToEdgeList G t)).eval (leeYangFugacityVec (β : ℂ) h)‖
  have hcont : ContinuousOn F K := by
    have hvec : Continuous (fun h : ℂ => (leeYangFugacityVec (β : ℂ) h : ι → ℂ)) := by
      exact continuous_pi (fun i => by
        simpa [leeYangFugacityVec] using continuous_leeYangFugacity (β : ℂ))
    exact ((MultilinPoly.continuous_eval (isingEdgePoly (graphToEdgeList G t))).comp
      hvec).norm.continuousOn
  by_cases hne : K.Nonempty
  · rcases hK.exists_isMinOn hne hcont with ⟨h₀, hh₀, hmin⟩
    refine ⟨F h₀, ?_, ?_⟩
    · exact norm_pos_iff.mpr
        (isingEdgePoly_eval_leeYangFugacityVec_ne_zero G ht₀ ht₁ hβ (hKsub hh₀))
    · intro h hh
      exact hmin hh
  · refine ⟨1, zero_lt_one, ?_⟩
    intro h hh
    exact False.elim (hne ⟨h, hh⟩)

/-- The one-variable Lee-Yang polynomial associated to an Ising edge
polynomial has value `1` at the origin. -/
theorem isingEdgePoly_uniformPolynomial_eval_zero (edges : List (ι × ι × ℝ)) :
    (isingEdgePoly edges).uniformPolynomial.eval 0 = 1 := by
  rw [MultilinPoly.uniformPolynomial_eval, MultilinPoly.eval_const_zero]
  simp [isingEdgePoly, edgeWeight]

/-- Roots of the one-variable specialisation of the Ising Lee-Yang polynomial
lie outside the open unit disk. -/
theorem isingEdgePoly_uniformPolynomial_roots_norm_ge_one
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    ∀ a ∈ (isingEdgePoly (graphToEdgeList G t)).uniformPolynomial.roots,
      1 ≤ ‖a‖ := by
  classical
  let q : Polynomial ℂ := (isingEdgePoly (graphToEdgeList G t)).uniformPolynomial
  have hq0 : q.eval 0 = 1 := by
    simpa [q] using isingEdgePoly_uniformPolynomial_eval_zero (graphToEdgeList G t)
  have hq_ne : q ≠ 0 := by
    intro hq
    have hzero : q.eval 0 = 0 := by simp [hq]
    linarith [show (q.eval 0).re = 1 by rw [hq0]; simp,
      show (q.eval 0).re = 0 by rw [hzero]; simp]
  intro a ha
  by_contra hbad
  have ha_lt : ‖a‖ < 1 := lt_of_not_ge hbad
  have hroot : q.eval a = 0 := (Polynomial.mem_roots hq_ne).mp ha
  have hnonzero : q.eval a ≠ 0 := by
    rw [MultilinPoly.uniformPolynomial_eval]
    exact isingEdgePoly_nonvanishing_of_graph G t ht₀ ht₁
      (fun _ : ι => a) (fun _ => ha_lt)
  exact hnonzero hroot

/-- Quantitative one-variable Lee-Yang lower bound: if `‖z‖ ≤ r < 1`, then
the uniform-fugacity Lee-Yang polynomial is bounded below by `(1-r)^|ι|`. -/
theorem one_sub_radius_pow_card_le_norm_isingEdgePoly_eval_const
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t r : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) {z : ℂ} (hz : ‖z‖ ≤ r) :
    (1 - r) ^ Fintype.card ι
      ≤ ‖(isingEdgePoly (graphToEdgeList G t)).eval (fun _ : ι => z)‖ := by
  let q : Polynomial ℂ := (isingEdgePoly (graphToEdgeList G t)).uniformPolynomial
  have hq0 : q.eval 0 = 1 := by
    simpa [q] using isingEdgePoly_uniformPolynomial_eval_zero (graphToEdgeList G t)
  have hroots : ∀ a ∈ q.roots, 1 ≤ ‖a‖ := by
    simpa [q] using isingEdgePoly_uniformPolynomial_roots_norm_ge_one (G := G) ht₀ ht₁
  have hdeg : q.natDegree ≤ Fintype.card ι := by
    simpa [q] using
      (MultilinPoly.uniformPolynomial_natDegree_le_card
        (isingEdgePoly (graphToEdgeList G t) : MultilinPoly ι))
  have hbase_nonneg : 0 ≤ 1 - r := by linarith
  have hbase_le_one : 1 - r ≤ 1 := by linarith
  have hpow_card_le : (1 - r) ^ Fintype.card ι ≤ (1 - r) ^ q.natDegree :=
    pow_le_pow_of_le_one hbase_nonneg hbase_le_one hdeg
  have hlower :
      (1 - r) ^ q.natDegree ≤ ‖q.eval z‖ :=
    Polynomial.one_sub_radius_pow_natDegree_le_norm_eval_of_roots_norm_ge_one
      q hr0 hr1 hq0 hroots hz
  calc
    (1 - r) ^ Fintype.card ι ≤ (1 - r) ^ q.natDegree := hpow_card_le
    _ ≤ ‖q.eval z‖ := hlower
    _ = ‖(isingEdgePoly (graphToEdgeList G t)).eval (fun _ : ι => z)‖ := by
      rw [MultilinPoly.uniformPolynomial_eval]

/-- Quantitative Lee-Yang lower bound for the uniform fugacity vector
`leeYangFugacityVec`. -/
theorem one_sub_radius_pow_card_le_norm_isingEdgePoly_eval_leeYangFugacityVec
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t r : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1)
    {β h : ℂ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hz : ‖leeYangFugacity β h‖ ≤ r) :
    (1 - r) ^ Fintype.card ι
      ≤ ‖(isingEdgePoly (graphToEdgeList G t)).eval
          (leeYangFugacityVec β h)‖ := by
  simpa [leeYangFugacityVec] using
    one_sub_radius_pow_card_le_norm_isingEdgePoly_eval_const
      (G := G) ht₀ ht₁ hr0 hr1 (z := leeYangFugacity β h) hz


end IsingModel
