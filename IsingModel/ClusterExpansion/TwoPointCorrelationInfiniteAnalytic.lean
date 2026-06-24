import IsingModel.ClusterExpansion.TwoPointCorrelationHTBound
import IsingModel.AmbientComplexAnalyticity.VolumeUniformZNonvanishing
import IsingModel.AmbientComplexAnalyticity.Vitali.CorrelationRealAxisVitali

/-!
# Infinite-volume high-temperature analyticity of the two-point function

This file is the final Route B capstone for the high-temperature two-point correlation
analyticity argument.

Layer 1 proves a finite-graph two-point correlation bound on a beta-disc whose radius depends
only on the degree cap `Delta` and the real coupling `J`, not on the finite graph.

Layer 2 applies the degree-uniform finite-graph bound to every induced lattice-exhaustion stage
and feeds the resulting volume-uniform local boundedness into the existing Vitali--Porter bridge.
-/

namespace IsingModel

open Finset Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## A degree-uniform beta radius -/

/-- A positive beta-radius on which `tanh (beta * J)` is inside the degree-uniform two-point
activity ball and `cosh (beta * J)` is nonzero. -/
private theorem exists_twoPointHTUniformRadius (Δ : ℕ) (J : ℝ) :
    ∃ r > 0,
      (∀ β ∈ Metric.ball (0 : ℂ) r,
        ‖Complex.tanh (β * (J : ℂ))‖ < twoPointHTActivityRadius Δ) ∧
      (∀ β ∈ Metric.ball (0 : ℂ) r,
        Complex.cosh (β * (J : ℂ)) ≠ 0) := by
  classical
  set R : ℝ := twoPointHTActivityRadius Δ with hRdef
  have hR : 0 < R := by simpa [hRdef] using twoPointHTActivityRadius_pos Δ
  have h_cosh0 : Complex.cosh ((0 : ℂ) * (J : ℂ)) ≠ 0 := by
    rw [zero_mul, Complex.cosh_zero]
    exact one_ne_zero
  have h_cosh_ev : ∀ᶠ β : ℂ in 𝓝 (0 : ℂ), Complex.cosh (β * (J : ℂ)) ≠ 0 :=
    (Complex.continuous_cosh.comp (continuous_id.mul continuous_const)).continuousAt.eventually_ne
      h_cosh0
  rw [Metric.eventually_nhds_iff_ball] at h_cosh_ev
  obtain ⟨rC, hrC, hcosh⟩ := h_cosh_ev
  have h_tanh0 : Complex.tanh ((0 : ℂ) * (J : ℂ)) = 0 := by
    rw [zero_mul, Complex.tanh_zero]
  have h_tanh_cont : ContinuousAt (fun β : ℂ => Complex.tanh (β * (J : ℂ))) 0 := by
    have hsinh : ContinuousAt (fun β : ℂ => Complex.sinh (β * (J : ℂ))) 0 :=
      (Complex.continuous_sinh.comp (continuous_id.mul continuous_const)).continuousAt
    have hcosh' : ContinuousAt (fun β : ℂ => Complex.cosh (β * (J : ℂ))) 0 :=
      (Complex.continuous_cosh.comp (continuous_id.mul continuous_const)).continuousAt
    exact hsinh.div hcosh' h_cosh0
  have h_tanh_ev : ∀ᶠ β : ℂ in 𝓝 (0 : ℂ), ‖Complex.tanh (β * (J : ℂ))‖ < R := by
    have htend : Filter.Tendsto (fun β : ℂ => ‖Complex.tanh (β * (J : ℂ))‖)
        (𝓝 0) (𝓝 0) := by
      have h2 := h_tanh_cont.norm.tendsto
      rwa [h_tanh0, norm_zero] at h2
    exact htend.eventually (gt_mem_nhds hR)
  rw [Metric.eventually_nhds_iff_ball] at h_tanh_ev
  obtain ⟨rT, hrT, htanh⟩ := h_tanh_ev
  refine ⟨min rT rC, lt_min hrT hrC, ?_, ?_⟩
  · intro β hβ
    have hdist : dist β 0 < min rT rC := Metric.mem_ball.mp hβ
    exact htanh β (Metric.mem_ball.mpr (lt_of_lt_of_le hdist (min_le_left _ _)))
  · intro β hβ
    have hdist : dist β 0 < min rT rC := Metric.mem_ball.mp hβ
    exact hcosh β (Metric.mem_ball.mpr (lt_of_lt_of_le hdist (min_le_right _ _)))

/-- The degree-uniform high-temperature beta radius for two-point correlations. -/
noncomputable def twoPointHTUniformRadius (Δ : ℕ) (J : ℝ) : ℝ :=
  Classical.choose (exists_twoPointHTUniformRadius Δ J)

/-- The degree-uniform beta radius is positive. -/
theorem twoPointHTUniformRadius_pos (Δ : ℕ) (J : ℝ) :
    0 < twoPointHTUniformRadius Δ J :=
  (Classical.choose_spec (exists_twoPointHTUniformRadius Δ J)).1

/-- On the degree-uniform beta radius, the `tanh` activity lies in the two-point activity ball. -/
theorem twoPointHTUniformRadius_tanh_lt (Δ : ℕ) (J : ℝ) :
    ∀ β ∈ Metric.ball (0 : ℂ) (twoPointHTUniformRadius Δ J),
      ‖Complex.tanh (β * (J : ℂ))‖ < twoPointHTActivityRadius Δ :=
  (Classical.choose_spec (exists_twoPointHTUniformRadius Δ J)).2.1

/-- On the degree-uniform beta radius, `cosh (beta * J)` is nonzero. -/
theorem twoPointHTUniformRadius_cosh_ne (Δ : ℕ) (J : ℝ) :
    ∀ β ∈ Metric.ball (0 : ℂ) (twoPointHTUniformRadius Δ J),
      Complex.cosh (β * (J : ℂ)) ≠ 0 :=
  (Classical.choose_spec (exists_twoPointHTUniformRadius Δ J)).2.2

/-! ## Uniform-radii high-temperature ratio identity -/

/-- Analyticity of a single `tanh (beta * J)^k` term at points where
`cosh (beta * J)` is nonzero. -/
private lemma tanh_pow_analyticAt_of_cosh_ne (J : ℝ) (k : ℕ) (z : ℂ)
    (hz : Complex.cosh (z * (J : ℂ)) ≠ 0) :
    AnalyticAt ℂ (fun β : ℂ => Complex.tanh (β * (J : ℂ)) ^ k) z := by
  have h_mul : AnalyticAt ℂ (fun β : ℂ => β * (J : ℂ)) z :=
    analyticAt_id.mul analyticAt_const
  have htanh : AnalyticAt ℂ (Complex.tanh ∘ fun β : ℂ => β * (J : ℂ)) z := by
    refine AnalyticAt.comp ?_ h_mul
    exact analyticAt_complex_tanh _ hz
  exact htanh.pow _

/-- Analyticity of the `htSubgraphSum` after the substitution `z = tanh (beta * J)`. -/
private lemma htSubgraphSum_tanh_analyticAt (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (J : ℝ) (z : ℂ)
    (hz : Complex.cosh (z * (J : ℂ)) ≠ 0) :
    AnalyticAt ℂ
      (fun β : ℂ => htSubgraphSum G A (Complex.tanh (β * (J : ℂ)))) z := by
  classical
  unfold htSubgraphSum
  exact Finset.analyticAt_fun_sum _ fun X _ =>
    tanh_pow_analyticAt_of_cosh_ne J X.card z hz

/-- The complex partition function high-temperature identity on any connected domain where
`cosh (beta * J)` is nonzero. -/
theorem partitionFunctionComplex_high_temp_expansion_h_zero_htSubgraphSum_on_connected
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) {U : Set ℂ}
    (_hU : IsOpen U) (hUconn : IsPreconnected U) (h0U : (0 : ℂ) ∈ U)
    (hcoshU : ∀ z ∈ U, Complex.cosh (z * (J : ℂ)) ≠ 0) :
    Set.EqOn
      (fun β : ℂ => partitionFunctionComplex G (J : ℂ) 0 β)
      (fun β : ℂ =>
        (2 : ℂ) ^ Fintype.card ι *
          Complex.cosh (β * (J : ℂ)) ^ G.edgeFinset.card *
          htSubgraphSum G (∅ : Finset ι) (Complex.tanh (β * (J : ℂ))))
      U := by
  classical
  set f : ℂ → ℂ := fun β => partitionFunctionComplex G (J : ℂ) 0 β with hf
  set g : ℂ → ℂ := fun β =>
    (2 : ℂ) ^ Fintype.card ι *
      Complex.cosh (β * (J : ℂ)) ^ G.edgeFinset.card *
      htSubgraphSum G (∅ : Finset ι) (Complex.tanh (β * (J : ℂ))) with hg
  have hf_anal : AnalyticOnNhd ℂ f U := by
    intro z _
    simpa [hf] using partitionFunctionComplex_analyticAt_beta G (J : ℂ) 0 z
  have hg_anal : AnalyticOnNhd ℂ g U := by
    intro z hz
    have hcosh_z := hcoshU z hz
    have h_two : AnalyticAt ℂ (fun _ : ℂ => (2 : ℂ) ^ Fintype.card ι) z :=
      analyticAt_const
    have h_cosh : AnalyticAt ℂ
        (fun β : ℂ => Complex.cosh (β * (J : ℂ)) ^ G.edgeFinset.card) z := by
      have h_mul : AnalyticAt ℂ (fun β : ℂ => β * (J : ℂ)) z :=
        analyticAt_id.mul analyticAt_const
      have h_comp : AnalyticAt ℂ (Complex.cosh ∘ fun β : ℂ => β * (J : ℂ)) z := by
        refine AnalyticAt.comp ?_ h_mul
        exact Complex.analyticOnNhd_cosh (s := Set.univ) (z * (J : ℂ)) (Set.mem_univ _)
      exact h_comp.pow _
    have h_ht : AnalyticAt ℂ
        (fun β : ℂ => htSubgraphSum G (∅ : Finset ι)
          (Complex.tanh (β * (J : ℂ)))) z :=
      htSubgraphSum_tanh_analyticAt G (∅ : Finset ι) J z hcosh_z
    simpa [hg] using (h_two.mul h_cosh).mul h_ht
  have h_frequently : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = g z := by
    have hev : (fun β : ℂ => f β) =ᶠ[𝓝 (0 : ℂ)] g := by
      filter_upwards
        [partitionFunctionComplex_high_temp_expansion_h_zero_polymer_family_near_zero_beta G J]
        with β hβ
      simp only [hf, hg]
      rw [hβ]
      rw [htSubgraphSum_empty_eq_vdPolymerFamilies_sum_complex]
    exact (Filter.Eventually.frequently (hev.filter_mono inf_le_left))
  exact hf_anal.eqOn_of_preconnected_of_frequently_eq hg_anal hUconn h0U h_frequently

/-- **High-temperature two-point ratio identity on a connected `cosh≠0` / activity-radius domain.**
On an open preconnected `U ∋ 0` where `cosh(βJ) ≠ 0` and `‖tanh(βJ)‖ < twoPointHTActivityRadius Δ`,
`correlationComplex G A J 0 β = htSubgraphSum G A / htSubgraphSum G ∅` (in `tanh(βJ)`). The
`ball 0`-version is the corollary `…_on_uniform_ball`. -/
private theorem correlationComplex_high_temp_expansion_h_zero_htSubgraphSum_on_connected
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (A : Finset ι) (J : ℝ) (Δ : ℕ) (hΔ : G.maxDegree ≤ Δ)
    {U : Set ℂ} (hUopen : IsOpen U) (hUpre : IsPreconnected U) (h0U : (0 : ℂ) ∈ U)
    (hcoshU : ∀ z ∈ U, Complex.cosh (z * (J : ℂ)) ≠ 0)
    (htanhU : ∀ z ∈ U, ‖Complex.tanh (z * (J : ℂ))‖ < twoPointHTActivityRadius Δ) :
    Set.EqOn (fun β : ℂ => correlationComplex G A (J : ℂ) 0 β)
      (fun β : ℂ => htSubgraphSum G A (Complex.tanh (β * (J : ℂ))) /
        htSubgraphSum G (∅ : Finset ι) (Complex.tanh (β * (J : ℂ)))) U := by
  classical
  set R : ℝ := twoPointHTActivityRadius Δ with hRdef
  have hRpos : 0 < R := by simpa [hRdef] using twoPointHTActivityRadius_pos Δ
  have hΔcast : (G.maxDegree : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ
  have hRkpΔ : (Δ : ℝ) ^ 2 * (Real.exp 1 * R) < 1 / 64 := by
    simpa [hRdef] using twoPointHTActivityRadius_kp_threshold Δ
  have hRkpG64 : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R) < 1 / 64 := by
    have hle : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R)
        ≤ (Δ : ℝ) ^ 2 * (Real.exp 1 * R) := by gcongr
    exact lt_of_le_of_lt hle hRkpΔ
  have hRkpG6 : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R) < 1 / 6 := by
    linarith [hRkpG64]
  obtain ⟨hkpR, hρR⟩ := kp_tail_conditions_of_lt hRkpG6
  have hpartEq :=
    partitionFunctionComplex_high_temp_expansion_h_zero_htSubgraphSum_on_connected
      (G := G) (J := J) hUopen hUpre h0U hcoshU
  have hdenU : ∀ z ∈ U,
      htSubgraphSum G (∅ : Finset ι) (Complex.tanh (z * (J : ℂ))) ≠ 0 := by
    intro z hz
    have hzball : Complex.tanh (z * (J : ℂ)) ∈ Metric.ball (0 : ℂ) R := by
      rw [Metric.mem_ball, dist_zero_right]
      exact htanhU z hz
    have hQ :=
      htSubgraphSum_empty_eq_exp_tsum_mayerExpansionTermComplex (G := G)
        hRpos hkpR hρR hzball
    rw [hQ]
    exact Complex.exp_ne_zero _
  have hZU : ∀ z ∈ U, partitionFunctionComplex G (J : ℂ) 0 z ≠ 0 := by
    intro z hz
    rw [show partitionFunctionComplex G (J : ℂ) 0 z =
        (2 : ℂ) ^ Fintype.card ι *
          Complex.cosh (z * (J : ℂ)) ^ G.edgeFinset.card *
          htSubgraphSum G (∅ : Finset ι) (Complex.tanh (z * (J : ℂ))) from hpartEq hz]
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ ?_) (pow_ne_zero _ (hcoshU z hz)))
      (hdenU z hz)
    norm_num
  have hf_anal : AnalyticOnNhd ℂ
      (fun β : ℂ => correlationComplex G A (J : ℂ) 0 β) U := by
    intro z hz
    exact correlationComplex_analyticAt_beta G A (J : ℂ) 0 z (hZU z hz)
  have hg_anal : AnalyticOnNhd ℂ
      (fun β : ℂ =>
        htSubgraphSum G A (Complex.tanh (β * (J : ℂ))) /
          htSubgraphSum G (∅ : Finset ι) (Complex.tanh (β * (J : ℂ)))) U := by
    intro z hz
    exact (htSubgraphSum_tanh_analyticAt G A J z (hcoshU z hz)).div
      (htSubgraphSum_tanh_analyticAt G (∅ : Finset ι) J z (hcoshU z hz)) (hdenU z hz)
  have h_real_eq : ∀ t : ℝ, (t : ℂ) ∈ U →
      correlationComplex G A (J : ℂ) 0 (t : ℂ) =
        htSubgraphSum G A (Complex.tanh ((t : ℂ) * (J : ℂ))) /
          htSubgraphSum G (∅ : Finset ι) (Complex.tanh ((t : ℂ) * (J : ℂ))) := by
    intro t _
    have hreal := correlation_high_temp_expansion_h_zero_closed G J t A
    have hcorr := correlation_ofReal_eq_correlationComplex G (⟨J, 0, t⟩ : IsingParams ℝ) A
    simp only [Complex.ofReal_zero] at hcorr
    rw [← hcorr]
    rw [hreal]
    simp only [htSubgraphSum, Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_pow,
      Complex.ofReal_tanh, Complex.ofReal_mul]
    have hAfilter :
        G.edgeFinset.powerset.filter
          (fun X => ∀ v : ι,
            Even ((if v ∈ A then (1 : ℕ) else 0) + (X.filter (v ∈ ·)).card)) =
        G.edgeFinset.powerset.filter (fun X => oddBoundary X = A) := by
      apply Finset.filter_congr
      intro X _
      exact (oddBoundary_eq_iff_inline_even_filter A X).symm
    have h0filter :
        G.edgeFinset.powerset.filter
          (fun X => ∀ v : ι, Even (X.filter (v ∈ ·)).card) =
        G.edgeFinset.powerset.filter (fun X => oddBoundary X = (∅ : Finset ι)) := by
      apply Finset.filter_congr
      intro X _
      simpa using (oddBoundary_eq_iff_inline_even_filter (∅ : Finset ι) X).symm
    rw [hAfilter, h0filter]
  have h_frequently : ∃ᶠ z in 𝓝[≠] (0 : ℂ),
      correlationComplex G A (J : ℂ) 0 z =
        htSubgraphSum G A (Complex.tanh (z * (J : ℂ))) /
          htSubgraphSum G (∅ : Finset ι) (Complex.tanh (z * (J : ℂ))) := by
    have h_tendsto : Filter.Tendsto (fun k : ℕ => ((1 / (k + 1 : ℝ) : ℝ) : ℂ))
        Filter.atTop (𝓝 (0 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp tendsto_one_div_add_atTop_nhds_zero_nat
    have h_ne : ∀ k : ℕ, ((1 / (k + 1 : ℝ) : ℝ) : ℂ) ≠ 0 := fun k => by
      have hpos : (0 : ℝ) < 1 / (k + 1 : ℝ) := one_div_pos.mpr (by positivity)
      exact_mod_cast hpos.ne'
    have h_principal : Filter.Tendsto (fun k : ℕ => ((1 / (k + 1 : ℝ) : ℝ) : ℂ))
        Filter.atTop (𝓝[≠] (0 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨h_tendsto, Filter.Eventually.of_forall fun k => h_ne k⟩
    have h_evU : ∀ᶠ k : ℕ in Filter.atTop,
        ((1 / (k + 1 : ℝ) : ℝ) : ℂ) ∈ U :=
      h_tendsto.eventually (IsOpen.mem_nhds hUopen h0U)
    have h_freq_atTop : ∃ᶠ k : ℕ in Filter.atTop,
        correlationComplex G A (J : ℂ) 0 ((1 / (k + 1 : ℝ) : ℝ) : ℂ) =
          htSubgraphSum G A
              (Complex.tanh (((1 / (k + 1 : ℝ) : ℝ) : ℂ) * (J : ℂ))) /
            htSubgraphSum G (∅ : Finset ι)
              (Complex.tanh (((1 / (k + 1 : ℝ) : ℝ) : ℂ) * (J : ℂ))) := by
      exact (h_evU.mono fun k hk => h_real_eq _ hk).frequently
    exact h_principal.frequently h_freq_atTop
  exact hf_anal.eqOn_of_preconnected_of_frequently_eq hg_anal hUpre h0U h_frequently

/-- The `ball 0`-instance of the two-point ratio identity (corollary of the connected-domain
version), on the degree-uniform high-temperature disc. -/
private theorem correlationComplex_high_temp_expansion_h_zero_htSubgraphSum_on_uniform_ball
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (A : Finset ι) (J : ℝ) (Δ : ℕ) (hΔ : G.maxDegree ≤ Δ) :
    ∀ β ∈ Metric.ball (0 : ℂ) (twoPointHTUniformRadius Δ J),
      correlationComplex G A (J : ℂ) 0 β =
        htSubgraphSum G A (Complex.tanh (β * (J : ℂ))) /
          htSubgraphSum G (∅ : Finset ι) (Complex.tanh (β * (J : ℂ))) :=
  correlationComplex_high_temp_expansion_h_zero_htSubgraphSum_on_connected G A J Δ hΔ
    Metric.isOpen_ball
    (convex_ball (0 : ℂ) (twoPointHTUniformRadius Δ J)).isPreconnected
    (Metric.mem_ball_self (twoPointHTUniformRadius_pos Δ J))
    (fun z hz => twoPointHTUniformRadius_cosh_ne Δ J z hz)
    (fun z hz => twoPointHTUniformRadius_tanh_lt Δ J z hz)

/-- On the smaller KP threshold `r < 1/64`, the Mayer-difference coefficient is at most `8`. -/
private lemma uniform_kpCoeff_le_eight {r : ℝ} (h0 : 0 ≤ r) (hr : r < 1 / 64) :
    (1 / (1 - r)) * (1 - 4 * r / (1 - r) ^ 2)⁻¹ ^ 2 ≤ 8 := by
  have hr_half : r < 1 / 2 := by linarith
  have hden_pos : 0 < 1 - r := by linarith
  have hden_sq_pos : 0 < (1 - r) ^ 2 := pow_pos hden_pos 2
  have hden_sq_ge : (1 / 4 : ℝ) ≤ (1 - r) ^ 2 := by
    nlinarith [h0, hr_half]
  have hrho_le : 4 * r / (1 - r) ^ 2 ≤ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ hden_sq_pos]
    nlinarith [hden_sq_ge, hr]
  have hone_minus_rho_pos : 0 < 1 - 4 * r / (1 - r) ^ 2 := by linarith
  have hinv1 : 1 / (1 - r) ≤ (2 : ℝ) := by
    rw [div_le_iff₀ hden_pos]
    nlinarith [hr_half]
  have hinv2 : (1 - 4 * r / (1 - r) ^ 2)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_le_comm₀ hone_minus_rho_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hinv2_nonneg : 0 ≤ (1 - 4 * r / (1 - r) ^ 2)⁻¹ :=
    inv_nonneg.mpr (le_of_lt hone_minus_rho_pos)
  have hsquare : (1 - 4 * r / (1 - r) ^ 2)⁻¹ ^ 2 ≤ (4 : ℝ) := by
    nlinarith [mul_le_mul hinv2 hinv2 hinv2_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
  nlinarith [mul_le_mul hinv1 hsquare
    (by positivity : 0 ≤ (1 - 4 * r / (1 - r) ^ 2)⁻¹ ^ 2)
    (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]

/-- The elementary exponential identity used to package the per-component bound. -/
private lemma uniform_activity_exp_card_identity (R : ℝ) (n : ℕ) :
    R ^ n * Real.exp (8 * ((n : ℝ) + 1)) = Real.exp 8 * (R * Real.exp 8) ^ n := by
  rw [mul_add, mul_one]
  have hmul : 8 * (n : ℝ) = (n : ℝ) * 8 := by ring
  rw [hmul, Real.exp_add, Real.exp_nat_mul, mul_pow]
  ring

/-- **Degree-uniform two-point norm bound on a connected `cosh≠0` / activity-radius domain.**
On an open preconnected `U ∋ 0` where `cosh(βJ) ≠ 0` and `‖tanh(βJ)‖ < twoPointHTActivityRadius Δ`,
the two-point correlation is bounded by `twoPointHTBoundValue Δ`, uniformly over `U`. The `ball 0`
version is the corollary `…_of_high_temp_uniform_radius`. -/
theorem correlationComplex_two_point_norm_le_on_connected
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet] {i j : ι} (hij : i ≠ j)
    (J : ℝ) (Δ : ℕ) (hΔ : G.maxDegree ≤ Δ)
    {U : Set ℂ} (hUopen : IsOpen U) (hUpre : IsPreconnected U) (h0U : (0 : ℂ) ∈ U)
    (hcoshU : ∀ z ∈ U, Complex.cosh (z * (J : ℂ)) ≠ 0)
    (htanhU : ∀ z ∈ U, ‖Complex.tanh (z * (J : ℂ))‖ < twoPointHTActivityRadius Δ) :
    ∀ β ∈ U,
      ‖correlationComplex G ({i, j} : Finset ι) (J : ℂ) 0 β‖
        ≤ twoPointHTBoundValue Δ := by
  classical
  set R : ℝ := twoPointHTActivityRadius Δ with hRdef
  set A : ℝ := Real.exp 8 with hAdef
  set a : ℝ := R * Real.exp 8 with hadef
  have hRpos : 0 < R := by simpa [hRdef] using twoPointHTActivityRadius_pos Δ
  have hRnonneg : 0 ≤ R := le_of_lt hRpos
  have hApos : 0 < A := by
    rw [hAdef]
    exact Real.exp_pos 8
  have hAnonneg : 0 ≤ A := le_of_lt hApos
  have hanonneg : 0 ≤ a := by positivity
  have hΔcast : (G.maxDegree : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ
  have hRkpΔ : (Δ : ℝ) ^ 2 * (Real.exp 1 * R) < 1 / 64 := by
    simpa [hRdef] using twoPointHTActivityRadius_kp_threshold Δ
  have hRkpG64 : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R) < 1 / 64 := by
    have hle : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R)
        ≤ (Δ : ℝ) ^ 2 * (Real.exp 1 * R) := by gcongr
    exact lt_of_le_of_lt hle hRkpΔ
  have hRkpG6 : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R) < 1 / 6 := by
    linarith [hRkpG64]
  obtain ⟨hkpR, hρR⟩ := kp_tail_conditions_of_lt hRkpG6
  have hqΔ : a * ((Δ : ℝ) ^ 2) < 1 := by
    simpa [hRdef, hadef, mul_assoc, mul_left_comm, mul_comm] using
      twoPointHTActivityRadius_hq_threshold Δ
  have hqG : a * ((G.maxDegree : ℝ) ^ 2) < 1 := by
    have hle : a * ((G.maxDegree : ℝ) ^ 2) ≤ a * ((Δ : ℝ) ^ 2) := by gcongr
    exact lt_of_le_of_lt hle hqΔ
  have hdenΔpos : 0 < 1 - a * ((Δ : ℝ) ^ 2) := by linarith
  have hExp :=
    correlationComplex_high_temp_expansion_h_zero_htSubgraphSum_on_connected
      (G := G) ({i, j} : Finset ι) J Δ hΔ hUopen hUpre h0U hcoshU htanhU
  intro β hβ
  set t : ℂ := Complex.tanh (β * (J : ℂ)) with htdef
  have htRlt : ‖t‖ < R := htanhU β hβ
  have htRle : ‖t‖ ≤ R := le_of_lt htRlt
  have htz : t ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]
    exact htRlt
  have httG64 : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖t‖) < 1 / 64 := by
    have hle : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖t‖)
        ≤ (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R) := by gcongr
    exact lt_of_le_of_lt hle hRkpG64
  have httG6 : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖t‖) < 1 / 6 := by
    linarith [httG64]
  obtain ⟨hkpt, hρt⟩ := kp_tail_conditions_of_lt httG6
  have hper : ∀ C ∈ connectingComponents G i j,
      ‖t‖ ^ C.card * ‖htSubgraphSumAvoiding G C t / htSubgraphSum G (∅ : Finset ι) t‖
        ≤ A * a ^ C.card := by
    intro C hC
    have hCdata := hC
    rw [connectingComponents, Finset.mem_filter, Finset.mem_powerset] at hCdata
    have hCsub : C ⊆ G.edgeFinset := hCdata.1
    have hCne : C.Nonempty := hCdata.2.1
    have hCconn : IsEdgeConnected C := hCdata.2.2.1
    set rr : ℝ := (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖t‖) with hrrdef
    set κ : ℝ := (1 / (1 - rr)) * (1 - 4 * rr / (1 - rr) ^ 2)⁻¹ ^ 2 with hκdef
    have hrr_nonneg : 0 ≤ rr := by positivity
    have hκle : κ ≤ 8 := by
      simpa [κ, rr] using uniform_kpCoeff_le_eight hrr_nonneg (by simpa [rr] using httG64)
    have hdiff :=
      norm_mayerExpansionTermComplex_tsum_sub_Gavoid_le_support_card_complex
        (G := G) (C := C) (z := t) hkpt hρt
    have hdiff8 :
        ‖(∑' n : ℕ, mayerExpansionTermComplex G n t)
            - (∑' n : ℕ, mayerExpansionTermComplex (Gavoid G C) n t)‖
          ≤ 8 * ((polymerSupport C).card : ℝ) := by
      calc
        ‖(∑' n : ℕ, mayerExpansionTermComplex G n t)
            - (∑' n : ℕ, mayerExpansionTermComplex (Gavoid G C) n t)‖
          ≤ κ * ((polymerSupport C).card : ℝ) := by simpa [κ, rr] using hdiff
        _ ≤ 8 * ((polymerSupport C).card : ℝ) := by
          exact mul_le_mul_of_nonneg_right hκle (by positivity)
    have hratio :=
      norm_htSubgraphSumAvoiding_div_htSubgraphSum_empty_le
        (G := G) (C := C) (R := R) hRpos hkpR hρR htz
    have hsupp_nat : (polymerSupport C).card ≤ C.card + 1 :=
      polymerSupport_card_le_card_add_one_of_isEdgeConnected G hCsub hCne hCconn
    have hsupp_real : ((polymerSupport C).card : ℝ) ≤ (C.card : ℝ) + 1 := by
      exact_mod_cast hsupp_nat
    have hratio8 :
        ‖htSubgraphSumAvoiding G C t / htSubgraphSum G (∅ : Finset ι) t‖
          ≤ Real.exp (8 * ((C.card : ℝ) + 1)) := by
      calc
        ‖htSubgraphSumAvoiding G C t / htSubgraphSum G (∅ : Finset ι) t‖
          ≤ Real.exp ‖(∑' n : ℕ, mayerExpansionTermComplex G n t)
              - (∑' n : ℕ, mayerExpansionTermComplex (Gavoid G C) n t)‖ := hratio
        _ ≤ Real.exp (8 * ((polymerSupport C).card : ℝ)) := by
          exact Real.exp_le_exp.mpr hdiff8
        _ ≤ Real.exp (8 * ((C.card : ℝ) + 1)) := by
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsupp_real (by norm_num))
    have htpow : ‖t‖ ^ C.card ≤ R ^ C.card :=
      pow_le_pow_left₀ (norm_nonneg t) htRle C.card
    calc
      ‖t‖ ^ C.card * ‖htSubgraphSumAvoiding G C t / htSubgraphSum G (∅ : Finset ι) t‖
        ≤ R ^ C.card * Real.exp (8 * ((C.card : ℝ) + 1)) := by
          exact mul_le_mul htpow hratio8 (norm_nonneg _) (pow_nonneg hRnonneg _)
      _ = A * a ^ C.card := by
          rw [hAdef, hadef]
          exact uniform_activity_exp_card_identity R C.card
  have hratioBound :=
    twoPointRatio_norm_le_geometric (G := G) (i := i) (j := j) hij t A a hAnonneg hanonneg hper hqG
  have hcompare :
      A / (1 - a * ((G.maxDegree : ℝ) ^ 2)) ≤ twoPointHTBoundValue Δ := by
    have hgΔ : a * ((G.maxDegree : ℝ) ^ 2) ≤ a * ((Δ : ℝ) ^ 2) := by gcongr
    have hdenle : 1 - a * ((Δ : ℝ) ^ 2) ≤ 1 - a * ((G.maxDegree : ℝ) ^ 2) := by
      linarith
    have hinv : (1 - a * ((G.maxDegree : ℝ) ^ 2))⁻¹ ≤
        (1 - a * ((Δ : ℝ) ^ 2))⁻¹ := by
      exact inv_anti₀ hdenΔpos hdenle
    have hmul : A * (1 - a * ((G.maxDegree : ℝ) ^ 2))⁻¹ ≤
        A * (1 - a * ((Δ : ℝ) ^ 2))⁻¹ :=
      mul_le_mul_of_nonneg_left hinv hAnonneg
    calc
      A / (1 - a * ((G.maxDegree : ℝ) ^ 2))
          = A * (1 - a * ((G.maxDegree : ℝ) ^ 2))⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ A * (1 - a * ((Δ : ℝ) ^ 2))⁻¹ := hmul
      _ = twoPointHTBoundValue Δ := by
        rw [twoPointHTBoundValue, hAdef, hadef, hRdef, div_eq_mul_inv]
  calc
    ‖correlationComplex G ({i, j} : Finset ι) (J : ℂ) 0 β‖
      = ‖htSubgraphSum G ({i, j} : Finset ι) t / htSubgraphSum G (∅ : Finset ι) t‖ := by
        rw [show correlationComplex G ({i, j} : Finset ι) (J : ℂ) 0 β =
          htSubgraphSum G ({i, j} : Finset ι) t / htSubgraphSum G (∅ : Finset ι) t from hExp hβ]
    _ ≤ A / (1 - a * ((G.maxDegree : ℝ) ^ 2)) := hratioBound
    _ ≤ twoPointHTBoundValue Δ := hcompare

/-- The `ball 0`-instance of the two-point norm bound (corollary of the connected-domain version),
on the degree-uniform high-temperature disc. -/
theorem correlationComplex_two_point_norm_le_of_high_temp_uniform_radius
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet] {i j : ι} (hij : i ≠ j)
    (J : ℝ) (Δ : ℕ) (hΔ : G.maxDegree ≤ Δ) :
    ∀ β ∈ Metric.ball (0 : ℂ) (twoPointHTUniformRadius Δ J),
      ‖correlationComplex G ({i, j} : Finset ι) (J : ℂ) 0 β‖
        ≤ twoPointHTBoundValue Δ :=
  correlationComplex_two_point_norm_le_on_connected G hij J Δ hΔ
    Metric.isOpen_ball
    (convex_ball (0 : ℂ) (twoPointHTUniformRadius Δ J)).isPreconnected
    (Metric.mem_ball_self (twoPointHTUniformRadius_pos Δ J))
    (fun z hz => twoPointHTUniformRadius_cosh_ne Δ J z hz)
    (fun z hz => twoPointHTUniformRadius_tanh_lt Δ J z hz)

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ## Lattice-exhaustion uniform bound and final Vitali capstone -/

/-- The per-stage two-point complex correlations along a lattice exhaustion are uniformly bounded
on the degree-uniform high-temperature beta ball. -/
theorem correlationComplexAlongExhaustion_two_point_norm_le_uniform
    (d : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) {i j : Fin d → ℤ} (hij : i ≠ j) :
    ∀ n : ℕ, ∀ β ∈ Metric.ball (0 : ℂ) (twoPointHTUniformRadius (2 * d) J),
      ‖correlationComplexAlongExhaustion (latticeGraph d) Λ ({i, j} : Finset (Fin d → ℤ))
          (J : ℂ) 0 β n‖ ≤ twoPointHTBoundValue (2 * d) := by
  classical
  intro n β hβ
  unfold correlationComplexAlongExhaustion
  by_cases hsub : ({i, j} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
  · simp only [hsub, dif_pos]
    have hi : i ∈ Λ.volume n := hsub (by simp)
    have hj : j ∈ Λ.volume n := hsub (by simp)
    have hp :
        liftFinset ({i, j} : Finset (Fin d → ℤ)) hsub =
          ({⟨i, hi⟩, ⟨j, hj⟩} : Finset (↑(Λ.volume n) : Type _)) :=
      liftFinset_pair hsub hi hj
    have hij' : (⟨i, hi⟩ : ↑(Λ.volume n)) ≠ ⟨j, hj⟩ := by
      intro h
      exact hij (Subtype.mk.inj h)
    have hdeg :
        (inducedGraph (latticeGraph d) (Λ.volume n)).maxDegree ≤ 2 * d :=
      induced_latticeGraph_maxDegree_le d (Λ.volume n)
    have hbound :=
      correlationComplex_two_point_norm_le_of_high_temp_uniform_radius
        (G := inducedGraph (latticeGraph d) (Λ.volume n))
        (i := (⟨i, hi⟩ : ↑(Λ.volume n))) (j := ⟨j, hj⟩)
        hij' J (2 * d) hdeg β hβ
    simpa [hp] using hbound
  · rw [dif_neg hsub, norm_zero]
    exact le_of_lt (twoPointHTBoundValue_pos (2 * d))

/-- **Infinite-volume lattice two-point correlation analyticity at high temperature.** -/
theorem correlationInfinite_latticeGraph_two_point_analytic_high_temp
    (d : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    (J : ℝ) (hJ : 0 ≤ J) {i j : Fin d → ℤ} (hij : i ≠ j) :
    ∃ r > 0, ∀ β : ℝ, 0 < β → β < r →
      ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball (0 : ℂ) r) ∧
        TendstoLocallyUniformlyOn
          (fun n z => correlationComplexAlongExhaustion (latticeGraph d) Λ
            ({i, j} : Finset (Fin d → ℤ)) (J : ℂ) 0 z n)
          f Filter.atTop (Metric.ball (0 : ℂ) r) ∧
        f (β : ℂ) =
          ((correlationInfinite (latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
              ({i, j} : Finset (Fin d → ℤ)) : ℝ) : ℂ) := by
  classical
  obtain ⟨rZ, hrZpos, hZraw⟩ :=
    partitionFunctionComplexAlongExhaustion_ne_zero_on_ball_uniform_latticeGraph d Λ J
  set rHT : ℝ := twoPointHTUniformRadius (2 * d) J with hrHT
  set r : ℝ := min rHT rZ with hr
  have hrHTpos : 0 < rHT := by simpa [hrHT] using twoPointHTUniformRadius_pos (2 * d) J
  have hrpos : 0 < r := by
    rw [hr]
    exact lt_min hrHTpos hrZpos
  refine ⟨r, hrpos, ?_⟩
  intro β hβpos hβlt
  set U : Set ℂ := Metric.ball (0 : ℂ) r with hU
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hUpre : IsPreconnected U := (convex_ball (0 : ℂ) r).isPreconnected
  have hβU : (β : ℂ) ∈ U := by
    rw [hU, Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hβpos]
    exact hβlt
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
    ⟨hJ, le_rfl, hβpos⟩
  have hZ : ∀ n, ∀ z ∈ U,
      partitionFunctionComplexAlongExhaustion (latticeGraph d) Λ
        ((⟨J, 0, β⟩ : IsingParams ℝ).J : ℂ)
        ((⟨J, 0, β⟩ : IsingParams ℝ).h : ℂ) z n ≠ 0 := by
    intro n z hz
    have hzdist : dist z 0 < r := by
      simpa [hU] using Metric.mem_ball.mp hz
    have hzZ : z ∈ Metric.ball (0 : ℂ) rZ := by
      refine Metric.mem_ball.mpr (lt_of_lt_of_le hzdist ?_)
      rw [hr]
      exact min_le_right _ _
    simpa using hZraw n z hzZ
  have hbdd : ∀ z ∈ U, ∃ ρ M : ℝ, 0 < ρ ∧ Metric.ball z ρ ⊆ U ∧
      ∀ n, ∀ w ∈ Metric.ball z ρ,
        ‖correlationComplexAlongExhaustion (latticeGraph d) Λ
            ({i, j} : Finset (Fin d → ℤ)) ((⟨J, 0, β⟩ : IsingParams ℝ).J : ℂ)
            ((⟨J, 0, β⟩ : IsingParams ℝ).h : ℂ) w n‖ ≤
          M := by
    intro z hz
    have hz_norm : ‖z‖ < r := by
      have hzdist : dist z 0 < r := by simpa [hU] using Metric.mem_ball.mp hz
      simpa [dist_zero_right] using hzdist
    refine ⟨(r - ‖z‖) / 2, twoPointHTBoundValue (2 * d), by linarith, ?_, ?_⟩
    · intro w hw
      have hwz : dist w z < (r - ‖z‖) / 2 := Metric.mem_ball.mp hw
      have hw_norm : ‖w‖ < r := by
        calc
          ‖w‖ = dist w 0 := by simp [dist_zero_right]
          _ ≤ dist w z + dist z 0 := dist_triangle w z 0
          _ = dist w z + ‖z‖ := by rw [dist_zero_right]
          _ < (r - ‖z‖) / 2 + ‖z‖ := by linarith
          _ < r := by linarith
      rw [hU, Metric.mem_ball, dist_zero_right]
      exact hw_norm
    · intro n w hw
      have hwU : w ∈ U := by
        exact (show Metric.ball z ((r - ‖z‖) / 2) ⊆ U from by
          intro y hy
          have hyz : dist y z < (r - ‖z‖) / 2 := Metric.mem_ball.mp hy
          have hy_norm : ‖y‖ < r := by
            calc
              ‖y‖ = dist y 0 := by simp [dist_zero_right]
              _ ≤ dist y z + dist z 0 := dist_triangle y z 0
              _ = dist y z + ‖z‖ := by rw [dist_zero_right]
              _ < (r - ‖z‖) / 2 + ‖z‖ := by linarith
              _ < r := by linarith
          rw [hU, Metric.mem_ball, dist_zero_right]
          exact hy_norm) hw
      have hwHT : w ∈ Metric.ball (0 : ℂ) (twoPointHTUniformRadius (2 * d) J) := by
        have hwdist : dist w 0 < r := by simpa [hU] using Metric.mem_ball.mp hwU
        refine Metric.mem_ball.mpr (lt_of_lt_of_le hwdist ?_)
        rw [hr, hrHT]
        exact min_le_left _ _
      simpa using
        correlationComplexAlongExhaustion_two_point_norm_le_uniform
          d Λ J hij n w hwHT
  obtain ⟨f, hfdiff, hconv, hident⟩ :=
    correlationComplexAlongExhaustion_analytic_of_volume_uniform_bound
      (G := latticeGraph d) (Λ := Λ)
      (p := (⟨J, 0, β⟩ : IsingParams ℝ)) hf
      ({i, j} : Finset (Fin d → ℤ))
      hUopen hUpre hβU hZ hbdd
  refine ⟨f, ?_, ?_, ?_⟩
  · simpa [hU] using hfdiff
  · simpa [hU] using hconv
  · simpa using hident

end Ambient

end IsingModel
