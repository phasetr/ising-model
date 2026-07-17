import IsingModel.ComplexAnalyticity.Basic
import IsingModel.ClusterExpansion.Families.SandwichBounds
import IsingModel.ClusterExpansion.RegularityHZero
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Complex partition function high-temperature polymer-family expansion

This module hosts the complex extension of the high-temperature polymer-family
expansion of the partition function. The base case at real parameters
(`partitionFunctionComplex_high_temp_expansion_h_zero_polymer_family_at_real`)
is the analytic-continuation seed for the general `(J, β) : ℂ × ℂ` identity
toward the volume-uniform `Z_ℂ` lower bound for the Lemma 17.5.2 `hZ` provider
(Issue #3044) via the cluster-expansion route (Issue #3054).
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Complex
open scoped Topology

/-- **Complex `Z` high-temperature polymer-family expansion at real parameters**
(Issue #3054): the complex partition function at real `J, β` (coerced to `ℂ`)
admits the same factorization as the real `Z` —
`partitionFunctionComplex G ↑J 0 ↑β = 2^|ι| · Complex.cosh(β·J)^|E| ·
∑_Γ ∏_P Complex.tanh(β·J)^|P|`.

Cast of `partitionFunction_high_temp_expansion_h_zero_polymer_family` via
`partitionFunction_ofReal_eq_partitionFunctionComplex` and the standard
`Complex.ofReal_*` casts. This is the analytic-continuation seed for the
general-`(J, β) : ℂ × ℂ` complex high-temperature expansion (still to be
established by identity theorem). -/
theorem partitionFunctionComplex_high_temp_expansion_h_zero_polymer_family_at_real
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) :
    partitionFunctionComplex G (J : ℂ) 0 (β : ℂ) =
      (2 : ℂ) ^ Fintype.card ι *
        Complex.cosh ((β : ℂ) * (J : ℂ)) ^ G.edgeFinset.card *
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Complex.tanh ((β : ℂ) * (J : ℂ)) ^ P.card := by
  have hreal :
      partitionFunction G ⟨J, 0, β⟩ =
        (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
          ∑ Γ ∈ vdCompatiblePolymerFamilies G,
            ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
    partitionFunction_high_temp_expansion_h_zero_polymer_family G J β
  have hcast :
      ((partitionFunction G ⟨J, 0, β⟩ : ℝ) : ℂ) =
        partitionFunctionComplex G (J : ℂ) ((0 : ℝ) : ℂ) (β : ℂ) :=
    partitionFunction_ofReal_eq_partitionFunctionComplex G ⟨J, 0, β⟩
  -- Rewrite (0 : ℝ) : ℂ as (0 : ℂ).
  rw [show ((0 : ℝ) : ℂ) = (0 : ℂ) from Complex.ofReal_zero] at hcast
  rw [← hcast]
  -- Cast the real identity to ℂ.
  have hcast_id := congrArg (fun x : ℝ => (x : ℂ)) hreal
  simp only at hcast_id
  rw [hcast_id]
  push_cast
  rfl

/-- **Complex `Z` high-temperature polymer-family expansion holds eventually
near `β = 0` for real `J`** (Issue #3054, analytic-continuation upgrade of
`partitionFunctionComplex_high_temp_expansion_h_zero_polymer_family_at_real`):
for fixed real coupling `J`, the complex high-temperature expansion holds in a
complex neighborhood of `β = 0`.

Proof via the identity theorem on a small open disc `U = Metric.ball 0 r`:
both LHS and RHS are analytic on `U` (LHS entire, RHS analytic where
`Complex.cosh (β·J) ≠ 0` — choose `r` so that this holds on `U`); they agree
at the real points `(1/(n+1) : ℝ) : ℂ` (cast of the real identity, PR #3063),
which accumulate to `0`. -/
theorem partitionFunctionComplex_high_temp_expansion_h_zero_polymer_family_near_zero_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) :
    ∀ᶠ β : ℂ in 𝓝 (0 : ℂ),
      partitionFunctionComplex G (J : ℂ) 0 β =
        (2 : ℂ) ^ Fintype.card ι *
          Complex.cosh (β * (J : ℂ)) ^ G.edgeFinset.card *
          ∑ Γ ∈ vdCompatiblePolymerFamilies G,
            ∏ P ∈ Γ, Complex.tanh (β * (J : ℂ)) ^ P.card := by
  classical
  -- Pick a complex disc around 0 where Complex.cosh (β·J) ≠ 0.
  have hcont_cosh : Continuous (fun β : ℂ => Complex.cosh (β * (J : ℂ))) :=
    Complex.continuous_cosh.comp (continuous_id.mul continuous_const)
  have h_cosh0 : Complex.cosh ((0 : ℂ) * (J : ℂ)) ≠ 0 := by
    rw [zero_mul, Complex.cosh_zero]; exact one_ne_zero
  have h_cosh_ev : ∀ᶠ β in 𝓝 (0 : ℂ), Complex.cosh (β * (J : ℂ)) ≠ 0 :=
    hcont_cosh.continuousAt.eventually_ne h_cosh0
  rw [Metric.eventually_nhds_iff_ball] at h_cosh_ev
  obtain ⟨r, hr, h_cosh_ne⟩ := h_cosh_ev
  -- The identity theorem on the open disc `U := Metric.ball 0 r`.
  set f : ℂ → ℂ := fun β => partitionFunctionComplex G (J : ℂ) 0 β with hf_def
  set g : ℂ → ℂ := fun β => (2 : ℂ) ^ Fintype.card ι *
        Complex.cosh (β * (J : ℂ)) ^ G.edgeFinset.card *
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Complex.tanh (β * (J : ℂ)) ^ P.card with hg_def
  set U : Set ℂ := Metric.ball (0 : ℂ) r with hU_def
  have hU_open : IsOpen U := Metric.isOpen_ball
  have hU_preconn : IsPreconnected U :=
    (convex_ball (0 : ℂ) r).isPreconnected
  have h_zero_in_U : (0 : ℂ) ∈ U := Metric.mem_ball_self hr
  have hf_anal : AnalyticOnNhd ℂ f U := by
    intro β _
    exact partitionFunctionComplex_analyticAt_beta G (J : ℂ) 0 β
  have hg_anal : AnalyticOnNhd ℂ g U := by
    intro β hβ
    have hcosh_β : Complex.cosh (β * (J : ℂ)) ≠ 0 := h_cosh_ne β hβ
    have h_poly_tanh :
        AnalyticAt ℂ (fun β' : ℂ =>
          ∑ Γ ∈ vdCompatiblePolymerFamilies G,
            ∏ P ∈ Γ, Complex.tanh (β' * (J : ℂ)) ^ P.card) β :=
      vdPolymerFamilies_sum_tanh_analyticAt_complex_beta G (J : ℂ) β hcosh_β
    have h_cosh_pow :
        AnalyticAt ℂ (fun β' : ℂ =>
          Complex.cosh (β' * (J : ℂ)) ^ G.edgeFinset.card) β := by
      have h_mul : AnalyticAt ℂ (fun β' : ℂ => β' * (J : ℂ)) β :=
        analyticAt_id.mul analyticAt_const
      have h_cosh_at : AnalyticAt ℂ Complex.cosh (β * (J : ℂ)) :=
        Complex.analyticOnNhd_cosh (s := Set.univ) (β * (J : ℂ)) (Set.mem_univ _)
      have h_comp : AnalyticAt ℂ (Complex.cosh ∘ (fun β' : ℂ => β' * (J : ℂ))) β := by
        refine AnalyticAt.comp ?_ h_mul
        exact h_cosh_at
      exact h_comp.pow _
    have h_two_pow : AnalyticAt ℂ
        (fun _ : ℂ => (2 : ℂ) ^ Fintype.card ι) β := analyticAt_const
    exact (h_two_pow.mul h_cosh_pow).mul h_poly_tanh
  -- f and g agree at real points β = (1/(n+1) : ℝ) : ℂ inside U.
  have h_real_eq : ∀ x : ℝ, f (x : ℂ) = g (x : ℂ) := fun x => by
    simp only [hf_def, hg_def]
    exact partitionFunctionComplex_high_temp_expansion_h_zero_polymer_family_at_real G J x
  -- Build the accumulation: f = g at 1/(n+1) : ℂ which converge to 0 in U.
  have h_frequently : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = g z := by
    have h_tendsto : Filter.Tendsto
        (fun n : ℕ => ((1 / (n + 1 : ℝ) : ℝ) : ℂ)) Filter.atTop (𝓝 (0 : ℂ)) := by
      have h1 : Filter.Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ) : ℝ))
          Filter.atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
      exact (Complex.continuous_ofReal.tendsto _).comp h1
    have h_ne : ∀ n : ℕ, ((1 / (n + 1 : ℝ) : ℝ) : ℂ) ≠ 0 := fun n => by
      have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) :=
        one_div_pos.mpr (by positivity)
      exact_mod_cast hpos.ne'
    have h_principal : Filter.Tendsto
        (fun n : ℕ => ((1 / (n + 1 : ℝ) : ℝ) : ℂ)) Filter.atTop (𝓝[≠] (0 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨h_tendsto, Filter.Eventually.of_forall (fun n => h_ne n)⟩
    have h_freq_atTop :
        ∃ᶠ n : ℕ in Filter.atTop, f (((1 / ((n : ℝ) + 1) : ℝ)) : ℂ) =
            g (((1 / ((n : ℝ) + 1) : ℝ)) : ℂ) :=
      (Filter.Eventually.of_forall (fun n : ℕ => h_real_eq _)).frequently
    exact h_principal.frequently h_freq_atTop
  have h_eqOn : Set.EqOn f g U :=
    hf_anal.eqOn_of_preconnected_of_frequently_eq hg_anal hU_preconn h_zero_in_U h_frequently
  -- Convert EqOn to ∀ᶠ form.
  rw [Metric.eventually_nhds_iff_ball]
  exact ⟨r, hr, fun β hβ => h_eqOn hβ⟩

/-- **Complex partition function is bounded below by `ε > 0` on a closed
complex ball at `β = 0` for fixed real coupling `J`** (Issue #3054). Composition
of the analytic-continued high-temp identity
(`partitionFunctionComplex_high_temp_expansion_h_zero_polymer_family_near_zero_beta`)
with the polymer-tanh-sum closedBall lower bound
(`vdPolymerFamilies_sum_tanh_complex_norm_ge_eps_on_closedBall_at_zero_beta`)
and `cosh` continuity near `β = 0` (giving `|Complex.cosh (β·J)| > 0`).

For each `(G, J : ℝ)` there exist `r > 0, ε > 0` such that
`ε ≤ ‖partitionFunctionComplex G (J:ℂ) 0 β‖` for all
`β ∈ Metric.closedBall (0 : ℂ) r`. The per-fixed-volume version of the Lemma
17.5.2 `hZ` provider via the cluster-expansion route; both `r` and `ε` depend on
`G` (volume `ι`) and `J`. Volume-uniformity remains the research-level open
hard core. -/
theorem partitionFunctionComplex_norm_ge_eps_on_closedBall_at_zero_beta_real_J
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) :
    ∃ r > 0, ∃ ε > 0, ∀ β ∈ Metric.closedBall (0 : ℂ) r,
      ε ≤ ‖partitionFunctionComplex G (J : ℂ) 0 β‖ := by
  classical
  -- Pick a radius r₁ > 0 and ε₁ > 0 with polymer-tanh-sum norm ≥ ε₁ on closedBall (0) r₁.
  obtain ⟨r₁, hr₁, ε₁, hε₁, h_poly⟩ :=
    vdPolymerFamilies_sum_tanh_complex_norm_ge_eps_on_closedBall_at_zero_beta G (J : ℂ)
  -- Pick a radius r₂ > 0 with cosh(β·J) ≠ 0 on Metric.ball (0) r₂.
  have hcont_cosh : Continuous (fun β : ℂ => Complex.cosh (β * (J : ℂ))) :=
    Complex.continuous_cosh.comp (continuous_id.mul continuous_const)
  have h_cosh0 : Complex.cosh ((0 : ℂ) * (J : ℂ)) ≠ 0 := by
    rw [zero_mul, Complex.cosh_zero]; exact one_ne_zero
  have h_cosh_ev : ∀ᶠ β in 𝓝 (0 : ℂ), Complex.cosh (β * (J : ℂ)) ≠ 0 :=
    hcont_cosh.continuousAt.eventually_ne h_cosh0
  rw [Metric.eventually_nhds_iff_ball] at h_cosh_ev
  obtain ⟨r₂, hr₂, h_cosh_ne⟩ := h_cosh_ev
  -- Identity holds eventually near 0; extract a ball-form radius r₃.
  have h_id := partitionFunctionComplex_high_temp_expansion_h_zero_polymer_family_near_zero_beta G J
  rw [Metric.eventually_nhds_iff_ball] at h_id
  obtain ⟨r₃, hr₃, h_id_ball⟩ := h_id
  -- Compactness for cosh: get a min lower bound on closedBall (0) (min(r₂,r₃)/2).
  set r₄ : ℝ := min r₂ r₃ / 2 with hr₄_def
  have hr₄_pos : 0 < r₄ := by
    have : 0 < min r₂ r₃ := lt_min hr₂ hr₃
    simp only [hr₄_def]; linarith
  have hr₄_lt_r2 : r₄ < r₂ := by
    have : min r₂ r₃ ≤ r₂ := min_le_left _ _
    simp only [hr₄_def]; linarith
  have hr₄_lt_r3 : r₄ < r₃ := by
    have : min r₂ r₃ ≤ r₃ := min_le_right _ _
    simp only [hr₄_def]; linarith
  have h_sub2 : Metric.closedBall (0 : ℂ) r₄ ⊆ Metric.ball (0 : ℂ) r₂ := by
    intro β hβ
    rw [Metric.mem_closedBall] at hβ
    rw [Metric.mem_ball]; linarith
  have h_sub3 : Metric.closedBall (0 : ℂ) r₄ ⊆ Metric.ball (0 : ℂ) r₃ := by
    intro β hβ
    rw [Metric.mem_closedBall] at hβ
    rw [Metric.mem_ball]; linarith
  -- Min of |cosh(β·J)| on closedBall (0) r₄.
  have h_norm_cosh_cont :
      ContinuousOn (fun β : ℂ => ‖Complex.cosh (β * (J : ℂ))‖)
        (Metric.closedBall (0 : ℂ) r₄) := hcont_cosh.continuousOn.norm
  have h_compact : IsCompact (Metric.closedBall (0 : ℂ) r₄) :=
    isCompact_closedBall _ _
  have h_nonempty : (Metric.closedBall (0 : ℂ) r₄).Nonempty :=
    ⟨0, Metric.mem_closedBall_self hr₄_pos.le⟩
  obtain ⟨β_min, hβ_min, h_min⟩ :=
    h_compact.exists_isMinOn h_nonempty h_norm_cosh_cont
  set δ := ‖Complex.cosh (β_min * (J : ℂ))‖
  have h_cosh_ne_min : Complex.cosh (β_min * (J : ℂ)) ≠ 0 :=
    h_cosh_ne β_min (h_sub2 hβ_min)
  have h_δ_pos : 0 < δ := norm_pos_iff.mpr h_cosh_ne_min
  -- Take the further min of r₄ and r₁.
  set r : ℝ := min r₁ r₄ / 2 with hr_def
  have hmin_pos : 0 < min r₁ r₄ := lt_min hr₁ hr₄_pos
  have hr_pos : 0 < r := by simp only [hr_def]; linarith
  have hr_lt_r1 : r < r₁ := by
    have : min r₁ r₄ ≤ r₁ := min_le_left _ _
    simp only [hr_def]; linarith
  have hr_le_r4 : r ≤ r₄ := by
    have : min r₁ r₄ ≤ r₄ := min_le_right _ _
    simp only [hr_def]; linarith
  refine ⟨r, hr_pos, (2 : ℝ) ^ Fintype.card ι * δ ^ G.edgeFinset.card * ε₁,
    by positivity, ?_⟩
  intro β hβ
  rw [Metric.mem_closedBall] at hβ
  -- β ∈ closedBall (0) r, hence in closedBall (0) r₁ and closedBall (0) r₄.
  have hβ_b1 : β ∈ Metric.closedBall (0 : ℂ) r₁ := by
    rw [Metric.mem_closedBall]; linarith
  have hβ_b4 : β ∈ Metric.closedBall (0 : ℂ) r₄ := by
    rw [Metric.mem_closedBall]; linarith
  have hβ_b3 : β ∈ Metric.ball (0 : ℂ) r₃ := h_sub3 hβ_b4
  -- Use the identity.
  have h_eq := h_id_ball β hβ_b3
  rw [h_eq]
  -- ‖2^|ι| · cosh^|E| · sum‖ = 2^|ι| · |cosh|^|E| · |sum| (using 2^|ι| ≥ 0).
  simp only [norm_mul, norm_pow, Complex.norm_ofNat]
  have h_sum_norm :=
    h_poly β hβ_b1
  have h_cosh_norm : δ ≤ ‖Complex.cosh (β * (J : ℂ))‖ := h_min hβ_b4
  have h_two_pos : (0 : ℝ) ≤ (2 : ℝ) ^ Fintype.card ι := by positivity
  have h_cosh_pow_pos : (0 : ℝ) ≤ ‖Complex.cosh (β * (J : ℂ))‖ ^ G.edgeFinset.card := by
    positivity
  have h_eps_pos : (0 : ℝ) ≤ ε₁ := le_of_lt hε₁
  have h_two_cosh_pos : (0 : ℝ) ≤
      (2 : ℝ) ^ Fintype.card ι *
        ‖Complex.cosh (β * (J : ℂ))‖ ^ G.edgeFinset.card := by
    positivity
  -- Combine: 2^|ι| · δ^|E| · ε₁ ≤ 2^|ι| · |cosh(β·J)|^|E| · |sum|.
  have h_step1 : (2 : ℝ) ^ Fintype.card ι * δ ^ G.edgeFinset.card * ε₁ ≤
      (2 : ℝ) ^ Fintype.card ι * ‖Complex.cosh (β * (J : ℂ))‖ ^ G.edgeFinset.card * ε₁ := by
    apply mul_le_mul_of_nonneg_right _ h_eps_pos
    apply mul_le_mul_of_nonneg_left _ h_two_pos
    exact pow_le_pow_left₀ (le_of_lt h_δ_pos) h_cosh_norm _
  have h_step2 : (2 : ℝ) ^ Fintype.card ι * ‖Complex.cosh (β * (J : ℂ))‖ ^ G.edgeFinset.card * ε₁ ≤
      (2 : ℝ) ^ Fintype.card ι * ‖Complex.cosh (β * (J : ℂ))‖ ^ G.edgeFinset.card *
        ‖∑ Γ ∈ vdCompatiblePolymerFamilies G,
            ∏ P ∈ Γ, Complex.tanh (β * (J : ℂ)) ^ P.card‖ :=
    mul_le_mul_of_nonneg_left h_sum_norm h_two_cosh_pos
  linarith [h_step1, h_step2]

/-- **Complex `Z` high-temperature polymer-family expansion holds eventually
near `J = 0` for real `β`** (Issue #3054, `J`-direction analogue of
`partitionFunctionComplex_high_temp_expansion_h_zero_polymer_family_near_zero_beta`):
for fixed real `β`, the complex high-temperature expansion holds in a complex
neighborhood of `J = 0`.

Proof via the identity theorem on a small open disc `U = Metric.ball 0 r`:
both LHS and RHS are analytic on `U` (LHS entire in `J`, RHS analytic where
`Complex.cosh ((β:ℂ)·J) ≠ 0`); they agree at the real points
`((1/(n+1) : ℝ) : ℂ)` (cast of the at-real seed, PR #3063), which accumulate
to `0`. -/
theorem partitionFunctionComplex_high_temp_expansion_h_zero_polymer_family_near_zero_J
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) :
    ∀ᶠ J : ℂ in 𝓝 (0 : ℂ),
      partitionFunctionComplex G J 0 (β : ℂ) =
        (2 : ℂ) ^ Fintype.card ι *
          Complex.cosh ((β : ℂ) * J) ^ G.edgeFinset.card *
          ∑ Γ ∈ vdCompatiblePolymerFamilies G,
            ∏ P ∈ Γ, Complex.tanh ((β : ℂ) * J) ^ P.card := by
  classical
  -- Pick a complex disc around 0 where Complex.cosh ((β:ℂ)·J) ≠ 0.
  have hcont_cosh : Continuous (fun J : ℂ => Complex.cosh ((β : ℂ) * J)) :=
    Complex.continuous_cosh.comp (continuous_const.mul continuous_id)
  have h_cosh0 : Complex.cosh ((β : ℂ) * (0 : ℂ)) ≠ 0 := by
    rw [mul_zero, Complex.cosh_zero]; exact one_ne_zero
  have h_cosh_ev : ∀ᶠ J in 𝓝 (0 : ℂ), Complex.cosh ((β : ℂ) * J) ≠ 0 :=
    hcont_cosh.continuousAt.eventually_ne h_cosh0
  rw [Metric.eventually_nhds_iff_ball] at h_cosh_ev
  obtain ⟨r, hr, h_cosh_ne⟩ := h_cosh_ev
  -- The identity theorem on the open disc `U := Metric.ball 0 r`.
  set f : ℂ → ℂ := fun J => partitionFunctionComplex G J 0 (β : ℂ) with hf_def
  set g : ℂ → ℂ := fun J => (2 : ℂ) ^ Fintype.card ι *
        Complex.cosh ((β : ℂ) * J) ^ G.edgeFinset.card *
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Complex.tanh ((β : ℂ) * J) ^ P.card with hg_def
  set U : Set ℂ := Metric.ball (0 : ℂ) r with hU_def
  have hU_preconn : IsPreconnected U :=
    (convex_ball (0 : ℂ) r).isPreconnected
  have h_zero_in_U : (0 : ℂ) ∈ U := Metric.mem_ball_self hr
  have hf_anal : AnalyticOnNhd ℂ f U := by
    intro J _
    exact partitionFunctionComplex_analyticAt_J G 0 (β : ℂ) J
  have hg_anal : AnalyticOnNhd ℂ g U := by
    intro J hJ
    have hcosh_J : Complex.cosh ((β : ℂ) * J) ≠ 0 := h_cosh_ne J hJ
    have h_poly_tanh :
        AnalyticAt ℂ (fun J' : ℂ =>
          ∑ Γ ∈ vdCompatiblePolymerFamilies G,
            ∏ P ∈ Γ, Complex.tanh ((β : ℂ) * J') ^ P.card) J :=
      vdPolymerFamilies_sum_tanh_analyticAt_complex_J G (β : ℂ) J hcosh_J
    have h_cosh_pow :
        AnalyticAt ℂ (fun J' : ℂ =>
          Complex.cosh ((β : ℂ) * J') ^ G.edgeFinset.card) J := by
      have h_mul : AnalyticAt ℂ (fun J' : ℂ => (β : ℂ) * J') J :=
        analyticAt_const.mul analyticAt_id
      have h_cosh_at : AnalyticAt ℂ Complex.cosh ((β : ℂ) * J) :=
        Complex.analyticOnNhd_cosh (s := Set.univ) ((β : ℂ) * J) (Set.mem_univ _)
      have h_comp : AnalyticAt ℂ (Complex.cosh ∘ (fun J' : ℂ => (β : ℂ) * J')) J := by
        refine AnalyticAt.comp ?_ h_mul
        exact h_cosh_at
      exact h_comp.pow _
    have h_two_pow : AnalyticAt ℂ
        (fun _ : ℂ => (2 : ℂ) ^ Fintype.card ι) J := analyticAt_const
    exact (h_two_pow.mul h_cosh_pow).mul h_poly_tanh
  have h_real_eq : ∀ x : ℝ, f (x : ℂ) = g (x : ℂ) := fun x => by
    simp only [hf_def, hg_def]
    have h_seed := partitionFunctionComplex_high_temp_expansion_h_zero_polymer_family_at_real G x β
    convert h_seed using 2
  have h_frequently : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = g z := by
    have h_tendsto : Filter.Tendsto
        (fun n : ℕ => ((1 / (n + 1 : ℝ) : ℝ) : ℂ)) Filter.atTop (𝓝 (0 : ℂ)) := by
      have h1 : Filter.Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ) : ℝ))
          Filter.atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
      exact (Complex.continuous_ofReal.tendsto _).comp h1
    have h_ne : ∀ n : ℕ, ((1 / (n + 1 : ℝ) : ℝ) : ℂ) ≠ 0 := fun n => by
      have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) :=
        one_div_pos.mpr (by positivity)
      exact_mod_cast hpos.ne'
    have h_principal : Filter.Tendsto
        (fun n : ℕ => ((1 / (n + 1 : ℝ) : ℝ) : ℂ)) Filter.atTop (𝓝[≠] (0 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨h_tendsto, Filter.Eventually.of_forall (fun n => h_ne n)⟩
    have h_freq_atTop :
        ∃ᶠ n : ℕ in Filter.atTop, f (((1 / ((n : ℝ) + 1) : ℝ)) : ℂ) =
            g (((1 / ((n : ℝ) + 1) : ℝ)) : ℂ) :=
      (Filter.Eventually.of_forall (fun n : ℕ => h_real_eq _)).frequently
    exact h_principal.frequently h_freq_atTop
  have h_eqOn : Set.EqOn f g U :=
    hf_anal.eqOn_of_preconnected_of_frequently_eq hg_anal hU_preconn h_zero_in_U h_frequently
  rw [Metric.eventually_nhds_iff_ball]
  exact ⟨r, hr, fun J hJ => h_eqOn hJ⟩

end IsingModel
