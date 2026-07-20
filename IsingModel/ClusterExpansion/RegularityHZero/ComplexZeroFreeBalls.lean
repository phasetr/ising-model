import IsingModel.ClusterExpansion.RegularityHZero.ComplexAnalyticityCore

/-!
# Cluster expansion zero-field regularity (4/4): complex zero-free balls

Structural split (4/4) of `ClusterExpansion.RegularityHZero`.  This child holds the
local non-vanishing consequences of the complex analyticity (Issue #3054): the value `1`
of the complex polymer-family sum at zero activity and at `β = 0` / `J = 0`, the
`Eventually` and open-ball non-vanishing statements around the origin, and the compactness
upgrade to a uniform lower bound `ε > 0` for the norm on a closed ball, in both the `β`
and the `J` direction.  These are the per-fixed-volume precursors of the volume-uniform
`Z_ℂ` lower bound wanted by the Lemma 17.5.2 `hZ` provider (Issue #3044).  It builds on
the sibling `...ComplexAnalyticityCore`.  See the `ClusterExpansion.RegularityHZero`
facade module for the full contents overview.
-/

namespace IsingModel

open Finset
open scoped Topology

/-- **Polymer-family sum (complex) at `t = 0`** (Issue #3054): the
`∑_Γ ∏_P t^|P|` evaluated at the complex zero equals `1`. Mirror of
`vdPolymerFamilies_sum_at_zero` — only the empty family `Γ = ∅` contributes
(its empty product equals `1`); any non-empty `Γ` contains a polymer with
`|P| ≥ 1`, so `(0 : ℂ)^|P| = 0` and the product vanishes. Provides the
constant term of the polymer-family sum at `t = 0`, the foundational point for
local non-vanishing of the polymer expansion in a complex disc (en route to the
volume-uniform `Z_ℂ` lower bound for the Lemma 17.5.2 `hZ` provider, Issue
#3044). -/
theorem vdPolymerFamilies_sum_complex_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, (0 : ℂ) ^ P.card) = 1 := by
  classical
  have h_empty_in :
      (∅ : Finset (Finset (Sym2 ι))) ∈ vdCompatiblePolymerFamilies G := by
    rw [mem_vdCompatiblePolymerFamilies]
    exact ⟨Finset.empty_subset _, IsCompatiblePolymerFamilyVertexDisjoint.empty G⟩
  have h_nonempty_zero : ∀ Γ ∈ vdCompatiblePolymerFamilies G,
      Γ ≠ ∅ → (∏ P ∈ Γ, (0 : ℂ) ^ P.card) = 0 := by
    intro Γ hΓ hne
    rw [mem_vdCompatiblePolymerFamilies] at hΓ
    obtain ⟨P, hP⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hP_polymer : IsPolymer G P := mem_allPolymers.mp (hΓ.1 hP)
    have hP_pos : 0 < P.card := hP_polymer.nonempty.card_pos
    exact Finset.prod_eq_zero hP (zero_pow hP_pos.ne')
  rw [Finset.sum_eq_single ∅]
  · rw [Finset.prod_empty]
  · intro Γ hΓ hne
    exact h_nonempty_zero Γ hΓ hne
  · intro h
    exact absurd h_empty_in h

/-- **Polymer-family sum with `Complex.tanh` evaluated at `β = 0` equals `1`**
(Issue #3054): immediate from `Complex.tanh_zero` (`tanh 0 = 0`) and
`vdPolymerFamilies_sum_complex_at_zero`. -/
theorem vdPolymerFamilies_sum_tanh_complex_at_zero_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℂ) :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Complex.tanh ((0 : ℂ) * J) ^ P.card) = 1 := by
  simp [Complex.tanh_zero, vdPolymerFamilies_sum_complex_at_zero]

/-- **Polymer-family sum with `Complex.tanh` is eventually non-zero near
`β = 0`** (Issue #3054). At `β = 0` the sum equals `1` (via
`vdPolymerFamilies_sum_tanh_complex_at_zero_beta`); by complex-analytic continuity
(`vdPolymerFamilies_sum_tanh_analyticAt_complex_beta`, using `Complex.cosh 0 = 1
≠ 0`), the sum stays non-zero in a complex neighborhood of `β = 0`. The complex
analogue of the local non-vanishing point for the polymer expansion — the first
step in the eventual zero-free disc for the volume-uniform `Z_ℂ` lower bound of
the Lemma 17.5.2 `hZ` provider (#3044). -/
theorem vdPolymerFamilies_sum_tanh_complex_eventually_ne_zero_at_zero_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℂ) :
    ∀ᶠ β : ℂ in 𝓝 (0 : ℂ),
      (∑ Γ ∈ vdCompatiblePolymerFamilies G,
         ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card) ≠ 0 := by
  have hcosh0 : Complex.cosh ((0 : ℂ) * J) ≠ 0 := by
    rw [zero_mul, Complex.cosh_zero]; exact one_ne_zero
  have h_analyticAt :
      AnalyticAt ℂ (fun β : ℂ =>
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card) 0 :=
    vdPolymerFamilies_sum_tanh_analyticAt_complex_beta G J 0 hcosh0
  have h_continuousAt := h_analyticAt.continuousAt
  have h_at_zero :
      (fun β : ℂ => ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card) 0 = 1 :=
    vdPolymerFamilies_sum_tanh_complex_at_zero_beta G J
  have h_ne : (fun β : ℂ => ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card) 0 ≠ 0 := by
    rw [h_at_zero]; exact one_ne_zero
  exact h_continuousAt.eventually_ne h_ne

/-- **Polymer-family sum with `Complex.tanh` is non-zero on a complex ball at
`β = 0`** (Issue #3054). Quantitative ball-form of
`vdPolymerFamilies_sum_tanh_complex_eventually_ne_zero_at_zero_beta`: there
exists a radius `r > 0` such that the `tanh`-substituted complex polymer-family
sum is non-zero on the entire `Metric.ball (0 : ℂ) r`. Derived from
`Metric.eventually_nhds_iff_ball` applied to the `Eventually` form. The radius
`r` depends on `G` and `J`; volume-uniformity is the next step. -/
theorem vdPolymerFamilies_sum_tanh_complex_ne_zero_on_ball_at_zero_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℂ) :
    ∃ r > 0, ∀ β ∈ Metric.ball (0 : ℂ) r,
      (∑ Γ ∈ vdCompatiblePolymerFamilies G,
         ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card) ≠ 0 := by
  have h := vdPolymerFamilies_sum_tanh_complex_eventually_ne_zero_at_zero_beta G J
  rw [Metric.eventually_nhds_iff_ball] at h
  obtain ⟨r, hr_pos, hr⟩ := h
  exact ⟨r, hr_pos, hr⟩

/-- **Polymer-family sum with `Complex.tanh` is bounded below by `ε > 0` on a
closed complex ball at `β = 0`** (Issue #3054). Compactness + continuity
upgrade of the ball-form non-vanishing
`vdPolymerFamilies_sum_tanh_complex_ne_zero_on_ball_at_zero_beta`: pick a
strictly smaller closed sub-ball, where the continuous norm function attains
its minimum (which is `> 0` since the sum is non-zero on the larger open ball).

The dependence of both `r` and `ε` on `G`/`J` is not yet quantified — this is
the per-fixed-volume version. Volume-uniformity is the open hard core for the
Lemma 17.5.2 `hZ` provider (Issue #3044). -/
theorem vdPolymerFamilies_sum_tanh_complex_norm_ge_eps_on_closedBall_at_zero_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℂ) :
    ∃ r > 0, ∃ ε > 0, ∀ β ∈ Metric.closedBall (0 : ℂ) r,
      ε ≤ ‖∑ Γ ∈ vdCompatiblePolymerFamilies G,
         ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card‖ := by
  classical
  -- Open ball where polymer-tanh sum is non-zero (#3060).
  obtain ⟨r₁, hr₁, h_ne⟩ :=
    vdPolymerFamilies_sum_tanh_complex_ne_zero_on_ball_at_zero_beta G J
  -- Open ball where cosh (β·J) ≠ 0 (needed for tanh continuity).
  have hcont_cosh : Continuous (fun β : ℂ => Complex.cosh (β * J)) :=
    Complex.continuous_cosh.comp (continuous_id.mul continuous_const)
  have h_cosh0 : Complex.cosh ((0 : ℂ) * J) ≠ 0 := by
    rw [zero_mul, Complex.cosh_zero]; exact one_ne_zero
  have h_cosh_ev : ∀ᶠ β in 𝓝 (0 : ℂ), Complex.cosh (β * J) ≠ 0 :=
    hcont_cosh.continuousAt.eventually_ne h_cosh0
  rw [Metric.eventually_nhds_iff_ball] at h_cosh_ev
  obtain ⟨r₂, hr₂, h_cosh_ne⟩ := h_cosh_ev
  -- Take r := min(r₁, r₂) / 2 so closedBall (0) r ⊂ ball (0) r₁ ∩ ball (0) r₂.
  set r : ℝ := min r₁ r₂ / 2 with hr_def
  have hr_pos : 0 < r := by
    have hmin : 0 < min r₁ r₂ := lt_min hr₁ hr₂
    simp only [hr_def]; linarith
  refine ⟨r, hr_pos, ?_⟩
  have hmin_pos : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  have hr_lt_r1 : r < r₁ := by
    have : min r₁ r₂ ≤ r₁ := min_le_left _ _
    simp only [hr_def]; linarith
  have hr_lt_r2 : r < r₂ := by
    have : min r₁ r₂ ≤ r₂ := min_le_right _ _
    simp only [hr_def]; linarith
  have h_sub_b1 : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) r₁ := by
    intro β hβ
    rw [Metric.mem_closedBall] at hβ
    rw [Metric.mem_ball]; linarith
  have h_sub_b2 : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) r₂ := by
    intro β hβ
    rw [Metric.mem_closedBall] at hβ
    rw [Metric.mem_ball]; linarith
  -- Continuity of `Complex.tanh (β·J)` on closedBall (0) r.
  have h_tanh_cont :
      ContinuousOn (fun β : ℂ => Complex.tanh (β * J))
        (Metric.closedBall (0 : ℂ) r) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (Complex.continuous_sinh.comp
        (continuous_id.mul continuous_const)).continuousOn
    · exact hcont_cosh.continuousOn
    · intro β hβ
      exact h_cosh_ne β (h_sub_b2 hβ)
  -- Continuity of the polymer-tanh sum on closedBall.
  have h_sum_cont :
      ContinuousOn (fun β : ℂ =>
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card)
        (Metric.closedBall (0 : ℂ) r) :=
    continuousOn_finset_sum _ (fun Γ _ =>
      continuousOn_finset_prod _ (fun P _ => h_tanh_cont.pow _))
  have h_norm_cont :
      ContinuousOn (fun β : ℂ =>
        ‖∑ Γ ∈ vdCompatiblePolymerFamilies G,
            ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card‖)
        (Metric.closedBall (0 : ℂ) r) :=
    h_sum_cont.norm
  have h_compact : IsCompact (Metric.closedBall (0 : ℂ) r) :=
    isCompact_closedBall _ _
  have h_nonempty : (Metric.closedBall (0 : ℂ) r).Nonempty :=
    ⟨0, Metric.mem_closedBall_self hr_pos.le⟩
  obtain ⟨β_min, hβ_min, h_min⟩ :=
    h_compact.exists_isMinOn h_nonempty h_norm_cont
  set ε := ‖∑ Γ ∈ vdCompatiblePolymerFamilies G,
       ∏ P ∈ Γ, Complex.tanh (β_min * J) ^ P.card‖
  have h_ne_val : ∑ Γ ∈ vdCompatiblePolymerFamilies G,
       ∏ P ∈ Γ, Complex.tanh (β_min * J) ^ P.card ≠ 0 :=
    h_ne β_min (h_sub_b1 hβ_min)
  have h_eps_pos : 0 < ε := norm_pos_iff.mpr h_ne_val
  refine ⟨ε, h_eps_pos, ?_⟩
  intro β hβ
  exact h_min hβ

/-- **Polymer-family sum with `Complex.tanh` evaluated at `J = 0` equals `1`**
(Issue #3054, `J`-direction analogue of
`vdPolymerFamilies_sum_tanh_complex_at_zero_beta`): immediate from
`Complex.tanh_zero` (`tanh (β · 0) = tanh 0 = 0`) and
`vdPolymerFamilies_sum_complex_at_zero`. -/
theorem vdPolymerFamilies_sum_tanh_complex_at_zero_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℂ) :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Complex.tanh (β * (0 : ℂ)) ^ P.card) = 1 := by
  simp [Complex.tanh_zero, vdPolymerFamilies_sum_complex_at_zero]

/-- **Polymer-family sum with `Complex.tanh` is eventually non-zero near `J = 0`**
(Issue #3054, `J`-direction analogue of
`vdPolymerFamilies_sum_tanh_complex_eventually_ne_zero_at_zero_beta`). -/
theorem vdPolymerFamilies_sum_tanh_complex_eventually_ne_zero_at_zero_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℂ) :
    ∀ᶠ J : ℂ in 𝓝 (0 : ℂ),
      (∑ Γ ∈ vdCompatiblePolymerFamilies G,
         ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card) ≠ 0 := by
  have hcosh0 : Complex.cosh (β * (0 : ℂ)) ≠ 0 := by
    rw [mul_zero, Complex.cosh_zero]; exact one_ne_zero
  have h_analyticAt :
      AnalyticAt ℂ (fun J : ℂ =>
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card) 0 :=
    vdPolymerFamilies_sum_tanh_analyticAt_complex_J G β 0 hcosh0
  have h_continuousAt := h_analyticAt.continuousAt
  have h_at_zero :
      (fun J : ℂ => ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card) 0 = 1 :=
    vdPolymerFamilies_sum_tanh_complex_at_zero_J G β
  have h_ne : (fun J : ℂ => ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card) 0 ≠ 0 := by
    rw [h_at_zero]; exact one_ne_zero
  exact h_continuousAt.eventually_ne h_ne

/-- **Polymer-family sum with `Complex.tanh` is non-zero on a complex ball at
`J = 0`** (Issue #3054, `J`-direction analogue of
`vdPolymerFamilies_sum_tanh_complex_ne_zero_on_ball_at_zero_beta`). -/
theorem vdPolymerFamilies_sum_tanh_complex_ne_zero_on_ball_at_zero_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℂ) :
    ∃ r > 0, ∀ J ∈ Metric.ball (0 : ℂ) r,
      (∑ Γ ∈ vdCompatiblePolymerFamilies G,
         ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card) ≠ 0 := by
  have h := vdPolymerFamilies_sum_tanh_complex_eventually_ne_zero_at_zero_J G β
  rw [Metric.eventually_nhds_iff_ball] at h
  obtain ⟨r, hr_pos, hr⟩ := h
  exact ⟨r, hr_pos, hr⟩

/-- **Polymer-family sum with `Complex.tanh` is bounded below by `ε > 0` on a
closed complex ball at `J = 0`** (Issue #3054, `J`-direction analogue of
`vdPolymerFamilies_sum_tanh_complex_norm_ge_eps_on_closedBall_at_zero_beta`). -/
theorem vdPolymerFamilies_sum_tanh_complex_norm_ge_eps_on_closedBall_at_zero_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℂ) :
    ∃ r > 0, ∃ ε > 0, ∀ J ∈ Metric.closedBall (0 : ℂ) r,
      ε ≤ ‖∑ Γ ∈ vdCompatiblePolymerFamilies G,
         ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card‖ := by
  classical
  obtain ⟨r₁, hr₁, h_ne⟩ :=
    vdPolymerFamilies_sum_tanh_complex_ne_zero_on_ball_at_zero_J G β
  have hcont_cosh : Continuous (fun J : ℂ => Complex.cosh (β * J)) :=
    Complex.continuous_cosh.comp (continuous_const.mul continuous_id)
  have h_cosh0 : Complex.cosh (β * (0 : ℂ)) ≠ 0 := by
    rw [mul_zero, Complex.cosh_zero]; exact one_ne_zero
  have h_cosh_ev : ∀ᶠ J in 𝓝 (0 : ℂ), Complex.cosh (β * J) ≠ 0 :=
    hcont_cosh.continuousAt.eventually_ne h_cosh0
  rw [Metric.eventually_nhds_iff_ball] at h_cosh_ev
  obtain ⟨r₂, hr₂, h_cosh_ne⟩ := h_cosh_ev
  set r : ℝ := min r₁ r₂ / 2 with hr_def
  have hr_pos : 0 < r := by
    have : 0 < min r₁ r₂ := lt_min hr₁ hr₂
    simp only [hr_def]; linarith
  refine ⟨r, hr_pos, ?_⟩
  have hmin_pos : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  have hr_lt_r1 : r < r₁ := by
    have : min r₁ r₂ ≤ r₁ := min_le_left _ _
    simp only [hr_def]; linarith
  have hr_lt_r2 : r < r₂ := by
    have : min r₁ r₂ ≤ r₂ := min_le_right _ _
    simp only [hr_def]; linarith
  have h_sub_b1 : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) r₁ := by
    intro J hJ
    rw [Metric.mem_closedBall] at hJ
    rw [Metric.mem_ball]; linarith
  have h_sub_b2 : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) r₂ := by
    intro J hJ
    rw [Metric.mem_closedBall] at hJ
    rw [Metric.mem_ball]; linarith
  have h_tanh_cont :
      ContinuousOn (fun J : ℂ => Complex.tanh (β * J))
        (Metric.closedBall (0 : ℂ) r) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (Complex.continuous_sinh.comp
        (continuous_const.mul continuous_id)).continuousOn
    · exact hcont_cosh.continuousOn
    · intro J hJ
      exact h_cosh_ne J (h_sub_b2 hJ)
  have h_sum_cont :
      ContinuousOn (fun J : ℂ =>
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card)
        (Metric.closedBall (0 : ℂ) r) :=
    continuousOn_finset_sum _ (fun Γ _ =>
      continuousOn_finset_prod _ (fun P _ => h_tanh_cont.pow _))
  have h_norm_cont :
      ContinuousOn (fun J : ℂ =>
        ‖∑ Γ ∈ vdCompatiblePolymerFamilies G,
            ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card‖)
        (Metric.closedBall (0 : ℂ) r) :=
    h_sum_cont.norm
  have h_compact : IsCompact (Metric.closedBall (0 : ℂ) r) :=
    isCompact_closedBall _ _
  have h_nonempty : (Metric.closedBall (0 : ℂ) r).Nonempty :=
    ⟨0, Metric.mem_closedBall_self hr_pos.le⟩
  obtain ⟨J_min, hJ_min, h_min⟩ :=
    h_compact.exists_isMinOn h_nonempty h_norm_cont
  set ε := ‖∑ Γ ∈ vdCompatiblePolymerFamilies G,
       ∏ P ∈ Γ, Complex.tanh (β * J_min) ^ P.card‖
  have h_ne_val : ∑ Γ ∈ vdCompatiblePolymerFamilies G,
       ∏ P ∈ Γ, Complex.tanh (β * J_min) ^ P.card ≠ 0 :=
    h_ne J_min (h_sub_b1 hJ_min)
  have h_eps_pos : 0 < ε := norm_pos_iff.mpr h_ne_val
  refine ⟨ε, h_eps_pos, ?_⟩
  intro J hJ
  exact h_min hJ

end IsingModel
