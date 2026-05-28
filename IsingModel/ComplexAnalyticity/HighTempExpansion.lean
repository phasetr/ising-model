import IsingModel.ComplexAnalyticity.Basic
import IsingModel.ClusterExpansion.Families
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

end IsingModel
