import IsingModel.ClusterExpansion.MayerCore.MayerIdentityPersiteKP
import IsingModel.ClusterExpansion.MayerCore.TermsComplexHolomorphic
import IsingModel.ClusterExpansion.MayerCore.ZeroBounds

/-!
# Complex Mayer–Montroll log identity (GJ §18.4–18.6)

The complex-activity form of the Mayer–Montroll identity: the polymer partition function (the sum
over vertex-disjoint compatible polymer families) equals the exponential of the complex cluster sum,
\[
  \sum_{\Gamma} \prod_{P \in \Gamma} z^{|P|}
    = \exp\!\Big(\sum_n \texttt{mayerExpansionTermComplex}\,G\,n\,z\Big),
\]
on the Kotecký–Preiss ball.  Proven by **analytic continuation** from the real Mayer–Montroll
identity `polymerFreeEnergy_eq_tsum_mayerExpansionTerm_of_persite_kp` (same identity-theorem pattern
as the complex high-temperature `Z` expansion): both sides are holomorphic on the KP ball and agree
at the real points `1/(k+1) → 0`, so the identity theorem extends the agreement to the whole ball.

This is the key cluster-expansion ingredient for the volume-uniform lower bound
`VolumeUniformComplexHTBound` (Issue #4230, item D of #4214): combined with the volume-uniform
per-site Mayer bound it gives `‖∑_Γ ∏ tanh(βJ)^{|P|}‖ = exp(Re ∑ mayer) ≥ exp(−|Λ|·kpBound)`, whence
the volume-uniform partition non-vanishing.

## Main result
* `vdPolymerFamilies_sum_pow_eq_exp_tsum_mayerExpansionTermComplex` — the complex Mayer–Montroll
  identity on the KP ball.

This is Ising-side content and is fully proven.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §18.4–18.6.
-/

namespace IsingModel

open Filter Topology

/-- **Complex Mayer–Montroll log identity** (GJ §18.4–18.6): on the Kotecký–Preiss ball
`Metric.ball 0 R` (with `(Δ(G))²·e·R < 1` and the second KP condition), the polymer partition
function equals the exponential of the complex cluster sum,
`∑_Γ ∏_{P∈Γ} z^{|P|} = exp(∑_n mayerExpansionTermComplex G n z)`.

Proven by analytic continuation from the real identity
`polymerFreeEnergy_eq_tsum_mayerExpansionTerm_of_persite_kp`: both sides are holomorphic on the ball
(the LHS is a polynomial; the RHS is `exp` of the analytic complex cluster sum,
`mayerExpansionTermComplex_tsum_differentiableOn_ball`), and they agree at the real points
`z = 1/(k+1) → 0` (where the real polymer sum is `exp(polymerFreeEnergy) = exp(∑ mayerTerm)`,
`vdPolymerFamilies_sum_pos_of_nonneg`), so the identity theorem
(`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`) extends the identity to the whole ball. -/
theorem vdPolymerFamilies_sum_pow_eq_exp_tsum_mayerExpansionTermComplex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    {R : ℝ} (hR : 0 < R)
    (hkpR : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρR : 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, z ^ P.card)
      = Complex.exp (∑' n : ℕ, mayerExpansionTermComplex G n z) := by
  classical
  set f : ℂ → ℂ := fun z => ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, z ^ P.card with hf_def
  set g : ℂ → ℂ := fun z => Complex.exp (∑' n : ℕ, mayerExpansionTermComplex G n z) with hg_def
  set U : Set ℂ := Metric.ball (0 : ℂ) R with hU
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hUpre : IsPreconnected U := (convex_ball (0 : ℂ) R).isPreconnected
  have h0U : (0 : ℂ) ∈ U := Metric.mem_ball_self hR
  -- LHS is a polynomial, hence analytic on `U`
  have hf_anal : AnalyticOnNhd ℂ f U := by
    intro w _
    refine Finset.analyticAt_fun_sum _ (fun Γ _ => ?_)
    refine Finset.analyticAt_fun_prod _ (fun P _ => ?_)
    exact analyticAt_id.pow _
  -- RHS is `exp` of the analytic complex cluster sum, hence analytic on `U`
  have hg_anal : AnalyticOnNhd ℂ g U := by
    have hdiff : DifferentiableOn ℂ
        (fun z : ℂ => ∑' n : ℕ, mayerExpansionTermComplex G n z) U :=
      mayerExpansionTermComplex_tsum_differentiableOn_ball G hR.le hkpR hρR
    have hanal : AnalyticOnNhd ℂ
        (fun z : ℂ => ∑' n : ℕ, mayerExpansionTermComplex G n z) U :=
      hdiff.analyticOnNhd hUopen
    exact fun w hw => (hanal w hw).cexp
  -- real-axis agreement on `[0, R)`
  have h_real_eq : ∀ t : ℝ, 0 ≤ t → t < R → f (↑t) = g (↑t) := by
    intro t ht0 htR
    have hLHS : f (↑t : ℂ)
        = ((∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card : ℝ) : ℂ) := by
      simp only [hf_def, Complex.ofReal_sum, Complex.ofReal_prod, Complex.ofReal_pow]
    have hpos := vdPolymerFamilies_sum_pos_of_nonneg G ht0
    have hreal_id :=
      polymerFreeEnergy_eq_tsum_mayerExpansionTerm_of_persite_kp G hR hkpR hρR ⟨ht0, htR⟩
    have hsum_exp :
        (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card)
          = Real.exp (∑' n : ℕ, mayerExpansionTerm G n t) := by
      rw [← hreal_id]
      unfold polymerFreeEnergy
      rw [Real.exp_log hpos]
    rw [hLHS, hsum_exp, hg_def, Complex.ofReal_exp, Complex.ofReal_tsum]
    exact congrArg Complex.exp
      (tsum_congr fun n => (mayerExpansionTermComplex_ofReal G n t).symm)
  -- agreement is frequent in the punctured neighbourhood of `0`
  have h_frequently : ∃ᶠ w in 𝓝[≠] (0 : ℂ), f w = g w := by
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
    -- for large `k`, `1/(k+1) ∈ [0, R)`, so `f = g` there
    have h_evR : ∀ᶠ k : ℕ in Filter.atTop, (1 / (k + 1 : ℝ) : ℝ) < R := by
      have : Filter.Tendsto (fun k : ℕ => (1 / (k + 1 : ℝ) : ℝ)) Filter.atTop (𝓝 (0 : ℝ)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      exact this.eventually (eventually_lt_nhds hR)
    have h_eq_seq : ∀ᶠ k : ℕ in Filter.atTop,
        f ((1 / (k + 1 : ℝ) : ℝ) : ℂ) = g ((1 / (k + 1 : ℝ) : ℝ) : ℂ) := by
      filter_upwards [h_evR] with k hk
      exact h_real_eq _ (by positivity) hk
    exact h_principal.frequently (h_eq_seq.frequently)
  -- identity theorem on the preconnected ball
  have hEqOn := hf_anal.eqOn_of_preconnected_of_frequently_eq hg_anal hUpre h0U h_frequently
  exact hEqOn hz

end IsingModel
