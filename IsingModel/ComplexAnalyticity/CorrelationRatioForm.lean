import IsingModel.ComplexAnalyticity.Correlation
import IsingModel.Conditioning.CorrelationClosed.ClosedForm

/-!
# Complex two-point correlation intensive ratio form (GJ §18.4–18.7, FV (3.46))

The complex-parameter analogue of the real high-temperature subgraph expansion of the two-point
function (`correlation_high_temp_expansion_h_zero_closed`, FV eq. (3.46)): the **intensive ratio**
form in which the extensive `2^{|V|}·cosh(βJ)^{|E|}` prefactor has cancelled,
\[
  \langle σ^A \rangle_{\mathbb C}(J, 0, β)
    = \frac{\sum_{X : \partial X = A} \tanh(βJ)^{|X|}}{\sum_{X \text{ even}} \tanh(βJ)^{|X|}},
\]
on a disc around `β = 0`.  This is the foundation for a volume-uniform bound on the complex
correlation (the remaining Ising input `hbdd` of the infinite-volume correlation-analyticity
programme, Issue #4230, item D of #4214): bounding the *ratio* (not numerator and denominator
separately) is what yields a volume-independent estimate.

Proven by **analytic continuation** from the real identity: both sides are holomorphic on a small
disc where the complex partition function, the even-subgraph denominator, and `cosh(βJ)` are all
nonvanishing (each equals a nonzero value at `β = 0`, by continuity), and they agree at the real
points `1/(k+1) → 0`, so the identity theorem extends the equality to the whole disc.

## Main result
* `correlationComplex_high_temp_expansion_h_zero_closed_on_ball` — the complex intensive ratio form.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §18.4–18.7;
Friedli–Velenik, eq. (3.46).
-/

namespace IsingModel

open Filter Topology

/-- The complex even/`A`-odd subgraph-`tanh` sum (numerator of the intensive ratio for `A`; the
denominator is the `A = ∅` instance). -/
private noncomputable def subgraphTanhSumComplex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (A : Finset ι) (J : ℝ) (β : ℂ) : ℂ :=
  ∑ X ∈ G.edgeFinset.powerset.filter
      (fun X => ∀ v : ι, Even ((if v ∈ A then (1 : ℕ) else 0) + (X.filter (v ∈ ·)).card)),
    Complex.tanh (β * (J : ℂ)) ^ X.card

/-- **Complex two-point correlation intensive ratio form** (GJ §18.4–18.7; FV (3.46)): on a disc
around `β = 0`, the complex two-point correlation equals the ratio of the `A`-odd subgraph-`tanh`
sum to the even subgraph-`tanh` sum — the intensive form with the `2^{|V|}·cosh(βJ)^{|E|}` prefactor
cancelled.  Proven by analytic continuation from the real FV (3.46) identity
`correlation_high_temp_expansion_h_zero_closed`. -/
theorem correlationComplex_high_temp_expansion_h_zero_closed_on_ball
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (A : Finset ι) (J : ℝ) :
    ∃ r > 0, ∀ β ∈ Metric.ball (0 : ℂ) r,
      correlationComplex G A (J : ℂ) 0 β
        = subgraphTanhSumComplex G A J β / subgraphTanhSumComplex G ∅ J β := by
  classical
  -- nonvanishing-at-`0` data, pushed to a small disc by continuity
  -- (1) `cosh (β J) ≠ 0`
  have h_cosh0 : Complex.cosh ((0 : ℂ) * (J : ℂ)) ≠ 0 := by
    rw [zero_mul, Complex.cosh_zero]; exact one_ne_zero
  have h_cosh_ev : ∀ᶠ β : ℂ in 𝓝 (0 : ℂ), Complex.cosh (β * (J : ℂ)) ≠ 0 :=
    (Complex.continuous_cosh.comp (continuous_id.mul continuous_const)).continuousAt.eventually_ne
      h_cosh0
  -- (2) complex partition function `≠ 0` (at `β = 0`, `Z = 2^{|ι|} ≠ 0`)
  have hZ0 : partitionFunctionComplex G (J : ℂ) 0 0 ≠ 0 := by
    have : partitionFunctionComplex G (J : ℂ) 0 0
        = ∑ _σ : Config ι, (1 : ℂ) := by
      unfold partitionFunctionComplex
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      simp [neg_zero, zero_mul, Complex.exp_zero]
    rw [this]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact_mod_cast (Fintype.card_ne_zero (α := Config ι))
  have hZ_ev : ∀ᶠ β : ℂ in 𝓝 (0 : ℂ), partitionFunctionComplex G (J : ℂ) 0 β ≠ 0 :=
    (partitionFunctionComplex_analyticAt_beta G (J : ℂ) 0 0).continuousAt.eventually_ne hZ0
  -- analyticity of a single `tanh (β J) ^ k` at any point where `cosh (β J) ≠ 0`
  have htanhpow_at : ∀ (k : ℕ) (z : ℂ), Complex.cosh (z * (J : ℂ)) ≠ 0 →
      AnalyticAt ℂ (fun β : ℂ => Complex.tanh (β * (J : ℂ)) ^ k) z := by
    intro k z hz
    have h_mul : AnalyticAt ℂ (fun β : ℂ => β * (J : ℂ)) z :=
      analyticAt_id.mul analyticAt_const
    have hsinh : AnalyticAt ℂ (fun β : ℂ => Complex.sinh (β * (J : ℂ))) z := by
      have h_comp : AnalyticAt ℂ (Complex.sinh ∘ fun β : ℂ => β * (J : ℂ)) z := by
        refine AnalyticAt.comp ?_ h_mul
        exact Complex.analyticOnNhd_sinh (s := Set.univ) (z * (J : ℂ)) (Set.mem_univ _)
      exact h_comp
    have hcosh : AnalyticAt ℂ (fun β : ℂ => Complex.cosh (β * (J : ℂ))) z := by
      have h_comp : AnalyticAt ℂ (Complex.cosh ∘ fun β : ℂ => β * (J : ℂ)) z := by
        refine AnalyticAt.comp ?_ h_mul
        exact Complex.analyticOnNhd_cosh (s := Set.univ) (z * (J : ℂ)) (Set.mem_univ _)
      exact h_comp
    exact (hsinh.div hcosh hz).pow _
  -- (3) even-subgraph denominator `≠ 0` (at `β = 0`, only `X = ∅` survives, sum `= 1`)
  have h_den_analAt0 : AnalyticAt ℂ (fun β : ℂ => subgraphTanhSumComplex G ∅ J β) 0 := by
    unfold subgraphTanhSumComplex
    exact Finset.analyticAt_fun_sum _ (fun X _ => htanhpow_at X.card 0 h_cosh0)
  have h_den0 : subgraphTanhSumComplex G ∅ J 0 ≠ 0 := by
    unfold subgraphTanhSumComplex
    rw [Finset.sum_eq_single (∅ : Finset (Sym2 ι))]
    · simp
    · intro X hX hXne
      have hXcard : 0 < X.card := Finset.card_pos.mpr (Finset.nonempty_of_ne_empty hXne)
      rw [zero_mul, Complex.tanh_zero, zero_pow (by omega : X.card ≠ 0)]
    · intro hmem
      exfalso
      apply hmem
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.empty_subset _, fun v => by simp⟩
  have h_den_ev : ∀ᶠ β : ℂ in 𝓝 (0 : ℂ),
      subgraphTanhSumComplex G ∅ J β ≠ 0 :=
    h_den_analAt0.continuousAt.eventually_ne h_den0
  -- intersect the three neighbourhoods into a single ball
  obtain ⟨r, hr, hr_sub⟩ := Metric.eventually_nhds_iff_ball.mp
    (h_cosh_ev.and (hZ_ev.and h_den_ev))
  refine ⟨r, hr, ?_⟩
  set U : Set ℂ := Metric.ball (0 : ℂ) r with hU
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hUpre : IsPreconnected U := (convex_ball (0 : ℂ) r).isPreconnected
  have h0U : (0 : ℂ) ∈ U := Metric.mem_ball_self hr
  have hcoshU : ∀ z ∈ U, Complex.cosh (z * (J : ℂ)) ≠ 0 := fun z hz => (hr_sub z hz).1
  have hZU : ∀ z ∈ U, partitionFunctionComplex G (J : ℂ) 0 z ≠ 0 := fun z hz => (hr_sub z hz).2.1
  have hdenU : ∀ z ∈ U, subgraphTanhSumComplex G ∅ J z ≠ 0 := fun z hz => (hr_sub z hz).2.2
  -- analyticity of the subgraph-`tanh` sums on `U`
  have h_subgraph_anal : ∀ (B : Finset ι),
      AnalyticOnNhd ℂ (fun β : ℂ => subgraphTanhSumComplex G B J β) U := by
    intro B z hz
    exact Finset.analyticAt_fun_sum _ (fun X _ => htanhpow_at X.card z (hcoshU z hz))
  -- `f` and `g`
  have hf_anal : AnalyticOnNhd ℂ
      (fun β : ℂ => correlationComplex G A (J : ℂ) 0 β) U := by
    intro z hz
    exact correlationComplex_analyticAt_beta G A (J : ℂ) 0 z (hZU z hz)
  have hg_anal : AnalyticOnNhd ℂ
      (fun β : ℂ => subgraphTanhSumComplex G A J β / subgraphTanhSumComplex G ∅ J β) U := by
    intro z hz
    exact (h_subgraph_anal A z hz).div (h_subgraph_anal ∅ z hz) (hdenU z hz)
  -- real-axis agreement (cast of FV (3.46))
  have h_real_eq : ∀ t : ℝ, (↑t : ℂ) ∈ U →
      correlationComplex G A (J : ℂ) 0 (↑t)
        = subgraphTanhSumComplex G A J (↑t) / subgraphTanhSumComplex G ∅ J (↑t) := by
    intro t _
    have hreal := correlation_high_temp_expansion_h_zero_closed G J t A
    have hcast : ∀ (B : Finset ι),
        subgraphTanhSumComplex G B J (↑t)
          = ((∑ X ∈ G.edgeFinset.powerset.filter
              (fun X => ∀ v : ι, Even ((if v ∈ B then (1 : ℕ) else 0)
                + (X.filter (v ∈ ·)).card)),
              Real.tanh (t * J) ^ X.card : ℝ) : ℂ) := by
      intro B
      unfold subgraphTanhSumComplex
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun X _ => ?_)
      rw [Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_tanh]
    -- the `∅`-instance filter `Even((if v∈∅ then 1 else 0)+…)` equals the plain even filter
    have h_den_filter :
        (G.edgeFinset.powerset.filter
          (fun X => ∀ v : ι, Even ((if v ∈ (∅ : Finset ι) then (1 : ℕ) else 0)
            + (X.filter (v ∈ ·)).card)))
        = G.edgeFinset.powerset.filter
          (fun X => ∀ v : ι, Even ((X.filter (v ∈ ·)).card)) := by
      apply Finset.filter_congr
      intro X _
      simp
    have hcorr := correlation_ofReal_eq_correlationComplex G (⟨J, 0, t⟩ : IsingParams ℝ) A
    simp only [Complex.ofReal_zero] at hcorr
    rw [← hcorr, hcast A, hcast ∅, h_den_filter, ← Complex.ofReal_div]
    exact congrArg _ hreal
  -- frequent agreement at `1/(k+1) → 0`
  have h_frequently : ∃ᶠ z in 𝓝[≠] (0 : ℂ),
      correlationComplex G A (J : ℂ) 0 z
        = subgraphTanhSumComplex G A J z / subgraphTanhSumComplex G ∅ J z := by
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
    have h_evU : ∀ᶠ k : ℕ in Filter.atTop, ((1 / (k + 1 : ℝ) : ℝ) : ℂ) ∈ U := by
      exact h_tendsto.eventually (hUopen.mem_nhds h0U)
    have h_eq_seq : ∀ᶠ k : ℕ in Filter.atTop,
        correlationComplex G A (J : ℂ) 0 ((1 / (k + 1 : ℝ) : ℝ) : ℂ)
          = subgraphTanhSumComplex G A J ((1 / (k + 1 : ℝ) : ℝ) : ℂ)
            / subgraphTanhSumComplex G ∅ J ((1 / (k + 1 : ℝ) : ℝ) : ℂ) := by
      filter_upwards [h_evU] with k hk
      exact h_real_eq _ hk
    exact h_principal.frequently (h_eq_seq.frequently)
  -- identity theorem
  have hEqOn := hf_anal.eqOn_of_preconnected_of_frequently_eq hg_anal hUpre h0U h_frequently
  exact fun β hβ => hEqOn hβ

end IsingModel
