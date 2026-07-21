import IsingModel.ComplexAnalyticity.DomainGeometry

/-!
# Slit-Plane Loci and Local Branch Restatements

This module is part of the split `IsingModel.ComplexAnalyticity` development.
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Complex

/-! ### Summary of the PR #200 local-branch construction

The goal of PR #200 (continuation of PR #199) is the finite-volume
analyticity of `freeEnergyComplex` on the Lee-Yang domain. The following
chain was established:

1. `logDeriv_partitionFunctionComplex_analyticOnNhd_leeYangDomain`
   (logarithmic derivative is holomorphic on `leeYangDomain`).
2. `exists_logZ_branch_on_ball_of_leeYangDomain` (Morera primitive).
3. `exists_normalised_logZ_branch_on_ball` (basepoint normalisation).
4. `exists_logZ_holomorphic_branch_on_ball` (`exp g = Z`).
5. `exists_logZ_analytic_branch_on_ball` (`g` analytic on the ball).
6. `exists_logZ_analyticAt_of_leeYangDomain` (pointwise AnalyticAt on
   the entire Lee-Yang domain, via openness).
7. `exists_freeEnergyComplex_analyticAt_branch_of_leeYangDomain` (headline:
   local analytic branch of `freeEnergyComplex` at every point).
8. `analyticBranch_freeEnergyComplex_leeYangDomain` (∀-form).

This is the local-branch form of GJ Thm 4.6.2 finite volume. The
principal-branch `freeEnergyComplex` (using `Complex.log`) can be
discontinuous where `Z` crosses the negative real axis; the local
branch is continuous across such crossings.

The infinite-volume lift via Vitali:
- `vitali_bridge` / `_leeYangDomain` / `_leeYangSubdomain` /
  `_eventually` wrap mathlib's
  `TendstoLocallyUniformlyOn.differentiableOn`.
- `norm_partitionFunctionComplex_le_partitionFunction` +
  `norm_partitionFunctionComplex_le_trivial_bound` +
  `norm_partitionFunctionComplex_le_of_re_bound` provide the uniform
  bounds on `|Z|` (Montel input).
- `norm_freeEnergyComplex_le_trivial_bound` gives the bound on
  `‖freeEnergyComplex‖`.

The remaining step (locally uniform convergence of finite-volume
branches to an infinite-volume branch) requires a Montel-style
subsequence argument; this is the last ingredient of GJ Thm 4.6.2. -/

/-- **`freeEnergyComplex` is analytic at `h₀` whenever `Z(h₀) ∈ slitPlane`**,
restated with explicit analytic-at formulation for downstream use. -/
theorem analyticAt_freeEnergyComplex_of_slitPlane_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℂ) {h₀ : ℂ}
    (hZ : partitionFunctionComplex G J h₀ β ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun h => freeEnergyComplex G J h β) h₀ :=
  freeEnergyComplex_analyticAt_h G J β h₀ hZ

/-- `{h : ℂ | h ∈ leeYangSubdomain β N}` is convex — immediate since
`leeYangSubdomain` is open and convex (intersection of Lee-Yang +
strip). Formulated as `Convex ℝ`. -/
theorem convex_leeYangSubdomain' (β : ℝ) (N : ℕ) :
    Convex ℝ (leeYangSubdomain β N) := by
  intro x hx y hy a b ha hb hab
  refine ⟨convex_leeYangDomain hx.1 hy.1 ha hb hab, ?_⟩
  have hx2 : β * |x.im| * (N : ℝ) < Real.pi / 2 := hx.2
  have hy2 : β * |y.im| * (N : ℝ) < Real.pi / 2 := hy.2
  change β * |((a : ℝ) • x + (b : ℝ) • y).im| * (N : ℝ) < Real.pi / 2
  simp only [Complex.add_im, Complex.smul_im]
  have habs : |a * x.im + b * y.im| ≤ a * |x.im| + b * |y.im| := by
    calc |a * x.im + b * y.im|
        ≤ |a * x.im| + |b * y.im| := abs_add_le _ _
      _ = a * |x.im| + b * |y.im| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  -- β · |sum| · N ≤ ?; handle sign of β separately.
  by_cases hβ : 0 ≤ β
  · have : β * |a * x.im + b * y.im| * (N : ℝ)
            ≤ β * (a * |x.im| + b * |y.im|) * (N : ℝ) := by
      have hβN : 0 ≤ β * (N : ℝ) := by positivity
      nlinarith
    calc β * |a * x.im + b * y.im| * (N : ℝ)
        ≤ β * (a * |x.im| + b * |y.im|) * (N : ℝ) := this
      _ = a * (β * |x.im| * (N : ℝ)) + b * (β * |y.im| * (N : ℝ)) := by ring
      _ < a * (Real.pi / 2) + b * (Real.pi / 2) := by
          rcases eq_or_lt_of_le ha with rfl | ha_pos
          · rcases eq_or_lt_of_le hb with rfl | hb_pos
            · simp at hab
            · simpa using mul_lt_mul_of_pos_left hy2 hb_pos
          · rcases eq_or_lt_of_le hb with rfl | hb_pos
            · simpa using mul_lt_mul_of_pos_left hx2 ha_pos
            · exact add_lt_add (mul_lt_mul_of_pos_left hx2 ha_pos)
                (mul_lt_mul_of_pos_left hy2 hb_pos)
      _ = Real.pi / 2 := by linear_combination hab * (Real.pi / 2)
  · push Not at hβ
    -- β < 0: β·|·|·N ≤ 0 < π/2.
    have : β * |a * x.im + b * y.im| * (N : ℝ) ≤ 0 := by
      have : β * (N : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hβ.le
        (Nat.cast_nonneg _)
      nlinarith [abs_nonneg (a * x.im + b * y.im)]
    calc β * |a * x.im + b * y.im| * (N : ℝ) ≤ 0 := this
      _ < Real.pi / 2 := by positivity

/-- The Lee-Yang subdomain is preconnected (from convexity). -/
theorem isPreconnected_leeYangSubdomain (β : ℝ) (N : ℕ) :
    IsPreconnected (leeYangSubdomain β N) :=
  (convex_leeYangSubdomain' β N).isPreconnected

/-- The Lee-Yang subdomain is connected (nonempty + preconnected). -/
theorem isConnected_leeYangSubdomain (β : ℝ) (N : ℕ) :
    IsConnected (leeYangSubdomain β N) :=
  ⟨leeYangSubdomain_nonempty β N, isPreconnected_leeYangSubdomain β N⟩

/-- At `h = (h₀ : ℂ)` with `h₀ > 0` real, the partition function equals
its real-parameter value (which is `partitionFunction G ⟨J, h₀, β⟩`). -/
theorem partitionFunctionComplex_at_real_pos
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (h₀ : ℝ) :
    partitionFunctionComplex G (J : ℂ) (h₀ : ℂ) (β : ℂ)
      = ((partitionFunction G ⟨J, h₀, β⟩ : ℝ) : ℂ) :=
  (partitionFunction_ofReal_eq_partitionFunctionComplex G ⟨J, h₀, β⟩).symm

/-- `freeEnergyComplex` at real parameters equals its real-parameter
value. Restatement for convenience. -/
theorem freeEnergyComplex_at_real
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) :
    freeEnergyComplex G (J : ℂ) (h : ℂ) (β : ℂ)
      = ((freeEnergy G ⟨J, h, β⟩ : ℝ) : ℂ) :=
  freeEnergyComplex_ofReal_eq_freeEnergy G ⟨J, h, β⟩

/-- **Positivity of `Re Z` at real positive `h`**: at real parameters
`Z > 0` (real), so `Re Z > 0` in particular. -/
theorem partitionFunctionComplex_re_pos_at_real
    (G : SimpleGraph ι) [Fintype G.edgeSet] (p : IsingParams ℝ) :
    0 < (partitionFunctionComplex G (p.J : ℂ) (p.h : ℂ) (p.β : ℂ)).re := by
  rw [← partitionFunction_ofReal_eq_partitionFunctionComplex G p]
  simpa using partitionFunction_pos G p

/-- **`partitionFunctionComplex` im = 0 at real parameters**. -/
theorem partitionFunctionComplex_im_zero_at_real
    (G : SimpleGraph ι) [Fintype G.edgeSet] (p : IsingParams ℝ) :
    (partitionFunctionComplex G (p.J : ℂ) (p.h : ℂ) (p.β : ℂ)).im = 0 := by
  rw [← partitionFunction_ofReal_eq_partitionFunctionComplex G p]
  simp

/-- **`Complex.log(Z)` at real parameters is real**. -/
theorem log_partitionFunctionComplex_im_zero_at_real
    (G : SimpleGraph ι) [Fintype G.edgeSet] (p : IsingParams ℝ) :
    (Complex.log (partitionFunctionComplex G (p.J : ℂ) (p.h : ℂ)
                    (p.β : ℂ))).im = 0 := by
  rw [← partitionFunction_ofReal_eq_partitionFunctionComplex G p,
    ← Complex.ofReal_log (partitionFunction_pos G p).le]
  simp

/-- `freeEnergyComplex` at real parameters is real (its im part is 0). -/
theorem freeEnergyComplex_im_zero_at_real
    (G : SimpleGraph ι) [Fintype G.edgeSet] (p : IsingParams ℝ) :
    (freeEnergyComplex G (p.J : ℂ) (p.h : ℂ) (p.β : ℂ)).im = 0 := by
  rw [freeEnergyComplex_at_real]
  simp

/-- `freeEnergyComplex.re` at real parameters equals `freeEnergy`. -/
theorem freeEnergyComplex_re_eq_freeEnergy_at_real
    (G : SimpleGraph ι) [Fintype G.edgeSet] (p : IsingParams ℝ) :
    (freeEnergyComplex G (p.J : ℂ) (p.h : ℂ) (p.β : ℂ)).re
      = freeEnergy G p := by
  rw [freeEnergyComplex_at_real]
  simp

/-- `partitionFunctionComplex` norm equals the real partition function
at real parameters. -/
theorem norm_partitionFunctionComplex_at_real
    (G : SimpleGraph ι) [Fintype G.edgeSet] (p : IsingParams ℝ) :
    ‖partitionFunctionComplex G (p.J : ℂ) (p.h : ℂ) (p.β : ℂ)‖
      = partitionFunction G p := by
  rw [← partitionFunction_ofReal_eq_partitionFunctionComplex G p,
    Complex.norm_real]
  exact abs_of_pos (partitionFunction_pos G p)

/-- `partitionFunctionComplex` is nonnegative-real-valued at real
parameters; combined with positivity, it lies in the positive reals
`(0, ∞)`. -/
theorem partitionFunctionComplex_is_pos_real_at_real
    (G : SimpleGraph ι) [Fintype G.edgeSet] (p : IsingParams ℝ) :
    ∃ x : ℝ, 0 < x ∧ partitionFunctionComplex G (p.J : ℂ) (p.h : ℂ) (p.β : ℂ)
              = (x : ℂ) :=
  ⟨partitionFunction G p, partitionFunction_pos G p,
    (partitionFunction_ofReal_eq_partitionFunctionComplex G p).symm⟩

/-- **Real-slice agreement of local-log branch**: at the real-positive
basepoint `h₀ > 0`, the local branch `g` satisfies
`g(h₀) = Real.log(Z(h₀))` as a complex number (cast of the real log),
since `Z(h₀)` is real positive. This is useful for identifying the
local branch with the real `freeEnergy` on the real axis. -/
theorem logZ_branch_at_real_basepoint
    (G : SimpleGraph ι) [Fintype G.edgeSet] (p : IsingParams ℝ) :
    Complex.log (partitionFunctionComplex G (p.J : ℂ) (p.h : ℂ) (p.β : ℂ))
      = ((Real.log (partitionFunction G p)) : ℂ) := by
  rw [← partitionFunction_ofReal_eq_partitionFunctionComplex G p,
    ← Complex.ofReal_log (partitionFunction_pos G p).le]

/-- At `h₀ > 0` real, `exp (freeEnergyComplex * |ι|)` equals the real
partition function `Z(p)` (cast to `ℂ`). A concrete application of the
local-branch construction's `exp(g) = Z` relation at the basepoint. -/
theorem exp_card_mul_freeEnergyComplex_at_real
    (G : SimpleGraph ι) [Fintype G.edgeSet] [Nonempty ι]
    (p : IsingParams ℝ) :
    Complex.exp ((Fintype.card ι : ℂ) * freeEnergyComplex G (p.J : ℂ)
                    (p.h : ℂ) (p.β : ℂ))
      = (partitionFunction G p : ℂ) := by
  unfold freeEnergyComplex
  have hN : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := ι)).ne'
  have hmul : (Fintype.card ι : ℂ)
              * ((Fintype.card ι : ℂ)⁻¹ *
                Complex.log (partitionFunctionComplex G (p.J : ℂ) (p.h : ℂ)
                              (p.β : ℂ)))
              = Complex.log (partitionFunctionComplex G (p.J : ℂ) (p.h : ℂ)
                              (p.β : ℂ)) := by field_simp
  rw [hmul, ← partitionFunction_ofReal_eq_partitionFunctionComplex G p,
    ← Complex.ofReal_log (partitionFunction_pos G p).le]
  rw [Complex.ofReal_log (partitionFunction_pos G p).le]
  exact Complex.exp_log
    (by exact_mod_cast (partitionFunction_pos G p).ne')

/-- **`partitionFunctionComplex` is continuous in `h`** restated at
real parameters (h₀ real, approached from complex side). -/
theorem partitionFunctionComplex_continuousAt_real_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (h₀ : ℝ) :
    ContinuousAt (fun h : ℂ => partitionFunctionComplex G (J : ℂ) h (β : ℂ))
      (h₀ : ℂ) :=
  (continuous_partitionFunctionComplex_h G (J : ℂ) (β : ℂ)).continuousAt

/-- `freeEnergyComplex` continuous at real positive `h₀`. -/
theorem freeEnergyComplex_continuousAt_real_pos_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (h₀ : ℝ) :
    ContinuousAt (fun h : ℂ => freeEnergyComplex G (J : ℂ) h (β : ℂ))
      (h₀ : ℂ) :=
  (freeEnergyComplex_analyticAt_h_ofReal G J h₀ β).continuousAt

/-- `freeEnergyComplex` continuous on `{h | Z(h) ∈ slitPlane}`. -/
theorem freeEnergyComplex_continuousOn_slitPlane_locus
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℂ) :
    ContinuousOn (fun h => freeEnergyComplex G J h β)
      {h : ℂ | partitionFunctionComplex G J h β ∈ Complex.slitPlane} := by
  intro h hmem
  exact ((freeEnergyComplex_analyticAt_h G J β h hmem).continuousAt).continuousWithinAt

/-- **DifferentiableOn version on the slitPlane locus**. -/
theorem freeEnergyComplex_differentiableOn_slitPlane_locus
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℂ) :
    DifferentiableOn ℂ (fun h => freeEnergyComplex G J h β)
      {h : ℂ | partitionFunctionComplex G J h β ∈ Complex.slitPlane} := fun h hmem =>
  (freeEnergyComplex_analyticAt_h G J β h hmem).differentiableAt.differentiableWithinAt

/-- `freeEnergyComplex` is `AnalyticOn` (not just `AnalyticOnNhd`) on
the slitPlane locus. -/
theorem freeEnergyComplex_analyticOn_slitPlane_locus
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℂ) :
    AnalyticOn ℂ (fun h => freeEnergyComplex G J h β)
      {h : ℂ | partitionFunctionComplex G J h β ∈ Complex.slitPlane} :=
  (freeEnergyComplex_analyticOnNhd_slitPlane_locus G J β).analyticOn

/-- **Local branch of `log Z` is continuous** on the ball inside
Lee-Yang. Immediate from analyticity. -/
theorem continuous_logZ_branch_on_ball
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ leeYangDomain) :
    ∃ g : ℂ → ℂ, ContinuousOn g (Metric.ball h₀ r) ∧
        ∀ z ∈ Metric.ball h₀ r,
          Complex.exp (g z) = partitionFunctionComplex G (J : ℂ) z (β : ℂ) := by
  obtain ⟨g, hg_ana, hg_exp⟩ :=
    exists_logZ_analyticOnNhd_ball G hβ hJ hr hsub
  exact ⟨g, hg_ana.continuousOn, hg_exp⟩

/-- **DifferentiableOn form** of the local logZ branch: the branch
`g` from `exists_logZ_analytic_branch_on_ball` is differentiable on
the ball. -/
theorem exists_logZ_differentiableOn_ball
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ leeYangDomain) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (Metric.ball h₀ r) ∧
        ∀ z ∈ Metric.ball h₀ r,
          Complex.exp (g z) = partitionFunctionComplex G (J : ℂ) z (β : ℂ) := by
  obtain ⟨g, hg_ana, hg_exp⟩ :=
    exists_logZ_analyticOnNhd_ball G hβ hJ hr hsub
  exact ⟨g, hg_ana.differentiableOn, hg_exp⟩

/-- **Free-energy local-branch `AnalyticOnNhd ball`**: the local
`f = g/|ι|` branch is analytic on the ball. -/
theorem exists_freeEnergyComplex_analyticOnNhd_ball
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) [Nonempty ι]
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ leeYangDomain) :
    ∃ f : ℂ → ℂ,
        AnalyticOnNhd ℂ f (Metric.ball h₀ r)
      ∧ ∀ z ∈ Metric.ball h₀ r,
          Complex.exp ((Fintype.card ι : ℂ) * f z)
            = partitionFunctionComplex G (J : ℂ) z (β : ℂ) := by
  obtain ⟨g, hg_ana, hg_exp⟩ :=
    exists_logZ_analyticOnNhd_ball G hβ hJ hr hsub
  refine ⟨fun z => ((Fintype.card ι : ℂ))⁻¹ * g z, ?_, ?_⟩
  · exact analyticOnNhd_const.mul hg_ana
  · intro z hz
    have hNℕ : 0 < Fintype.card ι := Fintype.card_pos
    have hN : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast hNℕ.ne'
    have hmul : (Fintype.card ι : ℂ) * ((Fintype.card ι : ℂ)⁻¹ * g z) = g z := by
      field_simp
    rw [hmul]
    exact hg_exp z hz

/-- **Strong free-energy local branch on a ball**: the branch is
`AnalyticOnNhd` on the ball, its exponential recovers `Z` throughout the
ball, and its value at the centre agrees with the principal
`freeEnergyComplex`. -/
theorem exists_freeEnergyComplex_analyticOnNhd_branch_ball_strong
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) [Nonempty ι]
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ leeYangDomain) :
    ∃ f : ℂ → ℂ,
        AnalyticOnNhd ℂ f (Metric.ball h₀ r)
      ∧ (∀ z ∈ Metric.ball h₀ r,
          Complex.exp ((Fintype.card ι : ℂ) * f z)
            = partitionFunctionComplex G (J : ℂ) z (β : ℂ))
      ∧ f h₀ = freeEnergyComplex G (J : ℂ) h₀ (β : ℂ) := by
  obtain ⟨g, hg_exp, hg_base, hg_ana⟩ :=
    exists_logZ_analytic_branch_on_ball G hβ hJ hr hsub
  refine ⟨fun z => ((Fintype.card ι : ℂ))⁻¹ * g z, ?_, ?_, ?_⟩
  · exact analyticOnNhd_const.mul hg_ana
  · intro z hz
    have hNℕ : 0 < Fintype.card ι := Fintype.card_pos
    have hN : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast hNℕ.ne'
    have hmul : (Fintype.card ι : ℂ) * ((Fintype.card ι : ℂ)⁻¹ * g z) = g z := by
      field_simp
    rw [hmul]
    exact hg_exp z hz
  · simp [freeEnergyComplex, hg_base]

/-- **DifferentiableOn form** of the local freeEnergyComplex branch. -/
theorem exists_freeEnergyComplex_differentiableOn_ball
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) [Nonempty ι]
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ leeYangDomain) :
    ∃ f : ℂ → ℂ,
        DifferentiableOn ℂ f (Metric.ball h₀ r)
      ∧ ∀ z ∈ Metric.ball h₀ r,
          Complex.exp ((Fintype.card ι : ℂ) * f z)
            = partitionFunctionComplex G (J : ℂ) z (β : ℂ) := by
  obtain ⟨f, hf_ana, hf_exp⟩ :=
    exists_freeEnergyComplex_analyticOnNhd_ball G hβ hJ hr hsub
  exact ⟨f, hf_ana.differentiableOn, hf_exp⟩

/-- `leeYangDomain` is the preimage of `(0, ∞)` under the continuous
map `h ↦ Re h - |Im h|`. -/
theorem leeYangDomain_eq_preimage :
    leeYangDomain = (fun h : ℂ => h.re - |h.im|) ⁻¹' Set.Ioi 0 := by
  ext h
  simp only [leeYangDomain, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioi]
  constructor
  · intro hlt; linarith
  · intro hlt; change |h.im| < h.re; linarith

/-- When `β = 0`, `leeYangSubdomain 0 N = leeYangDomain` for any `N`
(the strip constraint is vacuously `0 < π/2`). -/
theorem leeYangSubdomain_beta_zero (N : ℕ) :
    leeYangSubdomain (0 : ℝ) N = leeYangDomain := by
  ext h
  refine ⟨fun hh => hh.1, fun hh => ⟨hh, ?_⟩⟩
  simp only [zero_mul]
  positivity

/-- `slitPlane` locus for `partitionFunctionComplex` contains
`leeYangSubdomain`. -/
theorem leeYangSubdomain_subset_slitPlane_locus
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} (hβ : 0 < β) (J : ℝ) :
    (leeYangSubdomain β (Fintype.card ι))
      ⊆ {h : ℂ | partitionFunctionComplex G (J : ℂ) h (β : ℂ)
                  ∈ Complex.slitPlane} := fun _ hh =>
  partitionFunctionComplex_mem_slitPlane_of_leeYangSubdomain G hβ J hh.2

/-- Every point of `leeYangSubdomain` has `Z` in `slitPlane`. -/
theorem mem_slitPlane_locus_of_mem_leeYangSubdomain
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} (hβ : 0 < β) (J : ℝ) {h : ℂ}
    (hh : h ∈ leeYangSubdomain β (Fintype.card ι)) :
    partitionFunctionComplex G (J : ℂ) h (β : ℂ) ∈ Complex.slitPlane :=
  partitionFunctionComplex_mem_slitPlane_of_leeYangSubdomain G hβ J hh.2

/-- Combined: on the Lee-Yang subdomain, `Re Z > 0` and thus
`Z ∈ slitPlane`, and `f_complex` is therefore analytic. Packaged
`AnalyticOnNhd` form of the finite-volume analyticity on the
Lee-Yang subdomain. -/
theorem freeEnergyComplex_analyticOnNhd_of_leeYangSubdomain
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} (hβ : 0 < β) (J : ℝ) :
    AnalyticOnNhd ℂ (fun h => freeEnergyComplex G (J : ℂ) h (β : ℂ))
      (leeYangSubdomain β (Fintype.card ι)) :=
  freeEnergyComplex_analyticOnNhd_leeYangSubdomain G hβ J

/-- `freeEnergyComplex_analyticOnNhd_leeYangSubdomain` restated as
`AnalyticOn`. -/
theorem freeEnergyComplex_analyticOn_leeYangSubdomain
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} (hβ : 0 < β) (J : ℝ) :
    AnalyticOn ℂ (fun h => freeEnergyComplex G (J : ℂ) h (β : ℂ))
      (leeYangSubdomain β (Fintype.card ι)) :=
  (freeEnergyComplex_analyticOnNhd_leeYangSubdomain G hβ J).analyticOn

/-- `freeEnergyComplex` is continuous on `leeYangSubdomain`. -/
theorem freeEnergyComplex_continuousOn_leeYangSubdomain
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} (hβ : 0 < β) (J : ℝ) :
    ContinuousOn (fun h => freeEnergyComplex G (J : ℂ) h (β : ℂ))
      (leeYangSubdomain β (Fintype.card ι)) :=
  (freeEnergyComplex_differentiableOn_leeYangSubdomain G hβ J).continuousOn

end IsingModel
