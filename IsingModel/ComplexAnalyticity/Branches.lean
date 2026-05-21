import IsingModel.ComplexAnalyticity.Subdomain

/-!
# Local Log Branches

This module is part of the split `IsingModel.ComplexAnalyticity` development.
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Complex

/-! ### Toward full Lee-Yang analyticity via branch construction

The subdomain result above uses the principal branch `Complex.log`,
which is analytic only on `Complex.slitPlane`. On the full Lee-Yang
domain, `Z` is non-vanishing (PR #199), but may not stay in `slitPlane`
(winding of `Z` around `0` is not automatic from non-vanishing alone).

Morera's theorem (`DifferentiableOn.isExactOn_ball`, mathlib) gives a
local primitive of a holomorphic function on a ball, which yields a
local holomorphic branch of `log Z` on any ball inside `leeYangDomain`.
This does not immediately produce a global branch, but it shows
`freeEnergyComplex` (with a custom branch, equal to `Complex.log`
modulo `2πi` on each ball) is analytic at every point of the Lee-Yang
domain.

The clean formalisation of this branch-based finite-volume analyticity
is larger than a single session; the subdomain result above is the
concrete verified form. -/

/-- `partitionFunctionComplex ≠ 0` on every point of the Lee-Yang
domain (lifted to an `AnalyticOnNhd`-style statement by openness).
This is the global non-vanishing statement. -/
theorem partitionFunctionComplex_analyticOnNhd_leeYangDomain
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℂ) :
    AnalyticOnNhd ℂ
        (fun h' => partitionFunctionComplex G J h' β) leeYangDomain :=
  fun h _ => partitionFunctionComplex_analyticAt_h G J β h

/-- **The logarithmic derivative `Z'/Z` is analytic on the Lee-Yang
domain** (real ferromagnetic `J > 0`, real `β > 0`). `Z` is entire and
non-vanishing on `leeYangDomain` (PR #199), so `Z'/Z` is analytic there.
This is the key input to the Morera-based branch construction of `log Z`. -/
theorem logDeriv_partitionFunctionComplex_analyticOnNhd_leeYangDomain
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    AnalyticOnNhd ℂ (fun h : ℂ =>
        deriv (fun h' => partitionFunctionComplex G (J : ℂ) h' (β : ℂ)) h
          / partitionFunctionComplex G (J : ℂ) h (β : ℂ)) leeYangDomain := by
  intro h hmem
  have hZ_ne : partitionFunctionComplex G (J : ℂ) h (β : ℂ) ≠ 0 :=
    partitionFunctionComplex_ne_zero_on_leeYangDomain G hβ hJ hmem
  have hZ_ana : AnalyticAt ℂ
      (fun h' => partitionFunctionComplex G (J : ℂ) h' (β : ℂ)) h :=
    partitionFunctionComplex_analyticAt_h G (J : ℂ) (β : ℂ) h
  have hZ'_ana : AnalyticAt ℂ
      (fun h' =>
        deriv (fun h'' => partitionFunctionComplex G (J : ℂ) h'' (β : ℂ)) h')
      h := hZ_ana.deriv
  exact hZ'_ana.div hZ_ana hZ_ne

/-- **Local primitive of the log derivative on a ball inside Lee-Yang**.
For any `h₀ ∈ leeYangDomain` and any `r > 0` with `ball h₀ r ⊆ leeYangDomain`,
there exists a holomorphic function `G : ℂ → ℂ` such that on the ball,
`G' = Z'/Z`. This `G` is a local holomorphic branch of `log Z`
(up to an additive complex constant); specifically, by the identity
`(exp(G)/Z)' = 0` on the connected ball, `exp(G) = c · Z` for some
non-zero constant `c`, and we can adjust `G` by a constant so that
`exp(G) = Z` pointwise. -/
theorem exists_logZ_branch_on_ball_of_leeYangDomain
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hsub : Metric.ball h₀ r ⊆ leeYangDomain) :
    ∃ g : ℂ → ℂ, ∀ z ∈ Metric.ball h₀ r, HasDerivAt g
        (deriv (fun h'' => partitionFunctionComplex G (J : ℂ) h'' (β : ℂ)) z
          / partitionFunctionComplex G (J : ℂ) z (β : ℂ)) z := by
  have hlogDeriv_ana :
      AnalyticOnNhd ℂ (fun h : ℂ =>
          deriv (fun h' => partitionFunctionComplex G (J : ℂ) h' (β : ℂ)) h
            / partitionFunctionComplex G (J : ℂ) h (β : ℂ)) leeYangDomain :=
    logDeriv_partitionFunctionComplex_analyticOnNhd_leeYangDomain G hβ hJ
  have hlogDeriv_diffOn :
      DifferentiableOn ℂ (fun h : ℂ =>
          deriv (fun h' => partitionFunctionComplex G (J : ℂ) h' (β : ℂ)) h
            / partitionFunctionComplex G (J : ℂ) h (β : ℂ))
        (Metric.ball h₀ r) :=
    (hlogDeriv_ana.mono hsub).differentiableOn
  exact hlogDeriv_diffOn.isExactOn_ball

/-- **Normalised local log-branch of `Z` on a ball inside Lee-Yang**.
Refining `exists_logZ_branch_on_ball_of_leeYangDomain`: there exists
`g : ℂ → ℂ` with `g(h₀) = Complex.log(Z(h₀))`, `g' = Z'/Z` on the
ball, and `g` is differentiable on the ball.

The normalisation `g(h₀) = Complex.log(Z(h₀))` makes this branch
agree with the principal branch at the basepoint. The exponential
identity `exp(g) = Z` on the whole ball follows from
`(exp(g)/Z)' = 0` on the connected ball; that step is deferred to
the next commit. -/
theorem exists_normalised_logZ_branch_on_ball
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ}
    (hsub : Metric.ball h₀ r ⊆ leeYangDomain) :
    ∃ g : ℂ → ℂ, g h₀ = Complex.log
        (partitionFunctionComplex G (J : ℂ) h₀ (β : ℂ))
      ∧ ∀ z ∈ Metric.ball h₀ r, HasDerivAt g
          (deriv (fun h'' => partitionFunctionComplex G (J : ℂ) h'' (β : ℂ)) z
            / partitionFunctionComplex G (J : ℂ) z (β : ℂ)) z := by
  obtain ⟨g₀, hg₀⟩ :=
    exists_logZ_branch_on_ball_of_leeYangDomain G hβ hJ (h₀ := h₀) (r := r) hsub
  refine ⟨fun z => g₀ z - g₀ h₀ + Complex.log
      (partitionFunctionComplex G (J : ℂ) h₀ (β : ℂ)), ?_, ?_⟩
  · simp
  · intro z hz
    have hg₀z := hg₀ z hz
    have := hg₀z.sub_const (g₀ h₀)
    simpa using this.add_const (Complex.log
      (partitionFunctionComplex G (J : ℂ) h₀ (β : ℂ)))

/-- **Local holomorphic branch of `log Z` on an open ball inside
Lee-Yang** (real ferromagnetic `β > 0`, `J > 0`). On the open ball of
radius `r > 0` around `h₀` (assumed contained in `leeYangDomain`),
there is a holomorphic function `g` with `exp(g(z)) = Z(z)` pointwise
and `g(h₀) = Complex.log(Z(h₀))`.

Proof: combine the normalised primitive `g` of `Z'/Z` (from
`exists_normalised_logZ_branch_on_ball`) with the constancy argument
for `F(z) = exp(g(z))/Z(z)`: on the convex ball `F' = 0` (chain + quotient
rules), so `F` is constant; `F(h₀) = exp(log Z(h₀))/Z(h₀) = 1`. -/
theorem exists_logZ_holomorphic_branch_on_ball
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ leeYangDomain) :
    ∃ g : ℂ → ℂ,
        (∀ z ∈ Metric.ball h₀ r,
          Complex.exp (g z)
            = partitionFunctionComplex G (J : ℂ) z (β : ℂ))
      ∧ g h₀ = Complex.log
          (partitionFunctionComplex G (J : ℂ) h₀ (β : ℂ))
      ∧ ∀ z ∈ Metric.ball h₀ r, HasDerivAt g
            (deriv (fun h'' => partitionFunctionComplex G (J : ℂ) h'' (β : ℂ)) z
              / partitionFunctionComplex G (J : ℂ) z (β : ℂ)) z := by
  obtain ⟨g, hg_base, hg_deriv⟩ :=
    exists_normalised_logZ_branch_on_ball G hβ hJ (h₀ := h₀) (r := r) hsub
  refine ⟨g, ?_, hg_base, hg_deriv⟩
  -- `F z = exp(g z) / Z(z)` has derivative zero on the ball.
  set F : ℂ → ℂ := fun z => Complex.exp (g z)
      / partitionFunctionComplex G (J : ℂ) z (β : ℂ) with hF_def
  have hZ_ne : ∀ z ∈ Metric.ball h₀ r,
      partitionFunctionComplex G (J : ℂ) z (β : ℂ) ≠ 0 := fun z hz =>
    partitionFunctionComplex_ne_zero_on_leeYangDomain G hβ hJ (hsub hz)
  have hh₀_mem : h₀ ∈ Metric.ball h₀ r := Metric.mem_ball_self hr
  have hF_deriv : ∀ z ∈ Metric.ball h₀ r, HasDerivAt F 0 z := by
    intro z hz
    have hgz := hg_deriv z hz
    have hZz_ne := hZ_ne z hz
    have hZ_diff : DifferentiableAt ℂ
        (fun w => partitionFunctionComplex G (J : ℂ) w (β : ℂ)) z :=
      (partitionFunctionComplex_analyticAt_h G (J : ℂ) (β : ℂ) z).differentiableAt
    have hZ_deriv : HasDerivAt
        (fun w => partitionFunctionComplex G (J : ℂ) w (β : ℂ))
        (deriv (fun w => partitionFunctionComplex G (J : ℂ) w (β : ℂ)) z)
        z := hZ_diff.hasDerivAt
    have hexp_deriv : HasDerivAt (fun w => Complex.exp (g w))
        (Complex.exp (g z)
          * (deriv (fun w =>
              partitionFunctionComplex G (J : ℂ) w (β : ℂ)) z
            / partitionFunctionComplex G (J : ℂ) z (β : ℂ))) z := hgz.cexp
    have h_quot := hexp_deriv.div hZ_deriv hZz_ne
    -- Numerator evaluates to zero: cexp(g z) · (Z'/Z) · Z − cexp(g z) · Z' = 0.
    have hnum_zero :
        Complex.exp (g z)
          * (deriv (fun w =>
              partitionFunctionComplex G (J : ℂ) w (β : ℂ)) z
            / partitionFunctionComplex G (J : ℂ) z (β : ℂ))
          * partitionFunctionComplex G (J : ℂ) z (β : ℂ)
          - Complex.exp (g z)
            * deriv (fun w =>
                partitionFunctionComplex G (J : ℂ) w (β : ℂ)) z = 0 := by
      field_simp; ring
    have h_quot' := h_quot
    rw [show
        (Complex.exp (g z)
              * (deriv (fun w =>
                  partitionFunctionComplex G (J : ℂ) w (β : ℂ)) z
                / partitionFunctionComplex G (J : ℂ) z (β : ℂ))
            * partitionFunctionComplex G (J : ℂ) z (β : ℂ)
          - Complex.exp (g z)
              * deriv (fun w =>
                  partitionFunctionComplex G (J : ℂ) w (β : ℂ)) z)
          / partitionFunctionComplex G (J : ℂ) z (β : ℂ) ^ 2 = 0 from by
        rw [hnum_zero]; simp] at h_quot'
    exact h_quot'
  -- Convexity of the ball + zero fderivWithin ⇒ F is constant.
  have hconvex : Convex ℝ (Metric.ball h₀ r) := convex_ball _ _
  have hopen : IsOpen (Metric.ball h₀ r) := Metric.isOpen_ball
  have hdiffOn : DifferentiableOn ℂ F (Metric.ball h₀ r) := fun w hw =>
    (hF_deriv w hw).differentiableAt.differentiableWithinAt
  have hfderiv_zero : ∀ w ∈ Metric.ball h₀ r,
      fderivWithin ℂ F (Metric.ball h₀ r) w = 0 := by
    intro w hw
    have h1 : HasFDerivWithinAt F
        (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) 0)
        (Metric.ball h₀ r) w :=
      ((hF_deriv w hw).hasFDerivAt).hasFDerivWithinAt
    have huniq : UniqueDiffWithinAt ℂ (Metric.ball h₀ r) w :=
      hopen.uniqueDiffOn w hw
    rw [h1.fderivWithin huniq]; simp
  have hF_const : ∀ z ∈ Metric.ball h₀ r, F z = F h₀ := fun z hz =>
    hconvex.is_const_of_fderivWithin_eq_zero hdiffOn hfderiv_zero hz hh₀_mem
  -- F(h₀) = exp(log Z(h₀)) / Z(h₀) = 1.
  have hF_h₀ : F h₀ = 1 := by
    simp only [hF_def, hg_base]
    rw [Complex.exp_log (hZ_ne h₀ hh₀_mem)]
    exact div_self (hZ_ne h₀ hh₀_mem)
  intro z hz
  have hconst : F z = 1 := (hF_const z hz).trans hF_h₀
  have hZz_ne := hZ_ne z hz
  have hquot : Complex.exp (g z)
        / partitionFunctionComplex G (J : ℂ) z (β : ℂ) = 1 := hconst
  field_simp at hquot
  exact hquot

/-- The local log branch `g` (obtained from `Z'/Z` primitive via Morera)
is itself analytic on the ball. Any function that is `DifferentiableOn`
on an open set in `ℂ` is `AnalyticOnNhd` there (mathlib). -/
theorem exists_logZ_analytic_branch_on_ball
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ leeYangDomain) :
    ∃ g : ℂ → ℂ,
        (∀ z ∈ Metric.ball h₀ r,
          Complex.exp (g z)
            = partitionFunctionComplex G (J : ℂ) z (β : ℂ))
      ∧ g h₀ = Complex.log
          (partitionFunctionComplex G (J : ℂ) h₀ (β : ℂ))
      ∧ AnalyticOnNhd ℂ g (Metric.ball h₀ r) := by
  obtain ⟨g, hg_exp, hg_base, hg_deriv⟩ :=
    exists_logZ_holomorphic_branch_on_ball G hβ hJ (h₀ := h₀) (r := r) hr hsub
  refine ⟨g, hg_exp, hg_base, ?_⟩
  have hdiffOn : DifferentiableOn ℂ g (Metric.ball h₀ r) := fun z hz =>
    (hg_deriv z hz).differentiableAt.differentiableWithinAt
  exact hdiffOn.analyticOnNhd Metric.isOpen_ball

/-- **Pointwise local analytic log branch of `Z` at every point of the
Lee-Yang domain**. Since `leeYangDomain` is open, for every `h₀` there
is a ball around it inside the domain, and
`exists_logZ_analytic_branch_on_ball` provides a local analytic log
of `Z` on that ball (hence in particular analytic at `h₀`).

This is the finite-volume content of GJ §4.6 Thm 4.6.2:
at every `h₀ ∈ leeYangDomain`, `log Z` (as a holomorphic function
germ; equivalently the principal branch plus a locally-constant
`2πi·k` shift) is analytic. The principal `Complex.log Z` may
differ from this branch by `2πi·k` where `Z` crosses the negative
real axis; the local analytic branch constructed here is continuous
across such crossings. -/
theorem exists_logZ_analyticAt_of_leeYangDomain
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} (hmem : h₀ ∈ leeYangDomain) :
    ∃ g : ℂ → ℂ,
        AnalyticAt ℂ g h₀
      ∧ Complex.exp (g h₀)
          = partitionFunctionComplex G (J : ℂ) h₀ (β : ℂ)
      ∧ g h₀ = Complex.log
          (partitionFunctionComplex G (J : ℂ) h₀ (β : ℂ)) := by
  obtain ⟨r, hr_pos, hr_sub⟩ :=
    Metric.isOpen_iff.mp isOpen_leeYangDomain h₀ hmem
  obtain ⟨g, hg_exp, hg_base, hg_ana⟩ :=
    exists_logZ_analytic_branch_on_ball G hβ hJ (h₀ := h₀) (r := r) hr_pos hr_sub
  refine ⟨g, hg_ana h₀ (Metric.mem_ball_self hr_pos),
    hg_exp h₀ (Metric.mem_ball_self hr_pos), hg_base⟩

/-- **GJ §4.6 Thm 4.6.2 finite-volume (local-branch form)**: at every
`h₀ ∈ leeYangDomain` (real ferromagnetic `β > 0`, `J > 0`), the
free energy admits a local analytic representation. Concretely:
there exists `f : ℂ → ℂ` analytic at `h₀` with `exp(|ι| · f(h₀)) = Z(h₀)`
and `f(h₀) = freeEnergyComplex G (J : ℂ) h₀ (β : ℂ)`.

This is the finite-volume content of Thm 4.6.2 in the branch-adapted
sense. The principal-branch `freeEnergyComplex` may be discontinuous at
points where `Z` crosses the negative real axis; the local branch `f`
is analytic across such crossings. -/
theorem exists_freeEnergyComplex_analyticAt_branch_of_leeYangDomain
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) [Nonempty ι]
    {h₀ : ℂ} (hmem : h₀ ∈ leeYangDomain) :
    ∃ f : ℂ → ℂ,
        AnalyticAt ℂ f h₀
      ∧ Complex.exp ((Fintype.card ι : ℂ) * f h₀)
          = partitionFunctionComplex G (J : ℂ) h₀ (β : ℂ)
      ∧ f h₀ = freeEnergyComplex G (J : ℂ) h₀ (β : ℂ) := by
  obtain ⟨g, hg_ana, hg_exp, hg_base⟩ :=
    exists_logZ_analyticAt_of_leeYangDomain G hβ hJ hmem
  refine ⟨fun z => ((Fintype.card ι : ℂ))⁻¹ * g z, ?_, ?_, ?_⟩
  · exact analyticAt_const.mul hg_ana
  · have hNℕ : 0 < Fintype.card ι := Fintype.card_pos
    have hN : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast hNℕ.ne'
    have hmul : (Fintype.card ι : ℂ) * ((Fintype.card ι : ℂ)⁻¹ * g h₀)
                = g h₀ := by field_simp
    rw [hmul]; exact hg_exp
  · unfold freeEnergyComplex; simp [hg_base]


end IsingModel
