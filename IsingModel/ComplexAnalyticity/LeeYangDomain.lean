import IsingModel.ComplexAnalyticity.Basic

/-!
# Lee-Yang Domain and Fugacity

This module is part of the split `IsingModel.ComplexAnalyticity` development.
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Complex

/-! ## Lee-Yang domain (GJ §4.6 Thm 4.6.2, PR #199)

The Lee-Yang domain for the external field is `{h ∈ ℂ | |Im h| < Re h}`.
GJ §4.6 Thm 4.6.2 states that the free energy is analytic on this domain.
The proof uses Lee-Yang nonvanishing of the Ising polynomial (existing
`lee_yang_circle`) plus a branch-selection argument.

Session-spanning infrastructure (PR #199 work file 0164):
defining the domain here; the nonvanishing and analyticity results are
added in subsequent sessions on the same branch. -/

/-- The Lee-Yang domain: complex external fields with `|Im h| < Re h`. -/
def leeYangDomain : Set ℂ := {h : ℂ | |h.im| < h.re}

/-- The Lee-Yang domain is a subset of `Complex.slitPlane` (the right
half-plane `Re h > |Im h|` is contained in `Re h > 0 ∨ Im h ≠ 0`). -/
theorem leeYangDomain_subset_slitPlane : leeYangDomain ⊆ Complex.slitPlane := by
  intro h hmem
  refine Or.inl ?_
  have hlt : |h.im| < h.re := hmem
  have hnn : (0 : ℝ) ≤ |h.im| := abs_nonneg _
  linarith

/-- The Lee-Yang domain is open in `ℂ`. The defining inequality
`|Im h| < Re h` uses continuous functions (`Complex.im`, `abs`,
`Complex.re`), so the preimage of `(0, ∞)` under the continuous
`h ↦ Re h - |Im h|` is open. -/
theorem isOpen_leeYangDomain : IsOpen leeYangDomain := by
  have hcont : Continuous (fun h : ℂ => h.re - |h.im|) := by
    exact Complex.continuous_re.sub Complex.continuous_im.abs
  have heq : leeYangDomain = (fun h : ℂ => h.re - |h.im|) ⁻¹' Set.Ioi 0 := by
    ext h
    constructor
    · intro hlt
      have : |h.im| < h.re := hlt
      change h.re - |h.im| ∈ Set.Ioi 0
      simp [Set.mem_Ioi]; linarith
    · intro hlt
      have : h.re - |h.im| > 0 := hlt
      change |h.im| < h.re
      linarith
  rw [heq]
  exact hcont.isOpen_preimage _ isOpen_Ioi

/-- The positive real axis is contained in `leeYangDomain`: if `h = h₀ > 0`
is real, then `Im h = 0 < h₀ = Re h`. This provides a canonical basepoint
from which to continue the Lee-Yang nonvanishing into the complex domain. -/
theorem real_pos_mem_leeYangDomain {h₀ : ℝ} (hpos : 0 < h₀) :
    (h₀ : ℂ) ∈ leeYangDomain := by
  change |(h₀ : ℂ).im| < (h₀ : ℂ).re
  simp [hpos]

/-- Lee-Yang fugacity map: `h ↦ e^{-2β h}`.

For the Ising partition polynomial `P(z)` (see `LeeYang.lean`), the site
fugacity is `z_k = e^{-2β h_k}`. For uniform `h`, all `z_k` coincide.
Lee-Yang nonvanishing requires `|z_k| < 1`, i.e., `|e^{-2β h}| < 1`. -/
noncomputable def leeYangFugacity (β h : ℂ) : ℂ := Complex.exp (-2 * β * h)

/-- **Fugacity norm formula**: `‖e^{-2β h}‖ = e^{-2 β · Re h}` for real `β`.
Used in Lee-Yang nonvanishing arguments: the left-hand side is the
input to `isingEdgePoly_nonvanishing_of_graph`, and this formula lets
us read off `< 1` or `≤ 1` bounds from `Re h`. -/
theorem norm_leeYangFugacity_eq (β : ℝ) (h : ℂ) :
    ‖leeYangFugacity (β : ℂ) h‖ = Real.exp (-2 * β * h.re) := by
  unfold leeYangFugacity
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- **`leeYangFugacity β` is continuous in `h`** for any fixed `β`.
`leeYangFugacity β h = exp (-2 β h)` is the composition of the linear
map `h ↦ -2β h` with the entire exponential, hence continuous. -/
theorem continuous_leeYangFugacity (β : ℂ) :
    Continuous (leeYangFugacity β) := by
  unfold leeYangFugacity
  exact Complex.continuous_exp.comp (by fun_prop)

/-- **`leeYangFugacity β` is entire** (analytic on all of `ℂ`) for any
fixed `β : ℂ`. Composition of the affine `h ↦ -2β h` with `Complex.exp`. -/
theorem analyticOnNhd_leeYangFugacity (β : ℂ) :
    AnalyticOnNhd ℂ (leeYangFugacity β) Set.univ := by
  intro z _
  unfold leeYangFugacity
  exact analyticAt_cexp.comp (by fun_prop)

/-- **Fugacity in the open unit disk on the Lee-Yang domain**:
for real `β > 0` and `h ∈ leeYangDomain` (i.e., `|Im h| < Re h`),
the fugacity `e^{-2β h}` has absolute value less than 1.

Proof: `‖e^{-2β h}‖ = e^{Re(-2β h)} = e^{-2β · Re h}`, and `Re h > 0`
on the Lee-Yang domain (from `leeYangDomain_subset_slitPlane`). -/
theorem norm_leeYangFugacity_lt_one
    {β : ℝ} (hβ : 0 < β) {h : ℂ} (hh : h ∈ leeYangDomain) :
    ‖leeYangFugacity (β : ℂ) h‖ < 1 := by
  have hreh : 0 < h.re := by
    have hlt : |h.im| < h.re := hh
    have hnn : (0 : ℝ) ≤ |h.im| := abs_nonneg _
    linarith
  unfold leeYangFugacity
  rw [Complex.norm_exp]
  have hre : (-2 * (β : ℂ) * h).re = -2 * β * h.re := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  -- want: exp(-2β Re h) < 1, i.e., -2β Re h < 0
  refine Real.exp_lt_one_iff.mpr ?_
  have : 0 < 2 * β * h.re := by positivity
  linarith

/-- `leeYangFugacity β` maps `leeYangDomain` into the open unit disk
(for real `β > 0`): constant-coefficient version of the site fugacity
vector going into `isingEdgePoly_nonvanishing_of_graph`. -/
theorem leeYangFugacity_mapsTo_ball
    {β : ℝ} (hβ : 0 < β) :
    Set.MapsTo (leeYangFugacity (β : ℂ)) leeYangDomain (Metric.ball (0 : ℂ) 1) := by
  intro h hh
  rw [Metric.mem_ball, dist_zero_right]
  exact norm_leeYangFugacity_lt_one hβ hh

/-- `leeYangFugacity β h ≠ 0`: the fugacity `e^{-2β h}` is never zero
(as the complex exponential is always non-vanishing). -/
theorem leeYangFugacity_ne_zero (β h : ℂ) : leeYangFugacity β h ≠ 0 := by
  unfold leeYangFugacity
  exact Complex.exp_ne_zero _

/-- Constant (uniform) fugacity vector at site level: `fun _ : ι => leeYangFugacity β h`.
This is the input to `isingEdgePoly_nonvanishing_of_graph` for a uniform
external field `h`. -/
noncomputable def leeYangFugacityVec (β h : ℂ) : ι → ℂ :=
  fun _ => leeYangFugacity β h

omit [Fintype ι] [DecidableEq ι] in
/-- On the Lee-Yang domain with real β > 0, every entry of the uniform
fugacity vector is in the open unit disk — the exact condition
`∀ k, ‖z k‖ < 1` required by `isingEdgePoly_nonvanishing_of_graph`. -/
theorem leeYangFugacityVec_norm_lt_one
    {β : ℝ} (hβ : 0 < β) {h : ℂ} (hh : h ∈ leeYangDomain) (k : ι) :
    ‖(leeYangFugacityVec (β : ℂ) h : ι → ℂ) k‖ < 1 := by
  exact norm_leeYangFugacity_lt_one hβ hh

/-- **Compact-uniform Lee-Yang fugacity gap**: on compact subsets of
`leeYangDomain`, the scalar fugacity `h ↦ exp (-2βh)` is uniformly separated
from the unit circle. This packages the compactness step needed before turning
Lee-Yang polynomial nonvanishing into quantitative lower logarithmic control. -/
theorem exists_leeYangFugacity_norm_le_lt_one_on_isCompact
    {β : ℝ} (hβ : 0 < β) {K : Set ℂ}
    (hK : IsCompact K) (hKsub : K ⊆ leeYangDomain) :
    ∃ r : ℝ, r < 1 ∧ ∀ h ∈ K, ‖leeYangFugacity (β : ℂ) h‖ ≤ r := by
  by_cases hne : K.Nonempty
  · rcases hK.exists_isMaxOn hne
        ((continuous_leeYangFugacity (β : ℂ)).norm.continuousOn)
      with ⟨h₀, hh₀, hmax⟩
    refine ⟨‖leeYangFugacity (β : ℂ) h₀‖,
      norm_leeYangFugacity_lt_one hβ (hKsub hh₀), ?_⟩
    intro h hh
    exact hmax hh
  · refine ⟨0, zero_lt_one, ?_⟩
    intro h hh
    exact False.elim (hne ⟨h, hh⟩)

omit [Fintype ι] [DecidableEq ι] in
/-- **Compact-uniform Lee-Yang fugacity-vector gap**: the scalar compact gap
also bounds every coordinate of the constant site-level fugacity vector. -/
theorem exists_leeYangFugacityVec_norm_le_lt_one_on_isCompact
    {β : ℝ} (hβ : 0 < β) {K : Set ℂ}
    (hK : IsCompact K) (hKsub : K ⊆ leeYangDomain) :
    ∃ r : ℝ, r < 1 ∧
      ∀ h ∈ K, ∀ k : ι, ‖(leeYangFugacityVec (β : ℂ) h : ι → ℂ) k‖ ≤ r := by
  rcases exists_leeYangFugacity_norm_le_lt_one_on_isCompact hβ hK hKsub
    with ⟨r, hr, hbound⟩
  refine ⟨r, hr, ?_⟩
  intro h hh k
  simpa [leeYangFugacityVec] using hbound h hh


end IsingModel
