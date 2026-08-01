import IsingModel.ComplexAnalyticity.Bounds

/-!
# Lee-Yang Domain Geometry

This module is part of the split `IsingModel.ComplexAnalyticity` development.
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Complex

/-- The Lee-Yang domain is convex (hence connected). -/
theorem convex_leeYangDomain : Convex ℝ leeYangDomain := by
  intro x hxmem y hymem a b ha hb hab
  change |((a : ℝ) • x + (b : ℝ) • y).im| < ((a : ℝ) • x + (b : ℝ) • y).re
  have hx : |x.im| < x.re := hxmem
  have hy : |y.im| < y.re := hymem
  simp only [Complex.add_im, Complex.smul_im, Complex.add_re, Complex.smul_re]
  calc |a * x.im + b * y.im|
      ≤ |a * x.im| + |b * y.im| := abs_add_le _ _
    _ = a * |x.im| + b * |y.im| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ < a * x.re + b * y.re := by
        rcases eq_or_lt_of_le ha with rfl | ha_pos
        · rcases eq_or_lt_of_le hb with rfl | hb_pos
          · simp at hab
          · simpa using mul_lt_mul_of_pos_left hy hb_pos
        · rcases eq_or_lt_of_le hb with rfl | hb_pos
          · simpa using mul_lt_mul_of_pos_left hx ha_pos
          · exact add_lt_add (mul_lt_mul_of_pos_left hx ha_pos)
              (mul_lt_mul_of_pos_left hy hb_pos)

/-- The Lee-Yang domain is preconnected (via convex ⇒ connected). -/
theorem isPreconnected_leeYangDomain : IsPreconnected leeYangDomain :=
  convex_leeYangDomain.isPreconnected

/-- The Lee-Yang domain is nonempty (contains `(1 : ℂ)`). -/
theorem leeYangDomain_nonempty : leeYangDomain.Nonempty :=
  ⟨(1 : ℂ), real_pos_mem_leeYangDomain (by norm_num : (0 : ℝ) < 1)⟩

/-- The Lee-Yang domain is connected. -/
theorem isConnected_leeYangDomain : IsConnected leeYangDomain :=
  ⟨leeYangDomain_nonempty, isPreconnected_leeYangDomain⟩

/-- **Star-convex Lee-Yang domain** at `(1 : ℂ)`: convex + contains `1`. -/
theorem starConvex_leeYangDomain : StarConvex ℝ (1 : ℂ) leeYangDomain :=
  convex_leeYangDomain.starConvex (real_pos_mem_leeYangDomain (by norm_num))

/-- `leeYangDomain` contains an open ball around each of its points
(direct restatement of `isOpen_leeYangDomain`). -/
theorem leeYangDomain_ball_subset {h₀ : ℂ} (hmem : h₀ ∈ leeYangDomain) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball h₀ r ⊆ leeYangDomain :=
  Metric.isOpen_iff.mp isOpen_leeYangDomain h₀ hmem

/-- `leeYangDomain` contains a positive-radius closed ball around each of its
points. This half-radius form is convenient for local compactness handoffs. -/
theorem leeYangDomain_closedBall_subset {h₀ : ℂ} (hmem : h₀ ∈ leeYangDomain) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall h₀ ρ ⊆ leeYangDomain := by
  rcases leeYangDomain_ball_subset hmem with ⟨r, hr, hsub⟩
  refine ⟨r / 2, half_pos hr, ?_⟩
  exact (Metric.closedBall_subset_ball (half_lt_self hr)).trans hsub

/-- `leeYangSubdomain` is non-empty for `β ≥ 0` (contains `(1 : ℂ)`). -/
theorem leeYangSubdomain_nonempty (β : ℝ) (N : ℕ) :
    (leeYangSubdomain β N).Nonempty :=
  ⟨(1 : ℂ), real_pos_mem_leeYangSubdomain β N (by norm_num)⟩

/-- `leeYangDomain` membership implies `slitPlane` membership. -/
theorem mem_slitPlane_of_mem_leeYangDomain {h : ℂ} (hh : h ∈ leeYangDomain) :
    h ∈ Complex.slitPlane :=
  leeYangDomain_subset_slitPlane hh

/-- `leeYangSubdomain` membership implies `slitPlane` membership. -/
theorem mem_slitPlane_of_mem_leeYangSubdomain (β : ℝ) (N : ℕ)
    {h : ℂ} (hh : h ∈ leeYangSubdomain β N) : h ∈ Complex.slitPlane :=
  leeYangDomain_subset_slitPlane (leeYangSubdomain_subset_leeYangDomain β N hh)

/-- `partitionFunctionComplex` is non-zero on `leeYangDomain` gives
`∈ Complex.slitPlane`? No — the partition function may still lie on the
negative real axis at some `h`. This is a helper stating explicitly the
gap: the value `Z(J, h, β)` lies in `ℂ \ {0}` (non-vanishing) but not
automatically in `slitPlane`. -/
theorem partitionFunctionComplex_ne_zero_not_iff_slitPlane
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℂ) (h : ℂ)
    (hne : partitionFunctionComplex G J h β ≠ 0) :
    partitionFunctionComplex G J h β ∈ ({z : ℂ | z ≠ 0}) := hne

/-- **AnalyticOnNhd form**: `partitionFunctionComplex` is jointly
entire (already known for each variable separately). This provides
an AnalyticOnNhd statement on any open set, including `leeYangDomain`. -/
theorem partitionFunctionComplex_analyticOnNhd_univ_h
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℂ) :
    AnalyticOnNhd ℂ (fun h => partitionFunctionComplex G J h β) Set.univ :=
  fun h _ => partitionFunctionComplex_analyticAt_h G J β h

/-- `freeEnergyComplex` is AnalyticOnNhd on the set of `h` where
`Z(J, h, β) ∈ slitPlane`. This is an automatic restriction of the
pointwise statement to the analyticity locus. -/
theorem freeEnergyComplex_analyticOnNhd_slitPlane_locus
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℂ) :
    AnalyticOnNhd ℂ (fun h => freeEnergyComplex G J h β)
      {h : ℂ | partitionFunctionComplex G J h β ∈ Complex.slitPlane} := by
  intro h hmem
  exact freeEnergyComplex_analyticAt_h G J β h hmem

/-- The analyticity locus
`{h | partitionFunctionComplex G J h β ∈ Complex.slitPlane}` is open
(preimage of open `Complex.slitPlane` by continuous
`partitionFunctionComplex`). -/
theorem isOpen_freeEnergy_analyticity_locus
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℂ) :
    IsOpen {h : ℂ | partitionFunctionComplex G J h β ∈ Complex.slitPlane} := by
  have hcont : Continuous (fun h => partitionFunctionComplex G J h β) :=
    continuous_iff_continuousAt.mpr fun h =>
      (partitionFunctionComplex_analyticAt_h G J β h).continuousAt
  exact hcont.isOpen_preimage _ Complex.isOpen_slitPlane

/-- **`Continuous` form of `partitionFunctionComplex` in `h`**. -/
theorem continuous_partitionFunctionComplex_h
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℂ) :
    Continuous (fun h => partitionFunctionComplex G J h β) :=
  continuous_iff_continuousAt.mpr fun h =>
    (partitionFunctionComplex_analyticAt_h G J β h).continuousAt

/-- `Continuous` form in `J`. -/
theorem continuous_partitionFunctionComplex_J
    (G : SimpleGraph ι) [Fintype G.edgeSet] (h β : ℂ) :
    Continuous (fun J => partitionFunctionComplex G J h β) :=
  continuous_iff_continuousAt.mpr fun J =>
    (partitionFunctionComplex_analyticAt_J G h β J).continuousAt

/-- `Continuous` form in `β`. -/
theorem continuous_partitionFunctionComplex_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J h : ℂ) :
    Continuous (fun β => partitionFunctionComplex G J h β) :=
  continuous_iff_continuousAt.mpr fun β =>
    (partitionFunctionComplex_analyticAt_beta G J h β).continuousAt

/-- Continuous form of `partitionFunctionComplex` jointly in
`(J, h, β) : ℂ × ℂ × ℂ`. -/
theorem continuous_partitionFunctionComplex_joint
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Continuous (fun z : ℂ × ℂ × ℂ =>
      partitionFunctionComplex G z.1 z.2.1 z.2.2) :=
  continuous_iff_continuousAt.mpr fun z =>
    (partitionFunctionComplex_analyticAt_joint G z).continuousAt

/-- `partitionFunctionComplex` is jointly holomorphic (i.e.
`AnalyticOnNhd ℂ` on all of `ℂ × ℂ × ℂ`). -/
theorem partitionFunctionComplex_analyticOnNhd_univ_joint
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    AnalyticOnNhd ℂ
      (fun z : ℂ × ℂ × ℂ => partitionFunctionComplex G z.1 z.2.1 z.2.2)
      Set.univ :=
  fun z _ => partitionFunctionComplex_analyticAt_joint G z

/-- `partitionFunctionComplex_ne_zero_on_leeYangDomain` (PR #199): for
real ferromagnetic `J > 0`, `β > 0`, the complex partition function
is non-zero everywhere on `leeYangDomain`. Restatement as a
`Set.MapsTo` style result. -/
theorem partitionFunctionComplex_mapsTo_ne_zero_leeYangDomain
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    Set.MapsTo (fun h : ℂ => partitionFunctionComplex G (J : ℂ) h (β : ℂ))
      leeYangDomain {z : ℂ | z ≠ 0} := fun _ hh =>
  partitionFunctionComplex_ne_zero_on_leeYangDomain G hβ hJ hh

/-- Intersection of `leeYangDomain` and `leeYangSubdomain` is just
`leeYangSubdomain` (which is a subset of the former). -/
theorem inter_leeYangDomain_leeYangSubdomain (β : ℝ) (N : ℕ) :
    leeYangDomain ∩ leeYangSubdomain β N = leeYangSubdomain β N :=
  Set.inter_eq_right.mpr (leeYangSubdomain_subset_leeYangDomain β N)

/-- `leeYangSubdomain β 0 = leeYangDomain` since `β · |Im h| · 0 = 0 < π/2`
is automatic. -/
theorem leeYangSubdomain_zero (β : ℝ) :
    leeYangSubdomain β 0 = leeYangDomain := by
  ext h
  refine ⟨fun hh => hh.1, fun hh => ⟨hh, ?_⟩⟩
  simp only [Nat.cast_zero, mul_zero]
  positivity

/-- `leeYangSubdomain β N` is monotone decreasing in `N` (for `β > 0`):
larger `N` gives a tighter constraint on `|Im h|`. -/
theorem leeYangSubdomain_anti_N_of_pos {β : ℝ} (hβ : 0 < β)
    {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) :
    leeYangSubdomain β N₂ ⊆ leeYangSubdomain β N₁ := by
  intro h hh
  refine ⟨hh.1, ?_⟩
  calc β * |h.im| * (N₁ : ℝ)
      ≤ β * |h.im| * (N₂ : ℝ) := by
        have hnn : 0 ≤ β * |h.im| := mul_nonneg hβ.le (abs_nonneg _)
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hN) hnn
    _ < Real.pi / 2 := hh.2

/-- **Complex field at real imaginary part 0 lies in `leeYangSubdomain`**
iff the real part is positive (the `β · |Im h| · N` constraint is
vacuous when `Im h = 0`). -/
theorem mem_leeYangSubdomain_of_im_zero {β : ℝ} (N : ℕ) {h : ℂ}
    (him : h.im = 0) (hpos : 0 < h.re) :
    h ∈ leeYangSubdomain β N := by
  refine ⟨?_, ?_⟩
  · change |h.im| < h.re
    rw [him]; simpa using hpos
  · rw [him, abs_zero, mul_zero, zero_mul]; positivity

omit [Fintype ι] [DecidableEq ι] in
/-- `leeYangFugacityVec (β : ℂ) h = (fun _ => exp(-2β h))` is analytic
in `h` for fixed `β`. -/
theorem leeYangFugacityVec_analyticAt_h
    (β : ℂ) (h₀ : ℂ) (i : ι) :
    AnalyticAt ℂ (fun h => leeYangFugacityVec β h i) h₀ := by
  unfold leeYangFugacityVec leeYangFugacity
  exact analyticAt_cexp.comp (by fun_prop)

omit [Fintype ι] [DecidableEq ι] in
/-- `leeYangFugacityVec` is continuous in `h` for fixed `β : ℂ`. -/
theorem continuous_leeYangFugacityVec_h (β : ℂ) (i : ι) :
    Continuous (fun h => leeYangFugacityVec β h i) :=
  continuous_iff_continuousAt.mpr fun h =>
    (leeYangFugacityVec_analyticAt_h β h i).continuousAt

/-- Product-form rewrite of `isingEdgePoly` evaluation at the uniform
fugacity vector: `P_E(z(h))` as a specific function of `h`. -/
theorem isingEdgePoly_eval_leeYangFugacityVec_eq
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) (β h : ℂ) :
    (isingEdgePoly (graphToEdgeList G t)).eval (leeYangFugacityVec β h) =
      ∑ X : Finset ι,
        ((graphToEdgeList G t).map fun e => edgeWeight e.1 e.2.1 e.2.2 X).prod *
          ∏ _i ∈ X, leeYangFugacity β h := by
  unfold MultilinPoly.eval isingEdgePoly leeYangFugacityVec
  refine Finset.sum_congr rfl (fun X _ => ?_)
  rfl

/-- `leeYangNormalization` jointly analytic in (β, J, h): wraps
`leeYangNormalization_analyticAt_joint` as `AnalyticOnNhd`. -/
theorem leeYangNormalization_analyticOnNhd_univ (edgeCount siteCount : ℕ) :
    AnalyticOnNhd ℂ (fun z : ℂ × ℂ × ℂ =>
        leeYangNormalization z.2.2 z.1 z.2.1 edgeCount siteCount) Set.univ :=
  fun z _ => leeYangNormalization_analyticAt_joint edgeCount siteCount z

/-- `leeYangNormalization β J h |E| |ι| ≠ 0` as an `AnalyticOnNhd`
support: the normalization never vanishes. -/
theorem leeYangNormalization_nonzero_on_univ (edgeCount siteCount : ℕ)
    (β J h : ℂ) :
    leeYangNormalization β J h edgeCount siteCount ∈ ({z : ℂ | z ≠ 0}) :=
  leeYangNormalization_ne_zero β J h edgeCount siteCount

/-- **AnalyticOnNhd form of the local log branch** on any ball
contained in `leeYangDomain`. Packages
`exists_logZ_analytic_branch_on_ball` as an `AnalyticOnNhd ℂ g (ball h₀ r)`
statement. -/
theorem exists_logZ_analyticOnNhd_ball
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ leeYangDomain) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball h₀ r)
      ∧ ∀ z ∈ Metric.ball h₀ r,
          Complex.exp (g z) = partitionFunctionComplex G (J : ℂ) z (β : ℂ) := by
  obtain ⟨g, hg_exp, _hg_base, hg_ana⟩ :=
    exists_logZ_analytic_branch_on_ball G hβ hJ (h₀ := h₀) (r := r) hr hsub
  exact ⟨g, hg_ana, hg_exp⟩

omit [Fintype ι] [DecidableEq ι] in
/-- **`freeEnergyComplex` local-branch analyticAt via scaling**:
from the existence of `g` with `exp g = Z` analytic at `h₀`, scaling
by `|ι|⁻¹` gives an analytic `f = g/|ι|` with `exp(|ι|·f) = Z`. -/
theorem freeEnergyComplex_analyticAt_from_logZ_branch
    (c : ℂ) {g : ℂ → ℂ} {h₀ : ℂ}
    (hg_ana : AnalyticAt ℂ g h₀) :
    AnalyticAt ℂ (fun h => c * g h) h₀ :=
  analyticAt_const.mul hg_ana

end IsingModel
