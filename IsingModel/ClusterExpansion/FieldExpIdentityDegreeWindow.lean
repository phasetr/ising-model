import IsingModel.ClusterExpansion.FieldMayerCouplingTower
import IsingModel.ClusterExpansion.FieldPolymerComplexNonvanishing
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Degree-window field `exp` identity via real-`a` analytic continuation
(GJ §17.6.1, field cluster expansion, brick F2)

Brick F2 of the minimal (pair-only) field cluster-expansion route toward
Glimm–Jaffe (GJ) *Quantum Physics*, 2nd ed., §17.6.1, pp. 313–314 (the `∂/∂h`
infinite-volume differentiability / `h`-analyticity of the two-point function in
the high-temperature window).

Brick 6 (`FieldPolymerComplexNonvanishing.lean`) proved the complex field `exp`
identity `fieldPolymerZℂ G a b = Complex.exp (∑' n, fieldMayerExpansionTermℂ G n a b)`
only on the *extensive* window `hact_star : e·∑_P (Mr²·|tanh a|)^|P| < 1`, whose left
side grows like the volume `|ι|` and hence shrinks the admissible `a`-window to zero
as `|ι| → ∞`.  This file upgrades it to the *degree window* `(W_Δ)` — a condition on
`(Δ = G.maxDegree, a, R)` only, volume-uniform — by *analytic continuation in the real
coupling `a`* on the preconnected interval `Set.Ico 0 A`, using the
coupling-complexified holomorphic tower F2-pre (`FieldMayerCouplingTower.lean`).

The four continuation steps:

* **Step 0** (`analyticOnNhd_ctanh_ofReal`): `a ↦ Complex.tanh (↑a)` is `AnalyticOnNhd ℝ`
  on all of `ℝ` (`ofReal` is `ℝ`-analytic, `Complex.tanh` is holomorphic off the
  `cosh`-zeros, and `cosh (↑a) = ↑(Real.cosh a) ≠ 0`).
* **F2a** (`fieldMayerExpansionTermℂ_tsum_analyticOnNhd_real_a`): the RHS `tsum` is
  `AnalyticOnNhd ℝ` in `a` on `Ico 0 A`, obtained by *composing* F2-pre's
  `τ`-holomorphy (`fieldMayerExpansionTermℂCoupling_tsum_analyticOnNhd`, restricted to
  `ℝ`) with Step 0 and rewriting through the bridge
  `fieldMayerExpansionTermℂCoupling_tanh_eq`.
* **F2b** (`fieldPolymerZℂ_eq_exp_eventually_a`): the small-`a` seed — brick 6 applies
  for all `a` near `0` (its window hypotheses hold as `a → 0` since `tanh 0 = 0`).
* **F2c** (`fieldPolymerZℂ_eq_exp_tsum_of_degree_window`): the analytic-continuation
  capstone — the LHS `a ↦ fieldPolymerZℂ G a b` is a finite polynomial in
  `Complex.tanh (↑a)` hence `ℝ`-analytic, the RHS is `Complex.exp ∘ F2a`, they agree
  near `0` (F2b), so `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` spreads the
  identity across `Ico 0 A`.
* **F2d** (`fieldPolymerZℂ_ne_zero_of_degree_window`): non-vanishing, immediate from
  the identity and `Complex.exp_ne_zero`.

## References
- Friedli–Velenik §5.3, Proposition 5.3, gives the formal Mayer/Ursell identity;
  §5.4, Theorem 5.4, p. 224, gives convergence, and §5.7.3 is the `h = 0`
  application.
- Friedli–Velenik Exercise 5.8, p. 238, and its Appendix C solution, p. 531,
  give the exact real-field weight. The complex analytic continuation is a
  project extension.
-/

namespace IsingModel

open Finset Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Step 0: `ℝ`-analyticity of `a ↦ Complex.tanh (↑a)` and real-`tanh` monotonicity -/

/-- **`Real.tanh` is monotone**: `x ≤ y → Real.tanh x ≤ Real.tanh y`.  From
`tanh = sinh / cosh` (`Real.tanh_eq_sinh_div_cosh`, `cosh > 0`) and
`tanh y − tanh x = sinh (y − x) / (cosh x·cosh y) ≥ 0` (`Real.sinh_sub`,
`Real.sinh_nonneg_iff`).  Mathlib exports no `Real.tanh` monotonicity lemma; needed for
the `MapsTo Ico 0 A → ball 0 ρ` estimate of F2a. -/
theorem real_tanh_le_tanh {x y : ℝ} (hxy : x ≤ y) : Real.tanh x ≤ Real.tanh y := by
  have hcx := Real.cosh_pos x
  have hcy := Real.cosh_pos y
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, ← sub_nonneg]
  have h : Real.sinh y / Real.cosh y - Real.sinh x / Real.cosh x
      = Real.sinh (y - x) / (Real.cosh x * Real.cosh y) := by
    rw [Real.sinh_sub]; field_simp
  rw [h]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr (sub_nonneg.mpr hxy)) (by positivity)

set_option backward.isDefEq.respectTransparency false in
/-- **Step 0: `a ↦ Complex.tanh (↑a)` is `ℝ`-analytic on `ℝ`** (GJ §17.6.1, brick F2).
`Complex.tanh = sinh / cosh` is holomorphic on the open set `{z | cosh z ≠ 0}`
(`DifferentiableOn.analyticOnNhd`), the `ℝ`-analytic embedding
`ofReal` (`Complex.ofRealCLM.analyticOnNhd`) maps `ℝ` into it
(`cosh (↑a) = ↑(Real.cosh a) ≠ 0`, `Real.cosh_pos`), so
`AnalyticOnNhd.restrictScalars` + `AnalyticOnNhd.comp` give the
`ℝ`-analytic composite.  The `ℝ`-analytic coupling embedding underlying both F2a and the
LHS of F2c.  The `set_option backward.isDefEq.respectTransparency false` mirrors mathlib's
`AnalyticOnNhd.re_ofReal` and is required for `AnalyticOnNhd.restrictScalars` to synthesize
`IsScalarTower ℝ ℂ ℂ`. -/
theorem analyticOnNhd_ctanh_ofReal :
    AnalyticOnNhd ℝ (fun a : ℝ => Complex.tanh (a : ℂ)) Set.univ := by
  have hopen : IsOpen {z : ℂ | Complex.cosh z ≠ 0} :=
    isOpen_ne_fun Complex.differentiable_cosh.continuous continuous_const
  have htanh_c : AnalyticOnNhd ℂ Complex.tanh {z : ℂ | Complex.cosh z ≠ 0} := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hopen
    exact ((Complex.differentiable_sinh w).div (Complex.differentiable_cosh w)
      hw).differentiableWithinAt
  have hmaps : Set.MapsTo (fun a : ℝ => (a : ℂ)) Set.univ {z : ℂ | Complex.cosh z ≠ 0} := by
    intro a _
    simp only [Set.mem_setOf_eq, ← Complex.ofReal_cosh]
    exact_mod_cast (Real.cosh_pos a).ne'
  have hofReal : AnalyticOnNhd ℝ (fun a : ℝ => (a : ℂ)) Set.univ :=
    Complex.ofRealCLM.analyticOnNhd Set.univ
  exact (htanh_c.restrictScalars (𝕜 := ℝ)).comp hofReal hmaps

/-! ## F2a: real-`a` analyticity of the RHS `tsum` -/

set_option backward.isDefEq.respectTransparency false in
/-- **F2a: the field Mayer `tsum` is real-`a`-analytic on `Ico 0 A`** (GJ §17.6.1,
brick F2).  For fixed `b` and `ρ` with the degree window at radius `ρ`
(`hkp`, `hρwin`) and `Real.tanh A < ρ`, the map
`a ↦ ∑' n, fieldMayerExpansionTermℂ G n a b` is `AnalyticOnNhd ℝ` on `Set.Ico 0 A`.

Composition: F2-pre's coupling `τ`-holomorphy
(`fieldMayerExpansionTermℂCoupling_tsum_analyticOnNhd`, `restrictScalars ℝ`) precomposed
with Step 0 (`analyticOnNhd_ctanh_ofReal`), which maps `Ico 0 A` into `Metric.ball 0 ρ`
(`Complex.tanh (↑a) = ↑(Real.tanh a)`, `|Real.tanh a| ≤ Real.tanh A < ρ` via
`real_tanh_nonneg`/`real_tanh_le_tanh`).  The bridge
`fieldMayerExpansionTermℂCoupling_tanh_eq` rewrites the composite to the target `tsum`.

The `set_option backward.isDefEq.respectTransparency false` mirrors mathlib's
`AnalyticOnNhd.re_ofReal` and is required for `AnalyticOnNhd.restrictScalars` to
synthesize `IsScalarTower ℝ ℂ ℂ` for the normed module structures. -/
theorem fieldMayerExpansionTermℂ_tsum_analyticOnNhd_real_a (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (b : ℂ) {A ρ : ℝ} (hρ0 : 0 < ρ)
    (htanhA : Real.tanh A < ρ)
    (hkp : (G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ)) < 1)
    (hρwin : 8 * ((G.maxDegree : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ)))
        / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ))) ^ 2 < 1) :
    AnalyticOnNhd ℝ (fun a : ℝ => ∑' n, fieldMayerExpansionTermℂ G n a b)
      (Set.Ico 0 A) := by
  have hcoup := fieldMayerExpansionTermℂCoupling_tsum_analyticOnNhd G b hρ0 hkp hρwin
  have hinner : AnalyticOnNhd ℝ (fun a : ℝ => Complex.tanh (a : ℂ)) (Set.Ico 0 A) :=
    analyticOnNhd_ctanh_ofReal.mono (Set.subset_univ _)
  have hmaps : Set.MapsTo (fun a : ℝ => Complex.tanh (a : ℂ)) (Set.Ico 0 A)
      (Metric.ball 0 ρ) := by
    intro a ha
    simp only [Metric.mem_ball, dist_zero_right, ← Complex.ofReal_tanh, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_of_nonneg (real_tanh_nonneg ha.1)]
    exact lt_of_le_of_lt (real_tanh_le_tanh (le_of_lt ha.2)) htanhA
  have hcomp := (hcoup.restrictScalars (𝕜 := ℝ)).comp hinner hmaps
  have heq : (fun a : ℝ => ∑' n, fieldMayerExpansionTermℂ G n a b)
      = (fun τ : ℂ => ∑' n, fieldMayerExpansionTermℂCoupling G n τ b)
          ∘ fun a : ℝ => Complex.tanh (a : ℂ) := by
    funext a
    simp only [Function.comp_apply]
    refine tsum_congr (fun n => ?_)
    rw [← fieldMayerExpansionTermℂCoupling_tanh_eq G n a b, Complex.ofReal_tanh]
  rw [heq]; exact hcomp

/-! ## F2b: the small-`a` seed -/

/-- **F2b: small-`a` seed of the degree-window `exp` identity** (GJ §17.6.1, brick F2).
For fixed `b` in the `π/2`-ball `Metric.ball 0 r` with a uniform ball bound
`‖Complex.tanh z‖ ≤ Mr` (`Mr ≥ 1`), the brick-6 identity
`fieldPolymerZℂ G a b = Complex.exp (∑' n, fieldMayerExpansionTermℂ G n a b)` holds for all
real `a` in a neighbourhood of `0`.  Brick 6's two window hypotheses both hold as `a → 0`
(`tanh 0 = 0`, every connected polymer has positive cardinality), by continuity +
`Filter.Tendsto.eventually_lt_const`.  Mirror of `field_mayer_identity_general_eventually`
in the `a`-direction (fixed `b`), feeding the F2c continuation. -/
theorem fieldPolymerZℂ_eq_exp_eventually_a (G : SimpleGraph ι) [Fintype G.edgeSet]
    {r Mr : ℝ} {b : ℂ} (hr0 : 0 < r) (hrpi : r < Real.pi / 2) (hMr1 : 1 ≤ Mr)
    (hMr : ∀ z : ℂ, ‖z‖ ≤ r → ‖Complex.tanh z‖ ≤ Mr)
    (hbr : b ∈ Metric.ball 0 r) :
    ∀ᶠ a : ℝ in nhds 0,
      fieldPolymerZℂ G a b = Complex.exp (∑' n, fieldMayerExpansionTermℂ G n a b) := by
  classical
  -- `e·∑_P (Mr²·|tanh a|)^|P| < 1` eventually (vanishes at `a = 0`).
  have hA0 : Real.exp 1 *
      ∑ P ∈ allConnectedPolymers G, (Mr ^ 2 * |Real.tanh (0 : ℝ)|) ^ P.card = 0 := by
    rw [Real.tanh_zero, abs_zero, mul_zero]
    refine mul_eq_zero.mpr (Or.inr (Finset.sum_eq_zero (fun P hP => ?_)))
    exact zero_pow (Finset.card_ne_zero.mpr (mem_allConnectedPolymers.mp hP).nonempty)
  have hA_cont : Continuous (fun a : ℝ =>
      Real.exp 1 * ∑ P ∈ allConnectedPolymers G, (Mr ^ 2 * |Real.tanh a|) ^ P.card) :=
    continuous_const.mul (continuous_finset_sum _ (fun P _ =>
      (continuous_const.mul (continuous_abs.comp continuous_real_tanh)).pow P.card))
  have hact_ev : ∀ᶠ a : ℝ in nhds 0,
      Real.exp 1 * (∑ P ∈ allConnectedPolymers G, (Mr ^ 2 * |Real.tanh a|) ^ P.card) < 1 := by
    have h := hA_cont.tendsto 0
    rw [hA0] at h
    exact h.eventually_lt_const zero_lt_one
  -- `|ε_{a,0}| < 1` eventually (vanishes at `a = 0`).
  have hε0 : (∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
      ∏ P ∈ Γ, fieldPolymerWeight (0 : ℝ) 0 P) = 0 := by
    refine Finset.sum_eq_zero (fun Γ hΓ => ?_)
    rw [Finset.mem_erase] at hΓ
    obtain ⟨hne, hin⟩ := hΓ
    obtain ⟨P, hP⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    rw [mem_vdConnectedPolymerFamilies] at hin
    have hpos : 0 < P.card :=
      (mem_allConnectedPolymers.mp (hin.1 hP)).nonempty.card_pos
    refine Finset.prod_eq_zero hP ?_
    rw [fieldPolymerWeight, Real.tanh_zero, zero_pow hpos.ne', zero_mul]
  have hε_cont : Continuous (fun a : ℝ =>
      ∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, fieldPolymerWeight a 0 P) := by
    refine continuous_finset_sum _ (fun Γ _ => continuous_finset_prod _ (fun P _ => ?_))
    simp only [fieldPolymerWeight]
    exact (continuous_real_tanh.pow _).mul continuous_const
  have h_abs_ev : ∀ᶠ a : ℝ in nhds 0,
      |∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, fieldPolymerWeight a 0 P| < 1 := by
    have h := (continuous_abs.comp hε_cont).tendsto 0
    rw [Function.comp_apply, hε0, abs_zero] at h
    exact h.eventually_lt_const zero_lt_one
  filter_upwards [hact_ev, h_abs_ev] with a h1 h2
  exact fieldPolymerZℂ_eq_exp_tsum_fieldMayerExpansionTermℂ G hr0 hrpi hMr1 hMr h1 h2 hbr

/-! ## F2c/F2d: the degree-window capstone and non-vanishing -/

set_option backward.isDefEq.respectTransparency false in
/-- **F2c: degree-window field `exp` identity** (GJ §17.6.1, brick F2, capstone).  Fix
`b` and a target coupling `a ∈ Set.Ico 0 A`.  Under the brick-6 seed data (a `π/2`-ball
`Metric.ball 0 r ∋ b`, uniform bound `‖Complex.tanh z‖ ≤ Mr`, `Mr ≥ 1`) and the
*degree window* at radius `ρ` (`hkp`, `hρwin` with `Real.tanh A < ρ`),
`fieldPolymerZℂ G a b = Complex.exp (∑' n, fieldMayerExpansionTermℂ G n a b)`.

Analytic continuation in the real coupling `a` on the preconnected `Set.Ico 0 A`: the LHS
`a ↦ fieldPolymerZℂ G a b` is a finite sum/product of powers of `Complex.tanh (↑a)`
(Step 0, `Finset.analyticOnNhd_fun_sum/prod`, `AnalyticOnNhd.pow/mul`) hence `ℝ`-analytic;
the RHS is `Complex.exp ∘ F2a`
(`fieldMayerExpansionTermℂ_tsum_analyticOnNhd_real_a`, `AnalyticOnNhd.restrictScalars` of
`Complex.exp`); they agree near `0` (F2b `fieldPolymerZℂ_eq_exp_eventually_a`), so
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` extends the agreement to all of
`Ico 0 A`.  The window is `Δ`-based and **volume-uniform**, replacing brick 6's extensive
`hact_star`.

The `set_option backward.isDefEq.respectTransparency false` mirrors mathlib's
`AnalyticOnNhd.re_ofReal` and is required for the `AnalyticOnNhd.restrictScalars` of
`Complex.exp` (`IsScalarTower ℝ ℂ ℂ` synthesis for the normed module structures). -/
theorem fieldPolymerZℂ_eq_exp_tsum_of_degree_window (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] {a A r Mr ρ : ℝ} {b : ℂ}
    (ha : a ∈ Set.Ico 0 A) (hr0 : 0 < r) (hrpi : r < Real.pi / 2) (hMr1 : 1 ≤ Mr)
    (hMr : ∀ z : ℂ, ‖z‖ ≤ r → ‖Complex.tanh z‖ ≤ Mr) (hbr : b ∈ Metric.ball 0 r)
    (hρ0 : 0 < ρ) (htanhA : Real.tanh A < ρ)
    (hkp : (G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ)) < 1)
    (hρwin : 8 * ((G.maxDegree : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ)))
        / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ))) ^ 2 < 1) :
    fieldPolymerZℂ G a b = Complex.exp (∑' n, fieldMayerExpansionTermℂ G n a b) := by
  have hUpre : IsPreconnected (Set.Ico (0 : ℝ) A) := isPreconnected_Ico
  have h0U : (0 : ℝ) ∈ Set.Ico (0 : ℝ) A := ⟨le_refl 0, lt_of_le_of_lt ha.1 ha.2⟩
  -- LHS: finite polynomial in `Complex.tanh (↑a)`, hence `ℝ`-analytic.
  have hweight : ∀ P : Finset (Sym2 ι),
      AnalyticOnNhd ℝ (fun a : ℝ => fieldPolymerWeightℂ a b P) (Set.Ico 0 A) := by
    intro P
    have heqw : (fun a : ℝ => fieldPolymerWeightℂ a b P)
        = fun a : ℝ => Complex.tanh (a : ℂ) ^ P.card
            * Complex.tanh b ^ (oddBoundary P).card := by
      funext a; rw [fieldPolymerWeightℂ, Complex.ofReal_tanh]
    rw [heqw]
    exact ((analyticOnNhd_ctanh_ofReal.mono (Set.subset_univ _)).pow P.card).mul
      analyticOnNhd_const
  have hLHS : AnalyticOnNhd ℝ (fun a : ℝ => fieldPolymerZℂ G a b) (Set.Ico 0 A) := by
    simp only [fieldPolymerZℂ]
    exact Finset.analyticOnNhd_fun_sum _ (fun Γ _ =>
      Finset.analyticOnNhd_fun_prod _ (fun P _ => hweight P))
  -- RHS: `Complex.exp ∘ F2a`.
  have hF2a := fieldMayerExpansionTermℂ_tsum_analyticOnNhd_real_a G b hρ0 htanhA hkp hρwin
  have hexp : AnalyticOnNhd ℝ (fun z : ℂ => Complex.exp z) Set.univ :=
    (analyticOnNhd_id.cexp).restrictScalars (𝕜 := ℝ)
  have hRHS : AnalyticOnNhd ℝ
      (fun a : ℝ => Complex.exp (∑' n, fieldMayerExpansionTermℂ G n a b)) (Set.Ico 0 A) :=
    hexp.comp hF2a (Set.mapsTo_univ _ _)
  -- Agreement near `0` and continuation.
  have hseed := fieldPolymerZℂ_eq_exp_eventually_a G hr0 hrpi hMr1 hMr hbr
  exact hLHS.eqOn_of_preconnected_of_eventuallyEq hRHS hUpre h0U hseed ha

/-- **F2d: degree-window field partition non-vanishing** (GJ §17.6.1, brick F2).  Under
the hypotheses of `fieldPolymerZℂ_eq_exp_tsum_of_degree_window`, `fieldPolymerZℂ G a b ≠ 0`:
by the `exp` identity it equals `Complex.exp (…) ≠ 0` (`Complex.exp_ne_zero`).  The
`Δ`-based, **volume-uniform** replacement for brick 6's `fieldPolymerZℂ_ne_zero` (gated on
the extensive `hact_star`), consumed by the later `∂/∂h` infinite-volume bricks. -/
theorem fieldPolymerZℂ_ne_zero_of_degree_window (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] {a A r Mr ρ : ℝ} {b : ℂ}
    (ha : a ∈ Set.Ico 0 A) (hr0 : 0 < r) (hrpi : r < Real.pi / 2) (hMr1 : 1 ≤ Mr)
    (hMr : ∀ z : ℂ, ‖z‖ ≤ r → ‖Complex.tanh z‖ ≤ Mr) (hbr : b ∈ Metric.ball 0 r)
    (hρ0 : 0 < ρ) (htanhA : Real.tanh A < ρ)
    (hkp : (G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ)) < 1)
    (hρwin : 8 * ((G.maxDegree : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ)))
        / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ))) ^ 2 < 1) :
    fieldPolymerZℂ G a b ≠ 0 := by
  rw [fieldPolymerZℂ_eq_exp_tsum_of_degree_window G ha hr0 hrpi hMr1 hMr hbr hρ0 htanhA hkp
    hρwin]
  exact Complex.exp_ne_zero _

end IsingModel
