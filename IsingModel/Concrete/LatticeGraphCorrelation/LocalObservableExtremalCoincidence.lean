import IsingModel.Concrete.LatticeGraphCorrelation.CubicBoxExtremalCoincidence
import IsingModel.Dobrushin.ComparisonTheorem

/-!
# Extremal-state coincidence for a general local observable (GJ §17.1, Issue #4264)

PRs #4260/#4262/#4263 completed the ℤ^d Dobrushin-uniqueness programme for the single-spin
**origin** observable.  This file lifts the coincidence of the extremal `±` states — and the
screened infinite-volume limit — to a **general** `LocalObservable d` (on a finite support
`S ⊆ ℤ^d`), faithful to GJ §17.1 Dobrushin uniqueness for arbitrary local observables.

## Headline

`plusStateExpectation_eq_minusStateExpectation` — at high temperature the cubic-exhaustion `+`-state
and `−`-state functionals of **any** `O : LocalObservable d` coincide,
`μ⁺(O) = μ⁻(O)`.  No monotonicity of `O` is required.

`tendsto_gibbsExpectationBC_localObs_extremal_limit` — for a **monotone** `O`, every boundary
condition's screened-box expectation of `O` converges along the cubic exhaustion to the common
extremal value.

## Method

The single-site machinery is replaced by a **support-sum** of site oscillations.  The general
multi-site Dobrushin comparison `gibbsExpectationBC_dist_le_resolvent_sum`
(`Dobrushin/ComparisonTheorem.lean`) bounds the boundary difference by
`∑_x ∑_{y∈S'} R_{xy}·siteOsc_x f`; the lifted observable has `siteOsc_x = 0` off its support
(`siteOsc_lift_eq_zero_of_not_mem`) and
`siteOsc_x ≤ siteOsc_{x.val} O.φ` on it (`siteOsc_lift_le`), so the total is bounded by the
**box-independent** constant `∑_{j∈O.S} siteOsc_j O.φ` (`sum_siteOsc_lift_le`).  The mixed-config
bridge of `CubicBoxExtremalCoincidence` (already general) plus the far-field resolvent tail give
the per-stage bound `(∑_{j∈O.S} siteOsc_j O.φ)·resolventTail d (2d·tanh βJ) (k+1) → 0`; squeeze
gives the coincidence, and the extremal sandwich gives the limit.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306;
Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.4, §6.5; Georgii, *Gibbs
Measures and Phase Transitions*, Ch. 8.
-/

namespace IsingModel

namespace Ambient

open IsingModel.Dobrushin Finset Filter Topology

/-- **Restriction commutes with a support update**: for a box site `x` whose value lies in the
support `O.S`, updating the box configuration at `x` and restricting equals restricting and updating
at the corresponding support site `⟨x.val, hx⟩`. -/
theorem restrictConfig_update_of_mem (d : ℕ) {Λ : Finset (Fin d → ℤ)}
    {S : Finset (Fin d → ℤ)} (hS : S ⊆ Λ) (σ : Config (↑Λ : Type _))
    {x : ↑Λ} (hx : x.val ∈ S) (v : Spin) :
    restrictConfig hS (Function.update σ x v)
      = Function.update (restrictConfig hS σ) ⟨x.val, hx⟩ v := by
  funext j
  rcases eq_or_ne j (⟨x.val, hx⟩ : ↑S) with hj | hj
  · subst hj
    change (Function.update σ x v) (subtypeIncl hS (⟨x.val, hx⟩ : ↑S))
        = Function.update (restrictConfig hS σ) (⟨x.val, hx⟩ : ↑S) v (⟨x.val, hx⟩ : ↑S)
    rw [show subtypeIncl hS (⟨x.val, hx⟩ : ↑S) = x from Subtype.ext rfl,
      Function.update_self, Function.update_self]
  · have hne : subtypeIncl hS j ≠ x := by
      intro hcontra
      apply hj
      apply Subtype.ext
      have hval : (subtypeIncl hS j).val = x.val := congrArg Subtype.val hcontra
      exact hval
    simp only [restrictConfig, Function.comp_apply, Function.update_of_ne hj,
      Function.update_of_ne hne]

/-- **Restriction is unaffected by an off-support update**: updating the box configuration at a site
`x` whose value is **not** in the support leaves the restriction to the support unchanged. -/
theorem restrictConfig_update_of_not_mem (d : ℕ) {Λ : Finset (Fin d → ℤ)}
    {S : Finset (Fin d → ℤ)} (hS : S ⊆ Λ) (σ : Config (↑Λ : Type _))
    {x : ↑Λ} (hx : x.val ∉ S) (v : Spin) :
    restrictConfig hS (Function.update σ x v) = restrictConfig hS σ := by
  funext j
  have hne : subtypeIncl hS j ≠ x := by
    intro hcontra
    exact hx (hcontra ▸ j.property)
  simp only [restrictConfig, Function.comp_apply, Function.update_of_ne hne]

/-- **Off-support oscillation of the lifted observable vanishes**: for a box site `x` whose value is
not in the support `O.S`, the lifted observable `fun σ => O.φ (restrictConfig hS σ)` does not depend
on the spin at `x`, so its single-site oscillation there is `0`. -/
theorem siteOsc_lift_eq_zero_of_not_mem (d : ℕ) {Λ : Finset (Fin d → ℤ)} (O : LocalObservable d)
    (hS : O.S ⊆ Λ) {x : ↑Λ} (hx : x.val ∉ O.S) :
    siteOsc x (fun σ => O.φ (restrictConfig hS σ)) = 0 := by
  refine le_antisymm (siteOsc_le_of_forall fun σ => ?_) (siteOsc_nonneg _ _)
  rw [restrictConfig_update_of_not_mem d hS σ hx, restrictConfig_update_of_not_mem d hS σ hx,
    sub_self, abs_zero]

/-- **On-support oscillation of the lifted observable is dominated**: for a box site `x` whose value
lies in the support, the lifted observable's single-site oscillation at `x` is at most the intrinsic
oscillation of `O.φ` at the corresponding support site `⟨x.val, hx⟩`. -/
theorem siteOsc_lift_le (d : ℕ) {Λ : Finset (Fin d → ℤ)} (O : LocalObservable d)
    (hS : O.S ⊆ Λ) {x : ↑Λ} (hx : x.val ∈ O.S) :
    siteOsc x (fun σ => O.φ (restrictConfig hS σ)) ≤ siteOsc (⟨x.val, hx⟩ : ↑O.S) O.φ := by
  refine siteOsc_le_of_forall fun σ => ?_
  rw [restrictConfig_update_of_mem d hS σ hx, restrictConfig_update_of_mem d hS σ hx]
  exact abs_sub_update_le_siteOsc (⟨x.val, hx⟩ : ↑O.S) O.φ (restrictConfig hS σ)

/-- **The total lifted oscillation is the box-independent support sum**: the sum over all
box sites of the lifted observable's single-site oscillation is at most `∑_{j∈O.S} siteOsc_j O.φ`,
a constant independent of the ambient box `Λ`.  Off-support sites contribute `0`
(`siteOsc_lift_eq_zero_of_not_mem`); on-support sites are dominated (`siteOsc_lift_le`) and
reindexed to the support. -/
theorem sum_siteOsc_lift_le (d : ℕ) {Λ : Finset (Fin d → ℤ)} (O : LocalObservable d)
    (hS : O.S ⊆ Λ) :
    ∑ x : ↑Λ, siteOsc x (fun σ => O.φ (restrictConfig hS σ))
      ≤ ∑ j : ↑O.S, siteOsc j O.φ := by
  classical
  -- The support inclusion `↑O.S → ↑Λ`, injective.
  have hι : Function.Injective (fun j : ↑O.S => (⟨j.val, hS j.property⟩ : ↑Λ)) := by
    intro a b hab
    apply Subtype.ext
    have hval : (⟨a.val, hS a.property⟩ : ↑Λ).val = (⟨b.val, hS b.property⟩ : ↑Λ).val :=
      congrArg Subtype.val hab
    exact hval
  -- Off the image (support sites), the lifted oscillation vanishes, so the full-box sum equals the
  -- sum over the support image.
  have hsubset : ∑ x : ↑Λ, siteOsc x (fun σ => O.φ (restrictConfig hS σ))
      = ∑ x ∈ (Finset.univ : Finset ↑O.S).image (fun j : ↑O.S => (⟨j.val, hS j.property⟩ : ↑Λ)),
          siteOsc x (fun σ => O.φ (restrictConfig hS σ)) := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro x _ hximg
    refine siteOsc_lift_eq_zero_of_not_mem d O hS (fun hmem => hximg ?_)
    exact Finset.mem_image.mpr ⟨⟨x.val, hmem⟩, Finset.mem_univ _, Subtype.ext rfl⟩
  rw [hsubset, Finset.sum_image hι.injOn]
  exact Finset.sum_le_sum
    (fun j _ => siteOsc_lift_le d O hS (x := (⟨j.val, hS j.property⟩ : ↑Λ)) j.property)

/-- **Card-free multi-site boundary-influence bound** (GJ §17.1): for a general local observable `O`
on the induced cubic-lattice graph, if `η, η'` agree off a finite set `S` every site of which lies
at ℓ¹-lattice distance at least `R` from **every** support site of `O`, then the boundary-condition
difference of the lifted observable is bounded by `(∑_{j∈O.S} siteOsc_j O.φ)·resolventTail d
(2d·tanh βJ) R` — the box-independent support-oscillation sum times the far-field resolvent tail.
Generalises `gibbsExpectationBC_originObs_inducedLattice_dist_le_resolventTail` (#4258, single-site)
via `gibbsExpectationBC_dist_le_resolvent_sum` (the multi-site Dobrushin comparison) summed over the
support. -/
theorem gibbsExpectationBC_localObs_inducedLattice_dist_le_resolventTail (d : ℕ) (hd : 1 ≤ d)
    {Λ : Finset (Fin d → ℤ)} {β J : ℝ} (hβJ : 0 ≤ β * J) (hα : β * J * (2 * (d : ℝ)) < 1) (h : ℝ)
    (Λ' S : Finset ↑Λ) {η η' : Config ↑Λ} (hagree : agreesOff S η η')
    (O : LocalObservable d) (hS : O.S ⊆ Λ) (R : ℕ)
    (hfar : ∀ x : ↑Λ, x.val ∈ O.S → ∀ y ∈ S, R ≤ latticeDistance d x.val y.val) :
    |gibbsExpectationBC (Ambient.inducedGraph (latticeGraph d) Λ) β (fun _ => J) h Λ' η
          (fun σ => O.φ (restrictConfig hS σ))
        - gibbsExpectationBC (Ambient.inducedGraph (latticeGraph d) Λ) β (fun _ => J) h Λ' η'
          (fun σ => O.φ (restrictConfig hS σ))|
      ≤ (∑ j : ↑O.S, siteOsc j O.φ) * resolventTail d ((2 * (d : ℝ)) * Real.tanh (β * J)) R := by
  have hα0 : 0 ≤ (2 * (d : ℝ)) * Real.tanh (β * J) :=
    mul_nonneg (by positivity) (tanh_nonneg_of_nonneg hβJ)
  have hα1 : (2 * (d : ℝ)) * Real.tanh (β * J) < 1 := by
    have htanh := tanh_le_self hβJ
    have hnonneg : 0 ≤ 2 * (d : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left htanh hnonneg]
  have htail_nonneg : 0 ≤ resolventTail d ((2 * (d : ℝ)) * Real.tanh (β * J)) R :=
    tsum_nonneg (fun k => resolventTailSummand_nonneg hα0 hα1 (k + R))
  have hΔ : β * J * (Ambient.inducedGraph (latticeGraph d) Λ).maxDegree < 1 := by
    have hdeg : ((Ambient.inducedGraph (latticeGraph d) Λ).maxDegree : ℝ) ≤ 2 * (d : ℝ) := by
      exact_mod_cast induced_latticeGraph_maxDegree_le d Λ
    calc β * J * ((Ambient.inducedGraph (latticeGraph d) Λ).maxDegree : ℝ)
        ≤ β * J * (2 * (d : ℝ)) := mul_le_mul_of_nonneg_left hdeg hβJ
      _ < 1 := hα
  refine (gibbsExpectationBC_dist_le_resolvent_sum (Ambient.inducedGraph (latticeGraph d) Λ)
    hβJ hΔ h Λ' S hagree (fun σ => O.φ (restrictConfig hS σ))).trans ?_
  have hstep : ∑ x : ↑Λ, ∑ y ∈ S,
        dobrushinResolvent (Ambient.inducedGraph (latticeGraph d) Λ) β J x y
          * siteOsc x (fun σ => O.φ (restrictConfig hS σ))
      ≤ ∑ x : ↑Λ, siteOsc x (fun σ => O.φ (restrictConfig hS σ))
          * resolventTail d ((2 * (d : ℝ)) * Real.tanh (β * J)) R := by
    refine Finset.sum_le_sum fun x _ => ?_
    rw [← Finset.sum_mul, mul_comm]
    by_cases hx : x.val ∈ O.S
    · exact mul_le_mul_of_nonneg_left
        (dobrushinResolvent_farSum_le_resolventTail d hd hβJ hα x S R (hfar x hx))
        (siteOsc_nonneg _ _)
    · rw [siteOsc_lift_eq_zero_of_not_mem d O hS hx, zero_mul, zero_mul]
  refine hstep.trans ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (sum_siteOsc_lift_le d O hS) htail_nonneg

/-- **Per-stage extremal closeness for a general local observable** (GJ §17.1): for inner box `N+k`
and ambient box `N+k+1`, with `O.S ⊆ cubicBox d N`, the `+` box expectation and the flipped-`+`
(= `−`-boundary) box expectation of `O` differ by at most `(∑_{j∈O.S} siteOsc_j O.φ)·resolventTail d
(2d·tanh βJ) (k+1)`.  The mixed-config `μ` bridges `plusConfig`/`minusConfig`; the disagreement set
is the shell, every site at ℓ¹-distance `≥ k+1` from every support site
(`latticeDistance_ge_of_mem_cubicBox_succ_not_mem`, reference an arbitrary support point). -/
theorem abs_plusBoxObs_sub_flipObs_le (d : ℕ) (hd : 1 ≤ d) {β J : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (hα : β * J * (2 * (d : ℝ)) < 1) (h : ℝ) (O : LocalObservable d)
    (N k : ℕ) (hSk : O.S ⊆ cubicBox d (N + k + 1)) (hSN : O.S ⊆ cubicBox d N) :
    |plusBoxObsExpectation (N + k) (N + k + 1) J h β O hSk
        - plusBoxObsExpectation (N + k) (N + k + 1) J (-h) β O.flipObs hSk|
      ≤ (∑ j : ↑O.S, siteOsc j O.φ)
        * resolventTail d ((2 * (d : ℝ)) * Real.tanh (β * J)) (k + 1) := by
  have hβJ : 0 ≤ β * J := mul_nonneg hβ hJ
  set μ : Config (↑(cubicBox d (N + k + 1)) : Type _) :=
    fun x => if (x : Fin d → ℤ) ∈ cubicBox d (N + k) then Spin.down else Spin.up with hμ
  rw [show plusBoxObsExpectation (N + k) (N + k + 1) J h β O hSk
        = gibbsExpectationBC (inducedGraph (latticeGraph d) (cubicBox d (N + k + 1))) β
            (fun _ => J) h (plusBoxInterior d (N + k) (N + k + 1)) (plusConfig _)
            (fun σ => O.φ (restrictConfig hSk σ)) from rfl,
    plusBoxObsExpectation_flipObs_eq_minusBC d (N + k) (N + k + 1) O hSk]
  have hcong_plus : agreesOff (plusBoxInterior d (N + k) (N + k + 1)) (plusConfig _) μ := by
    intro i hi
    simp only [plusBoxInterior, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [hμ, plusConfig, if_neg hi]
  rw [gibbsExpectationBC_boundary_congr (inducedGraph (latticeGraph d) (cubicBox d (N + k + 1)))
    β (fun _ => J) h (plusBoxInterior d (N + k) (N + k + 1)) hcong_plus
    (fun σ => O.φ (restrictConfig hSk σ))]
  set S : Finset (↑(cubicBox d (N + k + 1)) : Type _) :=
    Finset.univ.filter (fun x => (x : Fin d → ℤ) ∉ cubicBox d (N + k)) with hSdef
  have hagree : agreesOff S μ (minusConfig _) := by
    intro i hi
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
    simp only [hμ, minusConfig, if_pos hi]
  have hfar : ∀ x : ↑(cubicBox d (N + k + 1)), x.val ∈ O.S →
      ∀ y ∈ S, k + 1 ≤ latticeDistance d x.val y.val := by
    intro x hx y hy
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have hge := latticeDistance_ge_of_mem_cubicBox_succ_not_mem
      (hSN hx) (Nat.le_add_right N k) y.property hy
    omega
  exact gibbsExpectationBC_localObs_inducedLattice_dist_le_resolventTail d hd hβJ hα h
    (plusBoxInterior d (N + k) (N + k + 1)) S hagree O hSk (k + 1) hfar

/-- **Coincidence of the extremal `±` states for a general local observable** (GJ §17.1; Dobrushin
uniqueness).  At high temperature the cubic-exhaustion `+`-state and `−`-state functionals of
**any** `O : LocalObservable d` coincide, `μ⁺(O) = μ⁻(O)`; no monotonicity of `O` is needed.
Proof: squeeze the per-stage difference of the two extremal screened box expectations
(`abs_plusBoxObs_sub_flipObs_le`) to `0` via the box-independent coefficient `∑_{j∈O.S} siteOsc_j
O.φ` and the vanishing far-field tail. -/
theorem plusStateExpectation_eq_minusStateExpectation (d : ℕ) (hd : 1 ≤ d) {β J : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (hα : β * J * (2 * (d : ℝ)) < 1) (h : ℝ) (O : LocalObservable d)
    {N : ℕ} (hS : O.S ⊆ cubicBox d N) :
    plusStateExpectation J h β O hS = minusStateExpectation J h β O hS := by
  have hβJ : 0 ≤ β * J := mul_nonneg hβ hJ
  have hα0 : 0 ≤ (2 * (d : ℝ)) * Real.tanh (β * J) :=
    mul_nonneg (by positivity) (tanh_nonneg_of_nonneg hβJ)
  have hα1 : (2 * (d : ℝ)) * Real.tanh (β * J) < 1 := by
    have htanh := tanh_le_self hβJ
    have hnonneg : 0 ≤ 2 * (d : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left htanh hnonneg]
  have hp := tendsto_plusStateExpectation (h := h) hβ hJ O hS
  have hm := tendsto_minusStateExpectation (h := h) hβ hJ O hS
  have hdiff := hp.sub hm
  have hshift : Tendsto (fun k : ℕ => k + 1) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_succ k) tendsto_id
  have hc : Tendsto (fun k : ℕ => (∑ j : ↑O.S, siteOsc j O.φ)
      * resolventTail d ((2 * (d : ℝ)) * Real.tanh (β * J)) (k + 1)) atTop (𝓝 0) := by
    have := ((tendsto_resolventTail_atTop d hα0 hα1).comp hshift).const_mul
      (∑ j : ↑O.S, siteOsc j O.φ)
    simpa using this
  have hzero : Tendsto (fun k : ℕ =>
      plusBoxObsExpectation (N + k) (N + k + 1) J h β O
          (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1)))
        - plusBoxObsExpectation (N + k) (N + k + 1) J (-h) β O.flipObs
          (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1)))) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun k => ?_) hc
    rw [Real.norm_eq_abs]
    exact abs_plusBoxObs_sub_flipObs_le d hd hβ hJ hα h O N k
      (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1))) hS
  have hlim := tendsto_nhds_unique hdiff hzero
  linarith [hlim]

/-- **Infinite-volume boundary-condition-free limit for a general monotone local observable**
(GJ §17.1; ℤ^d Dobrushin uniqueness).  For a **monotone** `O` and high temperature, every
boundary-condition family `η` gives a screened-box expectation of `O` converging along the cubic
exhaustion to the common extremal value `plusStateExpectation J h β O hS`.  The extremal sandwich
traps each term between the `±` box expectations, both `→` the common value by the coincidence. -/
theorem tendsto_gibbsExpectationBC_localObs_extremal_limit (d : ℕ) (hd : 1 ≤ d) {β J : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (hα : β * J * (2 * (d : ℝ)) < 1) (h : ℝ) (O : LocalObservable d)
    (hO_mono : Monotone O.φ) {N : ℕ} (hS : O.S ⊆ cubicBox d N)
    (η : ∀ k : ℕ, Config (↑(cubicBox d (N + k + 1)) : Type _)) :
    Tendsto (fun k : ℕ =>
        gibbsExpectationBC (inducedGraph (latticeGraph d) (cubicBox d (N + k + 1))) β (fun _ => J) h
          (plusBoxInterior d (N + k) (N + k + 1)) (η k)
          (fun σ => O.φ (restrictConfig (hS.trans
            (cubicBox_mono d (by omega : N ≤ N + k + 1))) σ)))
      atTop (𝓝 (plusStateExpectation J h β O hS)) := by
  have hupper : Tendsto (fun k : ℕ =>
      gibbsExpectationBC (inducedGraph (latticeGraph d) (cubicBox d (N + k + 1))) β (fun _ => J) h
        (plusBoxInterior d (N + k) (N + k + 1)) (plusConfig _)
        (fun σ => O.φ (restrictConfig (hS.trans
          (cubicBox_mono d (by omega : N ≤ N + k + 1))) σ))) atTop
      (𝓝 (plusStateExpectation J h β O hS)) :=
    tendsto_plusStateExpectation (h := h) hβ hJ O hS
  have hlower : Tendsto (fun k : ℕ =>
      gibbsExpectationBC (inducedGraph (latticeGraph d) (cubicBox d (N + k + 1))) β (fun _ => J) h
        (plusBoxInterior d (N + k) (N + k + 1)) (minusConfig _)
        (fun σ => O.φ (restrictConfig (hS.trans
          (cubicBox_mono d (by omega : N ≤ N + k + 1))) σ))) atTop
      (𝓝 (plusStateExpectation J h β O hS)) := by
    have hm := tendsto_minusStateExpectation (h := h) hβ hJ O hS
    rw [← plusStateExpectation_eq_minusStateExpectation d hd hβ hJ hα h O hS] at hm
    refine hm.congr (fun k => ?_)
    exact plusBoxObsExpectation_flipObs_eq_minusBC d (N + k) (N + k + 1) O
      (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper (fun k => ?_) (fun k => ?_)
  · exact (gibbsExpectationBC_extremal_sandwich _ hβ (fun _ => hJ) _ (η k) _
      (hO_mono.comp (restrictConfig_monotone _))).1
  · exact (gibbsExpectationBC_extremal_sandwich _ hβ (fun _ => hJ) _ (η k) _
      (hO_mono.comp (restrictConfig_monotone _))).2

end Ambient

end IsingModel
