import IsingModel.Concrete.LatticeGraphCorrelation.MinusStateExtremal
import IsingModel.Dobrushin.InfiniteVolumeUniqueness

/-!
# Coincidence of the extremal ± states and infinite-volume limit existence (GJ §17.1, Issue #4261)

The volume-uniform boundary-condition independence of PR #4260
(`Dobrushin/InfiniteVolumeUniqueness.lean`) proved that a single influence radius `R(ε)` bounds the
boundary-condition difference of the origin observable uniformly across the cubic exhaustion, but
left open the **existence** of the boundary-condition-free infinite-volume limit.  This file closes
that gap (in the screened `±`-state convention) via the extremal-state squeeze.

## Headline

`plusStateExpectation_eq_minusStateExpectation_originObs` — at high temperature the cubic-exhaustion
`+`-state and `−`-state functionals of the origin single-spin observable **coincide**,
`μ⁺(originObs g) = μ⁻(originObs g)`.  This is the decay-of-influence ⇒ uniqueness content of §17.1:
the two extremal infinite-volume Gibbs states agree on the local observable.  No monotonicity of `g`
is needed.

## Limit existence

`tendsto_gibbsExpectationBC_originObs_extremal_limit` — for a **monotone** `g`, every boundary
condition's screened-box expectation of the origin observable converges, along the cubic exhaustion,
to the common extremal value `μ⁺(originObs g) = μ⁻(originObs g)`.  This is the genuine
boundary-condition-free infinite-volume **limit existence** for the local observable.

## Method

The `±`-state machinery (`Concrete/.../{LocalObservableState,MinusStateExtremal}.lean`) uses the
screened box expectation `plusBoxExpectation d n m = gibbsExpectationBC … (plusBoxInterior d n m)
(plusConfig) …` (free region the inner box, frozen `±` boundary on the shell).  The `−` side equals
the flipped-`+` (`plusBoxObsExpectation_flipObs_eq_minusBC`).  The two extremal box expectations are
then same-graph, same-free-region Gibbs expectations of the same observable differing only in the
boundary configuration; the **mixed configuration** `μ` (`down` on the inner box, `up` on the shell)
bridges `plusConfig` and `minusConfig`: it agrees with `plusConfig` off the inner box (so the two
expectations coincide by the new boundary-congruence lemma `gibbsExpectationBC_boundary_congr`) and
agrees with `minusConfig` on the inner box, with disagreement exactly the shell — which recedes to
ℓ¹-distance `≥ n+1` from the origin, so the PR #4260 per-stage bound forces the difference `≤
|g↑−g↓|·resolventTail d (2d·tanh βJ) n → 0`.  The squeeze then gives the coincidence; the extremal
sandwich (`gibbsExpectationBC_extremal_sandwich`) traps every boundary condition between the two
coinciding limits.

## Honest scope

This is the **screened** convention (inner box strictly inside the ambient box, where the boundary
genuinely acts), which is the natural object of the existing `±`-state machinery and of GJ §17.1.
The literal full-box free-boundary (`Λ' = Finset.univ`) limit is a separate free-region
reconciliation and is **not** delivered here (the extremal sandwich is vacuous at `Λ = univ`).

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306;
Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.4 (Lemma 3.23, `μ⁻ ≤ μ⁺`),
§6.5 (Dobrushin uniqueness); Georgii, *Gibbs Measures and Phase Transitions*, Ch. 8.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Boundary-condition congruence of the Boltzmann weight**: if `η, η'` agree off the Gibbs region
`Λ`, the boundary-condition Boltzmann weights coincide pointwise (the weight constrains a
configuration only off `Λ`, through `agreesOff Λ η ·`). -/
theorem boltzmannWeightBC_boundary_congr (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) (Λ : Finset ι) {η η' : Config ι}
    (hcong : agreesOff Λ η η') (σ : Config ι) :
    boltzmannWeightBC G β J h Λ η σ = boltzmannWeightBC G β J h Λ η' σ := by
  unfold boltzmannWeightBC
  by_cases hσ : agreesOff Λ η σ
  · have hσ' : agreesOff Λ η' σ := fun i hi => (hσ i hi).trans (hcong i hi).symm
    rw [Set.indicator_of_mem hσ, Set.indicator_of_mem hσ']
  · have hσ' : ¬ agreesOff Λ η' σ := fun hh => hσ (fun i hi => (hh i hi).trans (hcong i hi))
    rw [Set.indicator_of_notMem hσ, Set.indicator_of_notMem hσ']

/-- **Boundary-condition congruence of the Gibbs expectation**: the boundary-condition Gibbs
expectation depends on the boundary condition only through its values **off** the Gibbs region `Λ`.
If `η, η'` agree off `Λ`, then `⟨F⟩^η_Λ = ⟨F⟩^{η'}_Λ` for every observable `F`.  (General, reusable;
the geometric core of the extremal-state bridge.) -/
theorem gibbsExpectationBC_boundary_congr (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) (Λ : Finset ι) {η η' : Config ι}
    (hcong : agreesOff Λ η η') (F : Config ι → ℝ) :
    gibbsExpectationBC G β J h Λ η F = gibbsExpectationBC G β J h Λ η' F := by
  have hbw : ∀ σ, boltzmannWeightBC G β J h Λ η σ = boltzmannWeightBC G β J h Λ η' σ :=
    fun σ => boltzmannWeightBC_boundary_congr G β J h Λ hcong σ
  unfold gibbsExpectationBC partitionFunctionBC
  simp_rw [hbw]

namespace Ambient

open IsingModel.Dobrushin Filter Topology

/-- **The origin single-spin observable as a support-`{0}` local observable**: for `g : Spin → ℝ`,
the `LocalObservable d` with support `{0}` reading the origin spin and applying `g`.  This is the
`LocalObservable`-typed avatar of `Dobrushin.originObs`, letting the cubic-exhaustion `±`-state
machinery (`plusStateExpectation` / `tendsto_plusStateExpectation`) act on the origin observable. -/
def originLocalObs (d : ℕ) (g : Spin → ℝ) : LocalObservable d :=
  ⟨{0}, fun τ => g (τ ⟨0, Finset.mem_singleton_self 0⟩)⟩

/-- The support of `originLocalObs d g` is `{0}`. -/
@[simp] theorem originLocalObs_S (d : ℕ) (g : Spin → ℝ) : (originLocalObs d g).S = {0} := rfl

/-- **The lifted origin local observable is `Dobrushin.originObs`**: pulling `originLocalObs d g`
back to a box configuration via `restrictConfig` reproduces the origin observable `originObs d g`.
Both read the origin spin; the subtype membership proofs agree by proof irrelevance. -/
theorem originLocalObs_lift_eq (d : ℕ) (g : Spin → ℝ) {m : ℕ}
    (hSm : (originLocalObs d g).S ⊆ cubicBox d m) :
    (fun σ : Config (↑(cubicBox d m) : Type _) => (originLocalObs d g).φ (restrictConfig hSm σ))
      = originObs d g (origin_mem_cubicBox d m) := by
  funext σ
  rfl

/-- **The flipped-`+` box expectation is the minus-boundary expectation**: extracting the inline
identity used in `plusBoxObsExpectation_flipObs_neg_h_le`, the `+` box expectation of the flipped
observable at field `−h` equals the genuine `−`-boundary (`minusConfig`) Gibbs expectation of the
observable at field `h`, on the same induced graph, free region, and lifted observable.  This is the
global spin-flip symmetry `gibbsExpectationBC_minus_eq_plus_neg_h_flip` packaged for the screened
cubic-box convention. -/
theorem plusBoxObsExpectation_flipObs_eq_minusBC (d : ℕ) (n m : ℕ) {J h β : ℝ}
    (O : LocalObservable d) (hS : O.S ⊆ cubicBox d m) :
    plusBoxObsExpectation n m J (-h) β O.flipObs hS
      = gibbsExpectationBC (inducedGraph (latticeGraph d) (cubicBox d m)) β (fun _ => J) h
          (plusBoxInterior d n m) (minusConfig _) (fun σ => O.φ (restrictConfig hS σ)) := by
  unfold plusBoxObsExpectation plusBoxExpectation
  have hbridge := gibbsExpectationBC_minus_eq_plus_neg_h_flip
    (inducedGraph (latticeGraph d) (cubicBox d m)) β (fun _ => J) h (plusBoxInterior d n m)
    (fun τ => O.φ (restrictConfig hS τ))
  rw [show (fun σ : Config (↑(cubicBox d m) : Type _) => O.flipObs.φ (restrictConfig hS σ))
        = (fun σ => O.φ (restrictConfig hS (Config.flip σ))) from rfl, ← hbridge]

/-- **`+` box expectation of the origin observable as a Gibbs expectation**: the screened `+` box
expectation of `originLocalObs d g` is the `plusConfig`-boundary Gibbs expectation of
`originObs d g` on the induced cubic-lattice graph with free region `plusBoxInterior d n m`. -/
theorem plusBoxObsExpectation_originObs_eq (d : ℕ) (n m : ℕ) {J h β : ℝ} (g : Spin → ℝ)
    (hSm : (originLocalObs d g).S ⊆ cubicBox d m) :
    plusBoxObsExpectation n m J h β (originLocalObs d g) hSm
      = gibbsExpectationBC (inducedGraph (latticeGraph d) (cubicBox d m)) β (fun _ => J) h
          (plusBoxInterior d n m) (plusConfig _) (originObs d g (origin_mem_cubicBox d m)) := by
  unfold plusBoxObsExpectation plusBoxExpectation
  rw [originLocalObs_lift_eq d g hSm]

/-- **Flipped-`+` box expectation of the origin observable as a Gibbs expectation**: the screened
`+` box expectation of the flipped origin observable at field `−h` is the `minusConfig`-boundary
Gibbs expectation of `originObs d g` at field `h`. -/
theorem plusBoxObsExpectation_flipObs_originObs_eq (d : ℕ) (n m : ℕ) {J h β : ℝ} (g : Spin → ℝ)
    (hSm : (originLocalObs d g).S ⊆ cubicBox d m) :
    plusBoxObsExpectation n m J (-h) β (originLocalObs d g).flipObs hSm
      = gibbsExpectationBC (inducedGraph (latticeGraph d) (cubicBox d m)) β (fun _ => J) h
          (plusBoxInterior d n m) (minusConfig _) (originObs d g (origin_mem_cubicBox d m)) := by
  rw [plusBoxObsExpectation_flipObs_eq_minusBC d n m (originLocalObs d g) hSm,
    originLocalObs_lift_eq d g hSm]

/-- **Per-stage extremal closeness for the origin observable** (GJ §17.1).

For inner box `n` and ambient box `n+1`, the `+` box expectation and the flipped-`+`
(= `−`-boundary) box expectation of the origin observable differ by at most
`|g↑−g↓|·resolventTail d (2d·tanh βJ) n`.
The two are same-graph, same-free-region (`plusBoxInterior d n (n+1)`) Gibbs expectations of
`originObs d g` differing only in boundary configuration (`plusConfig` vs `minusConfig`); the mixed
configuration `μ` (`down` on the inner box, `up` on the shell) agrees with `plusConfig` off
the inner box (boundary congruence) and with `minusConfig` on the inner box, so the disagreement
set is the shell, every site at ℓ¹-distance `≥ n+1` from the origin — whence the PR #4260 per-stage
card-free bound applies. -/
theorem abs_plusBoxObs_sub_flipObs_originObs_le (d : ℕ) (hd : 1 ≤ d) {β J : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (hα : β * J * (2 * (d : ℝ)) < 1) (h : ℝ) (g : Spin → ℝ) (n : ℕ)
    (hSm : (originLocalObs d g).S ⊆ cubicBox d (n + 1)) :
    |plusBoxObsExpectation n (n + 1) J h β (originLocalObs d g) hSm
        - plusBoxObsExpectation n (n + 1) J (-h) β (originLocalObs d g).flipObs hSm|
      ≤ |g Spin.up - g Spin.down| * resolventTail d ((2 * (d : ℝ)) * Real.tanh (β * J)) n := by
  have hβJ : 0 ≤ β * J := mul_nonneg hβ hJ
  -- The mixed boundary configuration: `down` inside the inner box, `up` on the shell.
  set μ : Config (↑(cubicBox d (n + 1)) : Type _) :=
    fun x => if (x : Fin d → ℤ) ∈ cubicBox d n then Spin.down else Spin.up with hμ
  rw [plusBoxObsExpectation_originObs_eq d n (n + 1) g hSm,
    plusBoxObsExpectation_flipObs_originObs_eq d n (n + 1) g hSm]
  -- `plusConfig` and `μ` agree off the inner box (on the shell `μ = up = plusConfig`).
  have hcong_plus : agreesOff (plusBoxInterior d n (n + 1)) (plusConfig _) μ := by
    intro i hi
    simp only [plusBoxInterior, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [hμ, plusConfig, if_neg hi]
  rw [gibbsExpectationBC_boundary_congr (inducedGraph (latticeGraph d) (cubicBox d (n + 1)))
    β (fun _ => J) h (plusBoxInterior d n (n + 1)) hcong_plus
    (originObs d g (origin_mem_cubicBox d (n + 1)))]
  -- The disagreement set: the shell (sites outside the inner box), at ℓ¹-distance `≥ n+1`.
  set S : Finset (↑(cubicBox d (n + 1)) : Type _) :=
    Finset.univ.filter (fun x => (x : Fin d → ℤ) ∉ cubicBox d n) with hSdef
  have hagree : agreesOff S μ (minusConfig _) := by
    intro i hi
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
    simp only [hμ, minusConfig, if_pos hi]
  have hfar : ∀ y ∈ S, n ≤ latticeDistance d (0 : Fin d → ℤ) y.val := by
    intro y hy
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have hge := latticeDistance_ge_of_mem_cubicBox_succ_not_mem
      (origin_mem_cubicBox d 0) (Nat.zero_le n) y.property hy
    omega
  exact gibbsExpectationBC_originObs_inducedLattice_dist_le_resolventTail
    d hd hβJ hα h g (n + 1) (plusBoxInterior d n (n + 1)) S hagree n hfar

/-- **Coincidence of the extremal `±` states for the origin observable** (GJ §17.1; Dobrushin
uniqueness via decay of influence).

At high temperature (`0 ≤ β`, `0 ≤ J`, `βJ·2d < 1`, `d ≥ 1`) the cubic-exhaustion `+`-state and
`−`-state functionals of the origin single-spin observable `originObs d g` coincide:
`μ⁺(originObs g) = μ⁻(originObs g)`.  This is the boundary-condition independence of the
infinite-volume Gibbs expectation of the local observable — the decay-of-influence ⇒ uniqueness
content of the Dobrushin theorem — obtained by squeezing the per-stage difference of the two
extremal screened box expectations (`abs_plusBoxObs_sub_flipObs_originObs_le`) to `0`.  No
monotonicity of `g` is required. -/
theorem plusStateExpectation_eq_minusStateExpectation_originObs (d : ℕ) (hd : 1 ≤ d) {β J : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (hα : β * J * (2 * (d : ℝ)) < 1) (h : ℝ) (g : Spin → ℝ) {N : ℕ}
    (hS : (originLocalObs d g).S ⊆ cubicBox d N) :
    plusStateExpectation J h β (originLocalObs d g) hS
      = minusStateExpectation J h β (originLocalObs d g) hS := by
  have hβJ : 0 ≤ β * J := mul_nonneg hβ hJ
  have hα0 : 0 ≤ (2 * (d : ℝ)) * Real.tanh (β * J) :=
    mul_nonneg (by positivity) (tanh_nonneg_of_nonneg hβJ)
  have hα1 : (2 * (d : ℝ)) * Real.tanh (β * J) < 1 := by
    have htanh := tanh_le_self hβJ
    have hnonneg : 0 ≤ 2 * (d : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left htanh hnonneg]
  have hp := tendsto_plusStateExpectation (h := h) hβ hJ (originLocalObs d g) hS
  have hm := tendsto_minusStateExpectation (h := h) hβ hJ (originLocalObs d g) hS
  have hdiff := hp.sub hm
  have hshift : Tendsto (fun k : ℕ => N + k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_add_left k N) tendsto_id
  have hc : Tendsto (fun k : ℕ => |g Spin.up - g Spin.down|
      * resolventTail d ((2 * (d : ℝ)) * Real.tanh (β * J)) (N + k)) atTop (𝓝 0) := by
    have := ((tendsto_resolventTail_atTop d hα0 hα1).comp hshift).const_mul
      (|g Spin.up - g Spin.down|)
    simpa using this
  have hzero : Tendsto (fun k : ℕ =>
      plusBoxObsExpectation (N + k) (N + k + 1) J h β (originLocalObs d g)
          (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1)))
        - plusBoxObsExpectation (N + k) (N + k + 1) J (-h) β (originLocalObs d g).flipObs
          (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1)))) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun k => ?_) hc
    rw [Real.norm_eq_abs]
    exact abs_plusBoxObs_sub_flipObs_originObs_le d hd hβ hJ hα h g (N + k)
      (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1)))
  have hlim := tendsto_nhds_unique hdiff hzero
  linarith [hlim]

/-- **Monotonicity of `g` from `g↓ ≤ g↑`**: a real function of `Spin` is monotone iff it is
nondecreasing from `down` to `up`. -/
theorem monotone_of_spin_le {g : Spin → ℝ} (hg : g Spin.down ≤ g Spin.up) : Monotone g := by
  intro a b hab
  match a, b with
  | Spin.down, Spin.down => exact le_refl _
  | Spin.down, Spin.up => exact hg
  | Spin.up, Spin.up => exact le_refl _
  | Spin.up, Spin.down => exact absurd hab (by decide)

/-- **The origin observable is monotone** when `g` is nondecreasing. -/
theorem originObs_monotone (d : ℕ) {g : Spin → ℝ} (hg : g Spin.down ≤ g Spin.up)
    {Λ : Finset (Fin d → ℤ)} (h0 : (0 : Fin d → ℤ) ∈ Λ) :
    Monotone (originObs d g h0) := fun _ _ hσσ' => monotone_of_spin_le hg (hσσ' ⟨0, h0⟩)

/-- **Infinite-volume boundary-condition-free limit existence for the origin observable** (GJ §17.1;
ℤ^d Dobrushin uniqueness, Issue #4214 §A).

For a **monotone** `g` and high temperature, every boundary-condition family `η` gives a
screened-box expectation of the origin observable that converges, along the cubic exhaustion, to
the **common** extremal value `plusStateExpectation J h β (originLocalObs d g) hS`.  Hence the Gibbs
expectation of the local observable exists and is independent of the boundary condition — the limit
existence half of Dobrushin uniqueness, complementing the volume-uniform boundary independence of PR
#4260.

Proof: the extremal sandwich (`gibbsExpectationBC_extremal_sandwich`) traps each term between the
`minusConfig` and `plusConfig` box expectations on the same induced graph and free region
`plusBoxInterior d (N+k) (N+k+1)`; both extremal sequences converge to `plusStateExpectation` (the
`+` one directly by `tendsto_plusStateExpectation`; the `−` one by `tendsto_minusStateExpectation`
rewritten through `plusBoxObsExpectation_flipObs_originObs_eq` and the coincidence
`plusStateExpectation_eq_minusStateExpectation_originObs`).  Apply the squeeze. -/
theorem tendsto_gibbsExpectationBC_originObs_extremal_limit (d : ℕ) (hd : 1 ≤ d) {β J : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (hα : β * J * (2 * (d : ℝ)) < 1) (h : ℝ) {g : Spin → ℝ}
    (hg : g Spin.down ≤ g Spin.up) {N : ℕ} (hS : (originLocalObs d g).S ⊆ cubicBox d N)
    (η : ∀ k : ℕ, Config (↑(cubicBox d (N + k + 1)) : Type _)) :
    Tendsto (fun k : ℕ =>
        gibbsExpectationBC (inducedGraph (latticeGraph d) (cubicBox d (N + k + 1))) β (fun _ => J) h
          (plusBoxInterior d (N + k) (N + k + 1)) (η k)
          (originObs d g (origin_mem_cubicBox d (N + k + 1))))
      atTop (𝓝 (plusStateExpectation J h β (originLocalObs d g) hS)) := by
  -- Upper extremal sequence: the `+` box expectation, `→ plusState`.
  have hupper : Tendsto (fun k : ℕ =>
      gibbsExpectationBC (inducedGraph (latticeGraph d) (cubicBox d (N + k + 1))) β (fun _ => J) h
        (plusBoxInterior d (N + k) (N + k + 1)) (plusConfig _)
        (originObs d g (origin_mem_cubicBox d (N + k + 1)))) atTop
      (𝓝 (plusStateExpectation J h β (originLocalObs d g) hS)) := by
    refine (tendsto_plusStateExpectation (h := h) hβ hJ (originLocalObs d g) hS).congr (fun k => ?_)
    exact plusBoxObsExpectation_originObs_eq d (N + k) (N + k + 1) g _
  -- Lower extremal sequence: the `−` box expectation, `→ minusState = plusState`.
  have hlower : Tendsto (fun k : ℕ =>
      gibbsExpectationBC (inducedGraph (latticeGraph d) (cubicBox d (N + k + 1))) β (fun _ => J) h
        (plusBoxInterior d (N + k) (N + k + 1)) (minusConfig _)
        (originObs d g (origin_mem_cubicBox d (N + k + 1)))) atTop
      (𝓝 (plusStateExpectation J h β (originLocalObs d g) hS)) := by
    have hm := tendsto_minusStateExpectation (h := h) hβ hJ (originLocalObs d g) hS
    rw [← plusStateExpectation_eq_minusStateExpectation_originObs d hd hβ hJ hα h g hS] at hm
    refine hm.congr (fun k => ?_)
    exact plusBoxObsExpectation_flipObs_originObs_eq d (N + k) (N + k + 1) g _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper (fun k => ?_) (fun k => ?_)
  · exact (gibbsExpectationBC_extremal_sandwich _ hβ (fun _ => hJ) _ (η k) _
      (originObs_monotone d hg (origin_mem_cubicBox d (N + k + 1)))).1
  · exact (gibbsExpectationBC_extremal_sandwich _ hβ (fun _ => hJ) _ (η k) _
      (originObs_monotone d hg (origin_mem_cubicBox d (N + k + 1)))).2

end Ambient

end IsingModel
