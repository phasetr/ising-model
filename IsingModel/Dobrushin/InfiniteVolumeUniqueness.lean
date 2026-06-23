import IsingModel.Dobrushin.InfiniteVolumeBoundaryInfluence
import IsingModel.Concrete.CubicExhaustion

/-!
# Cross-exhaustion ℤ^d infinite-volume Gibbs-state Dobrushin uniqueness (GJ §17.1, Issue #4214 §A)

This file is the cross-exhaustion capstone of the ℤ^d Dobrushin-uniqueness lift (Issue #4256). The
finite-graph Dobrushin uniqueness (`Dobrushin/Uniqueness.lean`) and the per-box card-free
boundary-influence estimate (`Dobrushin/InfiniteVolumeBoundaryInfluence.lean`, PR 2 of #4256) both
fix a single volume `Λ` *before* producing the influence radius `R`.  To pass to the infinite-volume
(cubic-exhaustion `Λ ↑ ℤ^d`) setting one must produce a *single* radius `R(ε)` that works
simultaneously for **every** stage `cubicBox d n` of the exhaustion, with the **same** observable
evaluated in every box.

## The observable-transport problem and its resolution

The card-free per-box bound is stated for an observable `f : Config ↑Λ → ℝ` local at a site
`x₀ : ↑Λ`.  As the box grows the subtype `↑Λ` changes, so a generic `f` cannot be carried across
stages.  We resolve this by fixing the observable to the **single spin at the origin**: for a fixed
`g : Spin → ℝ`, the observable `originObs d g h0 = fun σ => g (σ ⟨0, h0⟩)` is defined in every box
containing the origin (and the origin lies in every `cubicBox d n`, `origin_mem_cubicBox`).  Two
facts make it transport cleanly:
* it is local at the origin (`originObs_localAtSite`), and
* its single-site oscillation is the **box-independent** constant `|g ↑ − g ↓|`
  (`siteOsc_originObs`).

Because the radius `R(ε)` of the card-free estimate depends only on `d, β, J, ε` and
`siteOsc (origin) f`, and the latter is the same constant in every box, a single `R(ε)` controls the
boundary influence on `originObs g` uniformly across the whole exhaustion
(`gibbsExpectationBC_originObs_cubicExhaustion_boundary_influence_uniform`).  This is the
decay-of-influence (boundary-condition independence) half of Dobrushin uniqueness in infinite
volume, now genuinely **uniform in the volume** and **card-free** (no `Fintype.card` factor).

## Scope (honest gap)

This file delivers the volume-uniform *boundary-condition independence* of the local observable:
along the exhaustion, two boundary conditions agreeing on a fixed ball about the origin give Gibbs
expectations within `ε`, with `ε`-radius independent of the stage.  It does **not** assert existence
of the boundary-condition-free *limit* `lim_{n} ⟨originObs g⟩^{η_n}_{cubicBox d n}` as a single real
number: that requires a cross-box (DLR-consistency / monotonicity) comparison relating a fixed
boundary condition in `cubicBox d m` to one in `cubicBox d n` for `m ≤ n`, which the single-box
estimate of PR 2 does not provide and which is the remaining research-level content of Issue #4214
§A.  We record the uniform boundary independence here and flag limit existence as not-yet-done.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306; Georgii,
*Gibbs Measures and Phase Transitions*, Ch. 8; Friedli–Velenik, *Statistical Mechanics of Lattice
Systems*, §6.5 (Dobrushin uniqueness).
-/

namespace IsingModel

namespace Dobrushin

open Finset Filter Topology

/-- **The origin lies in every cubic box** `cubicBox d n`.  Every coordinate of the origin is `0`,
which lies in `Icc (-n) n` for all `n`. -/
theorem origin_mem_cubicBox (d n : ℕ) : (0 : Fin d → ℤ) ∈ Ambient.cubicBox d n := by
  rw [Ambient.mem_cubicBox]
  intro i
  simp only [Pi.zero_apply]
  exact ⟨neg_nonpos.mpr (Int.natCast_nonneg n), Int.natCast_nonneg n⟩

/-- **The single-spin-at-the-origin observable**: for a fixed `g : Spin → ℝ` and a box `Λ`
containing the origin, the observable on `Config ↑Λ` reading the spin at the origin and applying
`g`.  This is the transportable family carrying one observable across every stage of the cubic
exhaustion. -/
def originObs (d : ℕ) (g : Spin → ℝ) {Λ : Finset (Fin d → ℤ)}
    (h0 : (0 : Fin d → ℤ) ∈ Λ) : Config ↑Λ → ℝ :=
  fun σ => g (σ ⟨0, h0⟩)

/-- **The origin observable is local at the origin**: it depends only on the spin at the origin. -/
theorem originObs_localAtSite (d : ℕ) (g : Spin → ℝ) {Λ : Finset (Fin d → ℤ)}
    (h0 : (0 : Fin d → ℤ) ∈ Λ) :
    LocalAtSite (⟨0, h0⟩ : ↑Λ) (originObs d g h0) := by
  intro σ σ' hσ
  unfold originObs
  rw [hσ]

/-- **The single-site oscillation of the origin observable is the box-independent constant**
`|g ↑ − g ↓|`.  For every configuration `σ`, flipping the origin spin between `↑` and `↓` changes
`originObs d g h0` by exactly `g ↑ − g ↓` (the observable reads only the origin spin), so the
supremum defining `siteOsc` is the constant `|g ↑ − g ↓|`.  Crucially this value does not depend on
the box `Λ`, which is what makes the influence radius uniform across the exhaustion. -/
theorem siteOsc_originObs (d : ℕ) (g : Spin → ℝ) {Λ : Finset (Fin d → ℤ)}
    (h0 : (0 : Fin d → ℤ) ∈ Λ) :
    siteOsc (⟨0, h0⟩ : ↑Λ) (originObs d g h0) = |g Spin.up - g Spin.down| := by
  have hval : ∀ σ : Config ↑Λ,
      |originObs d g h0 (Function.update σ (⟨0, h0⟩ : ↑Λ) Spin.up)
        - originObs d g h0 (Function.update σ (⟨0, h0⟩ : ↑Λ) Spin.down)|
        = |g Spin.up - g Spin.down| := by
    intro σ
    unfold originObs
    simp only [Function.update_self]
  refine le_antisymm (siteOsc_le_of_forall (fun σ => (hval σ).le)) ?_
  calc |g Spin.up - g Spin.down|
      = |originObs d g h0 (Function.update (Classical.arbitrary _) (⟨0, h0⟩ : ↑Λ) Spin.up)
          - originObs d g h0 (Function.update (Classical.arbitrary _) (⟨0, h0⟩ : ↑Λ) Spin.down)| :=
        (hval _).symm
    _ ≤ siteOsc (⟨0, h0⟩ : ↑Λ) (originObs d g h0) := abs_sub_update_le_siteOsc _ _ _

/-- **Card-free per-stage boundary-influence bound for the origin observable** (GJ §17.1).

For a fixed exhaustion stage `cubicBox d n`, if two boundary conditions `η, η'` agree off a finite
set `S` every site of which lies at ℓ¹-lattice distance at least `R` from the origin, then the
boundary-condition difference of the origin observable `originObs d g` is bounded by
`|g ↑ − g ↓| · resolventTail d (2d·tanh βJ) R`.  This specialises
`gibbsExpectationBC_localObs_inducedLattice_dist_le_resolventTail` (#4258) to the transportable
origin observable, rewriting its `siteOsc` coefficient by the box-independent constant
(`siteOsc_originObs`).  The bound carries **no** `Fintype.card ↑(cubicBox d n)` factor. -/
theorem gibbsExpectationBC_originObs_inducedLattice_dist_le_resolventTail
    (d : ℕ) (hd : 1 ≤ d) {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hα : β * J * (2 * (d : ℝ)) < 1) (h : ℝ) (g : Spin → ℝ) (n : ℕ)
    (Λ' S : Finset ↑(Ambient.cubicBox d n)) {η η' : Config ↑(Ambient.cubicBox d n)}
    (hagree : agreesOff S η η') (R : ℕ)
    (hfar : ∀ y ∈ S, R ≤ latticeDistance d (0 : Fin d → ℤ) y.val) :
    |gibbsExpectationBC (Ambient.inducedGraph (latticeGraph d) (Ambient.cubicBox d n)) β
          (fun _ => J) h Λ' η (originObs d g (origin_mem_cubicBox d n))
        - gibbsExpectationBC (Ambient.inducedGraph (latticeGraph d) (Ambient.cubicBox d n)) β
          (fun _ => J) h Λ' η' (originObs d g (origin_mem_cubicBox d n))|
      ≤ |g Spin.up - g Spin.down| * resolventTail d ((2 * (d : ℝ)) * Real.tanh (β * J)) R := by
  have hbound := gibbsExpectationBC_localObs_inducedLattice_dist_le_resolventTail
    d hd hβJ hα h Λ' S hagree (originObs_localAtSite d g (origin_mem_cubicBox d n)) R hfar
  rwa [siteOsc_originObs] at hbound

/-- **Cross-exhaustion volume-uniform boundary-condition independence of a local observable**
(GJ §17.1; ℤ^d Dobrushin-uniqueness capstone, Issue #4256).

At high temperature (`0 ≤ βJ`, `βJ·2d < 1`, `d ≥ 1`), for the fixed single-spin-at-origin observable
`originObs d g` and every tolerance `ε > 0` there is a **single** radius `R` such that for **every**
exhaustion stage `n`, every Gibbs region `Λ'`, every disagreement set `S`, and all boundary
conditions `η, η'` agreeing off `S` with each disagreement site at ℓ¹-lattice distance at least `R`
from the origin, the boundary-condition difference of `originObs d g` is at most `ε`.

The radius `R` depends only on `d, β, J, ε` and the box-independent constant `|g ↑ − g ↓|` —
**not** on the stage `n`, the disagreement set, or the volume cardinality.  This is the card-free,
volume-uniform decay-of-influence content of Dobrushin uniqueness in the ℤ^d infinite-volume limit:
the same observable evaluated in every box becomes independent of the boundary condition as the
disagreement recedes, uniformly along the cubic exhaustion.  (Existence of the boundary-free *limit*
itself is a separate cross-box comparison, not asserted here; see the module docstring.) -/
theorem gibbsExpectationBC_originObs_cubicExhaustion_boundary_influence_uniform
    (d : ℕ) (hd : 1 ≤ d) {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hα : β * J * (2 * (d : ℝ)) < 1) (h : ℝ) (g : Spin → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℕ, ∀ (n : ℕ) (Λ' S : Finset ↑(Ambient.cubicBox d n))
        (η η' : Config ↑(Ambient.cubicBox d n)), agreesOff S η η' →
      (∀ y ∈ S, R ≤ latticeDistance d (0 : Fin d → ℤ) y.val) →
        |gibbsExpectationBC (Ambient.inducedGraph (latticeGraph d) (Ambient.cubicBox d n)) β
              (fun _ => J) h Λ' η (originObs d g (origin_mem_cubicBox d n))
            - gibbsExpectationBC (Ambient.inducedGraph (latticeGraph d) (Ambient.cubicBox d n)) β
              (fun _ => J) h Λ' η' (originObs d g (origin_mem_cubicBox d n))|
          ≤ ε := by
  have hα0 : 0 ≤ (2 * (d : ℝ)) * Real.tanh (β * J) :=
    mul_nonneg (by positivity) (tanh_nonneg_of_nonneg hβJ)
  have hα1 : (2 * (d : ℝ)) * Real.tanh (β * J) < 1 := by
    have htanh := tanh_le_self hβJ
    have hnonneg : 0 ≤ 2 * (d : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left htanh hnonneg]
  have htend : Tendsto
      (fun R : ℕ => |g Spin.up - g Spin.down|
          * resolventTail d ((2 * (d : ℝ)) * Real.tanh (β * J)) R)
      atTop (𝓝 0) := by
    have h0 := (tendsto_resolventTail_atTop d hα0 hα1).const_mul (|g Spin.up - g Spin.down|)
    simpa using h0
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨R, hR⟩ := htend ε hε
  refine ⟨R, fun n Λ' S η η' hagree hfar => ?_⟩
  refine (gibbsExpectationBC_originObs_inducedLattice_dist_le_resolventTail
    d hd hβJ hα h g n Λ' S hagree R hfar).trans ?_
  have hdist := hR R le_rfl
  rw [Real.dist_eq, sub_zero] at hdist
  exact (le_abs_self _).trans hdist.le

/-- **Disagreement-set form of the cross-exhaustion boundary independence** (GJ §17.1).

Restatement of `gibbsExpectationBC_originObs_cubicExhaustion_boundary_influence_uniform` with the
disagreement set described intrinsically: a single radius `R(ε)` such that, uniformly over every
exhaustion stage `n` and Gibbs region `Λ'`, any two boundary conditions `η, η'` differing only at
sites at ℓ¹-lattice distance at least `R` from the origin (i.e. agreeing on the ball of radius `R`)
give Gibbs expectations of `originObs d g` within `ε`.  This is the most direct reading of "the
infinite-volume expectation of a local observable is independent of the boundary condition", uniform
in the volume. -/
theorem gibbsExpectationBC_originObs_cubicExhaustion_boundary_influence_ball
    (d : ℕ) (hd : 1 ≤ d) {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hα : β * J * (2 * (d : ℝ)) < 1) (h : ℝ) (g : Spin → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℕ, ∀ (n : ℕ) (Λ' : Finset ↑(Ambient.cubicBox d n))
        (η η' : Config ↑(Ambient.cubicBox d n)),
      (∀ y : ↑(Ambient.cubicBox d n), η y ≠ η' y → R ≤ latticeDistance d (0 : Fin d → ℤ) y.val) →
        |gibbsExpectationBC (Ambient.inducedGraph (latticeGraph d) (Ambient.cubicBox d n)) β
              (fun _ => J) h Λ' η (originObs d g (origin_mem_cubicBox d n))
            - gibbsExpectationBC (Ambient.inducedGraph (latticeGraph d) (Ambient.cubicBox d n)) β
              (fun _ => J) h Λ' η' (originObs d g (origin_mem_cubicBox d n))|
          ≤ ε := by
  obtain ⟨R, hR⟩ :=
    gibbsExpectationBC_originObs_cubicExhaustion_boundary_influence_uniform d hd hβJ hα h g hε
  refine ⟨R, fun n Λ' η η' hfar => ?_⟩
  refine hR n Λ' (Finset.univ.filter (fun y => η y ≠ η' y)) η η' ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
    exact hi.symm
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    exact hfar y hy

end Dobrushin

end IsingModel
