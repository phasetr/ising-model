import IsingModel.Dobrushin.InfiniteVolumeUniformInfluence
import IsingModel.Dobrushin.ExponentialLocality

/-!
# Card-free volume-uniform boundary influence on cubic-lattice graphs

This file composes the card-free far-field resolvent tail
(`dobrushinResolvent_farSum_le_resolventTail`, the ℤ^d-uniqueness-lift ingredient of
`InfiniteVolumeUniformInfluence.lean`) with the Dobrushin row-sum locality bound
(`gibbsExpectationBC_localObs_dist_le_resolvent_row`).

The result is a boundary-influence estimate on the induced cubic-lattice graph
`GΛ = Ambient.inducedGraph (latticeGraph d) Λ` that, unlike the finite-graph form
`gibbsExpectationBC_localObs_boundary_influence_uniform_small`, carries **no** `Fintype.card`
factor: the radius `R` at which the boundary influence on a fixed local observable drops below a
target `ε` depends only on `d`, `β`, `J`, `ε`, and the site oscillation of the observable — never on
the size of the disagreement set or of the volume. This is the volume-uniform decay-of-influence
content needed to pass to the infinite-volume Gibbs state.
-/

namespace IsingModel

namespace Dobrushin

open Finset Filter Topology

/-- **Card-free far-field boundary-influence bound on a cubic-lattice volume** (GJ §17.1).

For the induced graph `GΛ = Ambient.inducedGraph (latticeGraph d) Λ`, if the boundary conditions
`η, η'` agree off a finite set `S` every site of which lies at ℓ¹-lattice distance at least `R`
from the observable site `x₀`, then the boundary-condition difference of a single-site observable
`f` (local at `x₀`) is bounded by `siteOsc x₀ f · resolventTail d (2d·tanh βJ) R`. The bound is
uniform in the volume `Λ` and the disagreement set `S`, containing **no** `Fintype.card ↑Λ` or
`S.card` factor. -/
theorem gibbsExpectationBC_localObs_inducedLattice_dist_le_resolventTail
    (d : ℕ) {Λ : Finset (Fin d → ℤ)} (hd : 1 ≤ d) {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hα : β * J * (2 * (d : ℝ)) < 1) (h : ℝ) (Λ' S : Finset ↑Λ) {η η' : Config ↑Λ}
    (hagree : agreesOff S η η') {x₀ : ↑Λ} {f : Config ↑Λ → ℝ} (hf : LocalAtSite x₀ f)
    (R : ℕ) (hfar : ∀ y ∈ S, R ≤ latticeDistance d x₀.val y.val) :
    |gibbsExpectationBC (Ambient.inducedGraph (latticeGraph d) Λ) β (fun _ => J) h Λ' η f
        - gibbsExpectationBC (Ambient.inducedGraph (latticeGraph d) Λ) β (fun _ => J) h Λ' η' f|
      ≤ siteOsc x₀ f * resolventTail d ((2 * (d : ℝ)) * Real.tanh (β * J)) R := by
  have hΔ : β * J * (Ambient.inducedGraph (latticeGraph d) Λ).maxDegree < 1 := by
    have hdeg : ((Ambient.inducedGraph (latticeGraph d) Λ).maxDegree : ℝ) ≤ 2 * (d : ℝ) := by
      exact_mod_cast induced_latticeGraph_maxDegree_le d Λ
    calc β * J * ((Ambient.inducedGraph (latticeGraph d) Λ).maxDegree : ℝ)
        ≤ β * J * (2 * (d : ℝ)) := mul_le_mul_of_nonneg_left hdeg hβJ
      _ < 1 := hα
  refine (gibbsExpectationBC_localObs_dist_le_resolvent_row
      (Ambient.inducedGraph (latticeGraph d) Λ) hβJ hΔ h Λ' S hagree hf).trans ?_
  exact mul_le_mul_of_nonneg_left
    (dobrushinResolvent_farSum_le_resolventTail d hd hβJ hα x₀ S R hfar)
    (siteOsc_nonneg x₀ f)

/-- **Card-free volume-uniform vanishing of the boundary influence** (GJ §17.1; ℤ^d lift).

For a fixed cubic-lattice volume `Λ`, observable site `x₀`, and observable `f` local at `x₀`, at
high temperature (`0 ≤ βJ`, `βJ·2d < 1`, `d ≥ 1`) and for every `ε > 0` there is a radius `R` such
that for **all** Gibbs regions `Λ'`, all disagreement sets `S`, and all boundary conditions `η, η'`
agreeing off `S` with every disagreement site at ℓ¹-lattice distance at least `R` from `x₀`, the
boundary-condition difference is at most `ε`. Crucially `R` depends only on `d, β, J, ε` and
`siteOsc x₀ f` — **not** on the size of `S` (which is `∀`-quantified after `∃ R`); and the bound of
the underlying estimate carries no volume-cardinality factor (see
`gibbsExpectationBC_localObs_inducedLattice_dist_le_resolventTail`). This is the card-free
improvement over the finite-graph `gibbsExpectationBC_localObs_boundary_influence_uniform_small`,
whose radius grows with `Fintype.card`. (The volume `Λ`, site `x₀`, and observable `f` are fixed
before `∃ R` here; the cross-exhaustion `ℤ^d` uniqueness is the subsequent step.) -/
theorem gibbsExpectationBC_localObs_inducedLattice_boundary_influence_uniform_small
    (d : ℕ) {Λ : Finset (Fin d → ℤ)} (hd : 1 ≤ d) {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hα : β * J * (2 * (d : ℝ)) < 1) (h : ℝ) {x₀ : ↑Λ} {f : Config ↑Λ → ℝ}
    (hf : LocalAtSite x₀ f) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℕ, ∀ (Λ' S : Finset ↑Λ) (η η' : Config ↑Λ), agreesOff S η η' →
      (∀ y ∈ S, R ≤ latticeDistance d x₀.val y.val) →
        |gibbsExpectationBC (Ambient.inducedGraph (latticeGraph d) Λ) β (fun _ => J) h Λ' η f
            - gibbsExpectationBC (Ambient.inducedGraph (latticeGraph d) Λ) β (fun _ => J) h Λ' η' f|
          ≤ ε := by
  have hα0 : 0 ≤ (2 * (d : ℝ)) * Real.tanh (β * J) :=
    mul_nonneg (by positivity) (real_tanh_nonneg hβJ)
  have hα1 : (2 * (d : ℝ)) * Real.tanh (β * J) < 1 := by
    have htanh := tanh_le_self hβJ
    have hnonneg : 0 ≤ 2 * (d : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left htanh hnonneg]
  have htend : Tendsto
      (fun R : ℕ => siteOsc x₀ f * resolventTail d ((2 * (d : ℝ)) * Real.tanh (β * J)) R)
      atTop (𝓝 0) := by
    have h0 := (tendsto_resolventTail_atTop d hα0 hα1).const_mul (siteOsc x₀ f)
    simpa using h0
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨R, hR⟩ := htend ε hε
  refine ⟨R, fun Λ' S η η' hagree hfar => ?_⟩
  refine (gibbsExpectationBC_localObs_inducedLattice_dist_le_resolventTail
    d hd hβJ hα h Λ' S hagree hf R hfar).trans ?_
  have hdist := hR R le_rfl
  rw [Real.dist_eq, sub_zero] at hdist
  exact (le_abs_self _).trans hdist.le

end Dobrushin

end IsingModel
