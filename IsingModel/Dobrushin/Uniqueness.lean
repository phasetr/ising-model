import IsingModel.Dobrushin.ExponentialLocality

/-!
# Finite-graph Dobrushin uniqueness: vanishing of the boundary influence (GJ §17.1, Issue #4214 §A)

The capstone of the single-site Dobrushin comparison programme (`Dobrushin/ComparisonTheorem.lean`,
`Dobrushin/ExponentialLocality.lean`, Issue #4214 §A, PRs #4215–#4223).  The exponential spatial
mixing bound (`gibbsExpectationBC_localObs_dist_le_exponential_spatial_mixing`)
\[
  |⟨f⟩^η_Λ − ⟨f⟩^{η'}_Λ| ≤ \mathrm{siteOsc}_{x₀}(f)\cdot |S|\cdot \frac{α^{R}}{1−α},
  \qquad S = \{y : η_y ≠ η'_y\},\ α = Δ(G)\tanh(βJ),
\]
holds uniformly in the volume `Λ`.  On the finite graph `ι` the disagreement cardinality is bounded
by the fixed constant `Fintype.card ι`, so the radius-`R` bound is dominated by
`siteOsc x₀ f · (Fintype.card ι) · α^R/(1−α)`, which tends to `0` as `R → ∞` independently of
`η, η', Λ`.  This is the finite-graph **Dobrushin uniqueness** statement: at high temperature the
finite-volume expectation of a local observable becomes independent of the boundary condition once
the boundary disagreement is pushed far enough from the observable — the decay-of-influence content
of the Dobrushin uniqueness theorem (GJ §17.1, Georgii, *Gibbs Measures and Phase Transitions*,
Ch. 8).

## Main results
* `gibbsExpectationBC_localObs_dist_le_card_univ_pow_radius` — the boundary-condition difference is
  bounded by `siteOsc x₀ f · (Fintype.card ι) · α^R/(1−α)`, uniformly in `η, η', Λ`.
* `gibbsExpectationBC_localObs_boundary_influence_uniform_small` — for every `ε > 0` there is a
  radius `R` beyond which the boundary influence on `f` is `≤ ε`, uniformly in `Λ` and in any pair
  of boundary conditions agreeing on the ball of radius `R` about `x₀`.

The full `ℤ^d` *infinite-volume* Gibbs-state uniqueness (the last bullet of Issue #4214 §A) remains
research-level: it requires lifting these finite-graph bounds to the (non-`Fintype`) lattice, where
the `Fintype.card ι` cardinality factor is unavailable.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306; Georgii,
*Gibbs Measures and Phase Transitions*, Ch. 8.
-/

namespace IsingModel

namespace Dobrushin

open Finset Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (G : SimpleGraph ι) [Fintype G.edgeSet] [DecidableRel G.Adj]

/-- **Cardinality-uniform Dobrushin spatial-mixing bound** (GJ §17.1): on the finite graph `ι` the
disagreement set `{y : η_y ≠ η'_y}` has at most `Fintype.card ι` elements, so the exponential
spatial mixing bound is dominated by `siteOsc x₀ f · (Fintype.card ι) · α^R/(1−α)` — uniform in the
boundary conditions `η, η'` and the volume `Λ`. -/
theorem gibbsExpectationBC_localObs_dist_le_card_univ_pow_radius {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hΔ : β * J * G.maxDegree < 1) (h : ℝ) (Λ : Finset ι) {η η' : Config ι}
    {x₀ : ι} {f : Config ι → ℝ} (hf : LocalAtSite x₀ f) (R : ℕ)
    (hfar : ∀ y, η y ≠ η' y → R ≤ G.dist x₀ y) :
    |gibbsExpectationBC G β (fun _ => J) h Λ η f - gibbsExpectationBC G β (fun _ => J) h Λ η' f|
      ≤ siteOsc x₀ f * ((Fintype.card ι : ℝ) *
          (isingDobrushinCoeff G β J ^ R * (1 - isingDobrushinCoeff G β J)⁻¹)) := by
  refine (gibbsExpectationBC_localObs_dist_le_exponential_spatial_mixing
    G hβJ hΔ h Λ hf R hfar).trans ?_
  have hα0 : 0 ≤ isingDobrushinCoeff G β J := isingDobrushinCoeff_nonneg G hβJ
  have hα1 : isingDobrushinCoeff G β J < 1 := isingDobrushinCoeff_lt_one_of_high_temp G hβJ hΔ
  have hXnonneg : 0 ≤ isingDobrushinCoeff G β J ^ R * (1 - isingDobrushinCoeff G β J)⁻¹ := by
    have : 0 < 1 - isingDobrushinCoeff G β J := by linarith
    positivity
  refine mul_le_mul_of_nonneg_left ?_ (siteOsc_nonneg x₀ f)
  refine mul_le_mul_of_nonneg_right ?_ hXnonneg
  calc ((univ.filter fun y => η y ≠ η' y).card : ℝ)
      ≤ ((univ : Finset ι).card : ℝ) := by
        exact_mod_cast Finset.card_filter_le _ _
    _ = (Fintype.card ι : ℝ) := by rw [Finset.card_univ]

/-- **Finite-graph Dobrushin uniqueness — vanishing of the boundary influence** (GJ §17.1; Georgii
Ch. 8): at high temperature, for an observable `f` local at `x₀` and every tolerance `ε > 0`, there
is a radius `R` beyond which the boundary condition has influence `≤ ε` on the finite-volume
expectation of `f`, *uniformly* in the volume `Λ` and in any pair of boundary conditions `η, η'`
that agree on the ball of radius `R` about `x₀` (i.e. differ only at sites `y` with
`R ≤ d_G(x₀, y)`).  Hence the finite-volume expectation of a local observable becomes independent of
the boundary condition as the disagreement recedes — the decay-of-influence content of the Dobrushin
uniqueness theorem.

Proof: the cardinality-uniform spatial-mixing bound
(`gibbsExpectationBC_localObs_dist_le_card_univ_pow_radius`) dominates the boundary difference by
`c · α^R/(1−α)` with the fixed constant `c = siteOsc x₀ f · (Fintype.card ι)`; this radius-bound
tends to `0` as `R → ∞` (`tendsto_dobrushin_radius_bound_atTop`), so it is eventually `≤ ε`. -/
theorem gibbsExpectationBC_localObs_boundary_influence_uniform_small {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hΔ : β * J * G.maxDegree < 1) (h : ℝ) {x₀ : ι} {f : Config ι → ℝ} (hf : LocalAtSite x₀ f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℕ, ∀ (Λ : Finset ι) (η η' : Config ι),
      (∀ y, η y ≠ η' y → R ≤ G.dist x₀ y) →
        |gibbsExpectationBC G β (fun _ => J) h Λ η f
          - gibbsExpectationBC G β (fun _ => J) h Λ η' f| ≤ ε := by
  have htend := tendsto_dobrushin_radius_bound_atTop G hβJ hΔ
    (siteOsc x₀ f * (Fintype.card ι : ℝ))
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨R, hR⟩ := htend ε hε
  refine ⟨R, fun Λ η η' hfar => ?_⟩
  refine (gibbsExpectationBC_localObs_dist_le_card_univ_pow_radius G hβJ hΔ h Λ hf R hfar).trans ?_
  have hdist := hR R le_rfl
  rw [Real.dist_eq, sub_zero] at hdist
  calc siteOsc x₀ f * ((Fintype.card ι : ℝ) *
          (isingDobrushinCoeff G β J ^ R * (1 - isingDobrushinCoeff G β J)⁻¹))
      = siteOsc x₀ f * (Fintype.card ι : ℝ) *
          (isingDobrushinCoeff G β J ^ R * (1 - isingDobrushinCoeff G β J)⁻¹) := by ring
    _ ≤ |siteOsc x₀ f * (Fintype.card ι : ℝ) *
          (isingDobrushinCoeff G β J ^ R * (1 - isingDobrushinCoeff G β J)⁻¹)| := le_abs_self _
    _ ≤ ε := hdist.le

end Dobrushin

end IsingModel
