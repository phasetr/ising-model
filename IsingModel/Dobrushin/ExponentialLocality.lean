import IsingModel.Dobrushin.Locality
import IsingModel.Dobrushin.ResolventDecay

/-!
# Dobrushin exponential spatial mixing (GJ §17.1, Issue #4214 §A)

The payoff of the single-site Dobrushin comparison theorem: composing the locality bound
(`gibbsExpectationBC_localObs_dist_le_resolvent_row`, the comparison collapsed to the observable
site `x₀`) with the exponential distance-decay of the resolvent
(`dobrushinResolvent_le_pow_dist`, `R_{xy} ≤ α^{d_G(x,y)}/(1−α)`) gives **exponential spatial
mixing**: for an observable `f` local at `x₀` and boundary conditions `η, η'` differing only on a
set all of whose sites lie at graph distance `≥ R` from `x₀`,
\[
  |⟨f⟩^η_Λ − ⟨f⟩^{η'}_Λ|
    ≤ \mathrm{siteOsc}_{x₀}(f)\cdot |S|\cdot \frac{α^{R}}{1−α},
  \qquad α = Δ(G)\tanh(βJ).
\]
The boundary sensitivity decays exponentially in the distance from the observable to the differing
set — the quantitative Dobrushin-uniqueness/decay-of-influence statement of GJ §17.1. The bound is
uniform in the volume `Λ` (it does not appear on the right), the seed of the infinite-volume
uniqueness argument.

* `gibbsExpectationBC_localObs_dist_le_resolvent_pow_dist` — the per-distance bound
  `≤ siteOsc x₀ f · ∑_{y∈S} α^{d_G(x₀,y)}/(1−α)`.
* `gibbsExpectationBC_localObs_dist_le_card_mul_pow_radius` — the uniform exponential bound
  `≤ siteOsc x₀ f · |S| · α^R/(1−α)` when `S` lies beyond radius `R`.
* `gibbsExpectationBC_localObs_dist_le_exponential_spatial_mixing` — the same with the disagreement
  set taken internally as `{y | η y ≠ η' y}`.
* `tendsto_dobrushin_radius_bound_atTop` — the bound vanishes exponentially as `R → ∞`.

Two caveats on reading these as genuine spatial decay. First, the `R → ∞` vanishing applies with a
*fixed* (or cardinality-controlled) disagreement set `S`; if `S = S_R` grows with `R` one
additionally needs `|S_R|·α^R → 0`. Second, `G.dist x₀ y` is the junk value `0` for a `y`
unreachable from `x₀` (so the radius hypothesis `R ≤ G.dist x₀ y` cannot hold for `R > 0` at such a
`y`); this is not a soundness gap — the resolvent entry itself is `0`
(`dobrushinResolvent_eq_zero_of_not_reachable`).

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306.
-/

namespace IsingModel

namespace Dobrushin

open Finset Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (G : SimpleGraph ι) [Fintype G.edgeSet] [DecidableRel G.Adj]

/-- **Per-distance Dobrushin locality bound** (GJ §17.1): for `f` local at `x₀`, the
boundary-condition difference is bounded by the resolvent row at `x₀` with each entry replaced
by its exponential distance-decay estimate `R_{x₀ y} ≤ α^{d_G(x₀,y)}/(1−α)`. -/
theorem gibbsExpectationBC_localObs_dist_le_resolvent_pow_dist {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hΔ : β * J * G.maxDegree < 1) (h : ℝ) (Λ S : Finset ι) {η η' : Config ι}
    (hagree : agreesOff S η η') {x₀ : ι} {f : Config ι → ℝ} (hf : LocalAtSite x₀ f) :
    |gibbsExpectationBC G β (fun _ => J) h Λ η f - gibbsExpectationBC G β (fun _ => J) h Λ η' f|
      ≤ siteOsc x₀ f * ∑ y ∈ S,
          isingDobrushinCoeff G β J ^ G.dist x₀ y * (1 - isingDobrushinCoeff G β J)⁻¹ := by
  refine (gibbsExpectationBC_localObs_dist_le_resolvent_row G hβJ hΔ h Λ S hagree hf).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (siteOsc_nonneg x₀ f)
  exact Finset.sum_le_sum fun y _ => dobrushinResolvent_le_pow_dist G hβJ hΔ x₀ y

/-- **Exponential spatial mixing** (GJ §17.1): if `f` is local at `x₀` and the boundary conditions
`η, η'` differ only on a set `S` every site of which lies at graph distance `≥ R` from `x₀`, then
the expectation difference is at most `siteOsc x₀ f · |S| · α^R/(1−α)`, decaying exponentially in
`R` (`α = Δ(G)·tanh(βJ)` the Dobrushin coefficient). The bound is uniform in the volume `Λ`. -/
theorem gibbsExpectationBC_localObs_dist_le_card_mul_pow_radius {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hΔ : β * J * G.maxDegree < 1) (h : ℝ) (Λ S : Finset ι) {η η' : Config ι}
    (hagree : agreesOff S η η') {x₀ : ι} {f : Config ι → ℝ} (hf : LocalAtSite x₀ f)
    (R : ℕ) (hfar : ∀ y ∈ S, R ≤ G.dist x₀ y) :
    |gibbsExpectationBC G β (fun _ => J) h Λ η f - gibbsExpectationBC G β (fun _ => J) h Λ η' f|
      ≤ siteOsc x₀ f * ((S.card : ℝ) *
          (isingDobrushinCoeff G β J ^ R * (1 - isingDobrushinCoeff G β J)⁻¹)) := by
  have hα0 : 0 ≤ isingDobrushinCoeff G β J := isingDobrushinCoeff_nonneg G hβJ
  have hα1 : isingDobrushinCoeff G β J < 1 := isingDobrushinCoeff_lt_one_of_high_temp G hβJ hΔ
  have hinv_nonneg : 0 ≤ (1 - isingDobrushinCoeff G β J)⁻¹ := inv_nonneg.mpr (by linarith)
  refine (gibbsExpectationBC_localObs_dist_le_resolvent_pow_dist G hβJ hΔ h Λ S hagree hf).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (siteOsc_nonneg x₀ f)
  have hterm : ∀ y ∈ S,
      isingDobrushinCoeff G β J ^ G.dist x₀ y * (1 - isingDobrushinCoeff G β J)⁻¹
        ≤ isingDobrushinCoeff G β J ^ R * (1 - isingDobrushinCoeff G β J)⁻¹ :=
    fun y hy => mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one hα0 hα1.le (hfar y hy)) hinv_nonneg
  simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul S _ _ hterm

/-- **Exponential spatial mixing, internal disagreement support** (GJ §17.1): the same bound with
the differing set taken explicitly as `S = {y | η y ≠ η' y}`. If every disagreement site lies at
distance `≥ R` from the observable site `x₀`, the expectation difference is at most
`siteOsc x₀ f · |{y | η y ≠ η' y}| · α^R/(1−α)`. -/
theorem gibbsExpectationBC_localObs_dist_le_exponential_spatial_mixing {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hΔ : β * J * G.maxDegree < 1) (h : ℝ) (Λ : Finset ι) {η η' : Config ι}
    {x₀ : ι} {f : Config ι → ℝ} (hf : LocalAtSite x₀ f) (R : ℕ)
    (hfar : ∀ y, η y ≠ η' y → R ≤ G.dist x₀ y) :
    |gibbsExpectationBC G β (fun _ => J) h Λ η f - gibbsExpectationBC G β (fun _ => J) h Λ η' f|
      ≤ siteOsc x₀ f * (((univ.filter fun y => η y ≠ η' y).card : ℝ) *
          (isingDobrushinCoeff G β J ^ R * (1 - isingDobrushinCoeff G β J)⁻¹)) := by
  classical
  set S : Finset ι := univ.filter fun y => η y ≠ η' y with hS
  have hagree : agreesOff S η η' := by
    intro y hy
    simp only [hS, mem_filter, mem_univ, true_and, not_not] at hy
    exact hy.symm
  have hfarS : ∀ y ∈ S, R ≤ G.dist x₀ y := by
    intro y hy
    simp only [hS, mem_filter, mem_univ, true_and] at hy
    exact hfar y hy
  exact gibbsExpectationBC_localObs_dist_le_card_mul_pow_radius G hβJ hΔ h Λ S hagree hf R hfarS

omit [Fintype G.edgeSet] [DecidableEq ι] in
/-- **The Dobrushin influence bound vanishes exponentially** (GJ §17.1): for any constant `c`, the
radius-`R` exponential-mixing bound `c · α^R/(1−α)` tends to `0` as `R → ∞` (`0 ≤ α < 1` under the
high-temperature condition). Hence the boundary influence on a local observable can be made
arbitrarily small by pushing the disagreement set far enough away — the qualitative
decay-of-influence content of Dobrushin uniqueness. -/
theorem tendsto_dobrushin_radius_bound_atTop {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hΔ : β * J * G.maxDegree < 1) (c : ℝ) :
    Tendsto (fun R : ℕ => c * (isingDobrushinCoeff G β J ^ R
        * (1 - isingDobrushinCoeff G β J)⁻¹)) atTop (nhds 0) := by
  have hα0 : 0 ≤ isingDobrushinCoeff G β J := isingDobrushinCoeff_nonneg G hβJ
  have hα1 : isingDobrushinCoeff G β J < 1 := isingDobrushinCoeff_lt_one_of_high_temp G hβJ hΔ
  have hpow : Tendsto (fun R : ℕ => isingDobrushinCoeff G β J ^ R) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hα0 hα1
  simpa using (hpow.mul_const (1 - isingDobrushinCoeff G β J)⁻¹).const_mul c

end Dobrushin

end IsingModel
