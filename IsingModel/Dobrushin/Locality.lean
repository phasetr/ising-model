import IsingModel.Dobrushin.ComparisonTheorem
import IsingModel.Dobrushin.SingleSiteObservableComparison
import IsingModel.Dobrushin.InfluenceMatrixResolvent

/-!
# Dobrushin locality of single-site observables (GJ §17.1, Issue #4214 §A)

Consequences of the Dobrushin comparison theorem for observables local at a single site. For `f`
local at `x₀`, the comparison sum `∑_x ∑_{y∈S} R_{xy}·siteOsc x f` collapses to the single `x = x₀`
row (the oscillation vanishes off `x₀`), so the boundary sensitivity of `⟨f⟩^η_Λ` is governed by the
resolvent row at `x₀`:
\[
  |⟨f⟩^η_Λ − ⟨f⟩^{η'}_Λ| ≤ \mathrm{siteOsc}_{x₀}(f)·∑_{y∈S} R_{x₀ y}
    ≤ \mathrm{siteOsc}_{x₀}(f)·(1 − α)^{-1},
\]
with `α = Δ(G)·tanh(βJ)` the Dobrushin coefficient. The uniform bound (independent of `Λ`, `S`, `η`,
`η'`) is the Dobrushin uniqueness/locality estimate.

* `siteOsc_eq_zero_of_localAtSite` — the oscillation of a single-site-local observable vanishes off
  its site.
* `gibbsExpectationBC_localObs_dist_le_resolvent_row` — the collapsed comparison.
* `gibbsExpectationBC_localObs_dist_le_totalInfluence` — the uniform locality bound.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306.
-/

namespace IsingModel

namespace Dobrushin

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (G : SimpleGraph ι) [Fintype G.edgeSet] [DecidableRel G.Adj]

omit [Fintype G.edgeSet] [DecidableRel G.Adj] in
/-- **The single-site oscillation vanishes off the locality site**: if `f` is local at `x₀`, then
`siteOsc x f = 0` for every `x ≠ x₀` (changing the spin at `x` leaves `σ_{x₀}` unchanged, so `f` is
unchanged). -/
theorem siteOsc_eq_zero_of_localAtSite {x₀ x : ι} {f : Config ι → ℝ} (hf : LocalAtSite x₀ f)
    (hx : x ≠ x₀) : siteOsc x f = 0 := by
  refine le_antisymm (siteOsc_le_of_forall fun σ => ?_) (siteOsc_nonneg x f)
  have hupd : (Function.update σ x Spin.up) x₀ = (Function.update σ x Spin.down) x₀ := by
    rw [Function.update_of_ne (fun h => hx h.symm), Function.update_of_ne (fun h => hx h.symm)]
  rw [hf _ _ hupd, sub_self, abs_zero]

/-- **The collapsed Dobrushin comparison for a single-site observable** (GJ §17.1): for `f` local at
`x₀`, the boundary-condition difference is governed by the resolvent row at `x₀`,
`|⟨f⟩^η_Λ − ⟨f⟩^{η'}_Λ| ≤ siteOsc x₀ f · ∑_{y∈S} R_{x₀ y}`. -/
theorem gibbsExpectationBC_localObs_dist_le_resolvent_row {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hΔ : β * J * G.maxDegree < 1) (h : ℝ) (Λ S : Finset ι) {η η' : Config ι}
    (hagree : agreesOff S η η') {x₀ : ι} {f : Config ι → ℝ} (hf : LocalAtSite x₀ f) :
    |gibbsExpectationBC G β (fun _ => J) h Λ η f - gibbsExpectationBC G β (fun _ => J) h Λ η' f|
      ≤ siteOsc x₀ f * ∑ y ∈ S, dobrushinResolvent G β J x₀ y := by
  refine (gibbsExpectationBC_dist_le_resolvent_sum G hβJ hΔ h Λ S hagree f).trans (le_of_eq ?_)
  rw [Finset.sum_eq_single x₀]
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  · intro x _ hx
    rw [siteOsc_eq_zero_of_localAtSite hf hx]
    simp
  · intro hx₀
    exact absurd (Finset.mem_univ x₀) hx₀

/-- **The uniform Dobrushin locality bound for a single-site observable** (GJ §17.1): the
boundary-condition difference is bounded uniformly in `Λ`, `S`, `η`, `η'` by `siteOsc x₀ f` times
the total-influence factor `(1 − α)⁻¹` (`α = Δ(G)·tanh(βJ)` the Dobrushin coefficient). -/
theorem gibbsExpectationBC_localObs_dist_le_totalInfluence {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hΔ : β * J * G.maxDegree < 1) (h : ℝ) (Λ S : Finset ι) {η η' : Config ι}
    (hagree : agreesOff S η η') {x₀ : ι} {f : Config ι → ℝ} (hf : LocalAtSite x₀ f) :
    |gibbsExpectationBC G β (fun _ => J) h Λ η f - gibbsExpectationBC G β (fun _ => J) h Λ η' f|
      ≤ siteOsc x₀ f * (1 - isingDobrushinCoeff G β J)⁻¹ := by
  refine (gibbsExpectationBC_localObs_dist_le_resolvent_row G hβJ hΔ h Λ S hagree hf).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (siteOsc_nonneg x₀ f)
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun y _ _ => dobrushinResolvent_nonneg G hβJ x₀ y)) ?_
  rw [dobrushinResolvent_rowSum G hβJ hΔ x₀]
  exact isingTotalInfluence_le G hβJ hΔ x₀

end Dobrushin

end IsingModel
