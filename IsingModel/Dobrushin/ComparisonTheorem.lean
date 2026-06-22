import IsingModel.Dobrushin.SweepContraction
import IsingModel.Dobrushin.GibbsBoundaryComparison

/-!
# The single-site Dobrushin comparison theorem (GJ §17.1, Issue #4214 §A capstone)

The capstone of the GJ §17.1 single-site Dobrushin comparison programme. Under the high-temperature
condition `βJ·Δ(G) < 1` (whence the Dobrushin coefficient `tanh(βJ)·Δ(G) < 1`), two finite-volume
Gibbs expectations under boundary conditions `η, η'` agreeing off a set `S` differ by at most the
resolvent-weighted oscillations of `f`,
\[
  |⟨f⟩^η_Λ − ⟨f⟩^{η'}_Λ|
    ≤ ∑_{x} \mathrm{siteOsc}_x(f)·w_x
    = ∑_{x}∑_{y∈S} R_{xy}·\mathrm{siteOsc}_x(f),
\]
where `R = (I − C)⁻¹` is the Dobrushin resolvent of the single-site influence matrix
`C_{xy} = tanh(βJ)·[y∼x]` and `w_x = ∑_{y∈S} R_{xy}` is the boundary weight.

The proof composes the merged ingredients: heat-bath sweep invariance leaves the expectation
unchanged, so `⟨f⟩ = ⟨g_n⟩` for `g_n = sweep^n f`; the full-volume Gibbs comparison
(support-diameter) bounds `|⟨g_n⟩^η − ⟨g_n⟩^{η'}|` by an interior sum over `Λ` plus a boundary sum
over `S`; the oscillation-tracking estimate dominates both by the oscillation-vector dynamics; the
boundary-sum Lyapunov bound caps the boundary part by `∑_x siteOsc x f·w_x`; and the interior part
vanishes in the sweep limit (`αⁿ → 0`). Passing `n → ∞` discharges the interior term.

* `gibbsExpectationBC_dist_le_dobrushinBoundaryWeight` — the comparison in boundary-weight form.
* `gibbsExpectationBC_dist_le_resolvent_sum` — the comparison in the resolvent double-sum form
  `∑_x ∑_{y∈S} R_{xy}·siteOsc x f`.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306; Georgii,
*Gibbs Measures and Phase Transitions*, Ch. 8.
-/

namespace IsingModel

namespace Dobrushin

open Finset Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (G : SimpleGraph ι) [Fintype G.edgeSet] [DecidableRel G.Adj]

/-- **The single-site Dobrushin comparison theorem** (GJ §17.1, capstone of Issue #4214 §A): under
the high-temperature condition `βJ·Δ(G) < 1` (whence the Dobrushin coefficient `tanh(βJ)·Δ(G) < 1`),
the Gibbs expectations under boundary conditions agreeing off `S` differ by at most
`∑_x siteOsc x f · w_x`, with `w_x = ∑_{y∈S} R_{xy}` the resolvent boundary weight. -/
theorem gibbsExpectationBC_dist_le_dobrushinBoundaryWeight {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hΔ : β * J * G.maxDegree < 1) (h : ℝ) (Λ S : Finset ι) {η η' : Config ι}
    (hagree : agreesOff S η η') (f : Config ι → ℝ) :
    |gibbsExpectationBC G β (fun _ => J) h Λ η f - gibbsExpectationBC G β (fun _ => J) h Λ η' f|
      ≤ ∑ x, siteOsc x f * dobrushinBoundaryWeight G β J S x := by
  classical
  set B := ∑ x, siteOsc x f * dobrushinBoundaryWeight G β J S x with hB
  set A := |gibbsExpectationBC G β (fun _ => J) h Λ η f
    - gibbsExpectationBC G β (fun _ => J) h Λ η' f| with hA
  have hα1 : isingDobrushinCoeff G β J < 1 := isingDobrushinCoeff_lt_one_of_high_temp G hβJ hΔ
  have hvnn : ∀ z, (0 : ℝ) ≤ siteOsc z f := fun z => siteOsc_nonneg z f
  -- per-sweep bound: `A ≤ interior_n + B`
  have hper : ∀ n, A ≤ (∑ x ∈ Λ, heatBathListOscBound G β J (repeatedFullSweep Λ n)
      (fun z => siteOsc z f) x) + B := by
    intro n
    have hsub := repeatedFullSweep_subset Λ n
    have hinvη :=
      gibbsExpectationBC_heatBathList_invariant G β J h η (repeatedFullSweep Λ n) f hsub
    have hinvη' :=
      gibbsExpectationBC_heatBathList_invariant G β J h η' (repeatedFullSweep Λ n) f hsub
    have hAeq : A = |gibbsExpectationBC G β (fun _ => J) h Λ η
          (heatBathList G β J h (repeatedFullSweep Λ n) f)
        - gibbsExpectationBC G β (fun _ => J) h Λ η'
          (heatBathList G β J h (repeatedFullSweep Λ n) f)| := by
      rw [hA, hinvη, hinvη']
    rw [hAeq]
    refine (gibbsExpectationBC_dist_le_volume_add_boundary_siteOsc G β (fun _ => J) h Λ S
      (heatBathList G β J h (repeatedFullSweep Λ n) f) hagree).trans ?_
    have hi : ∑ x ∈ Λ, siteOsc x (heatBathList G β J h (repeatedFullSweep Λ n) f)
        ≤ ∑ x ∈ Λ, heatBathListOscBound G β J (repeatedFullSweep Λ n) (fun z => siteOsc z f) x :=
      Finset.sum_le_sum fun x _ =>
        siteOsc_heatBathList_le_oscBound G hβJ h (repeatedFullSweep Λ n) f x
    have hbd : ∑ y ∈ S, siteOsc y (heatBathList G β J h (repeatedFullSweep Λ n) f) ≤ B := by
      refine le_trans (Finset.sum_le_sum fun y _ =>
        siteOsc_heatBathList_le_oscBound G hβJ h (repeatedFullSweep Λ n) f y) ?_
      exact heatBathListOscBound_boundary_sum_le_boundaryWeight G hβJ hΔ S
        (repeatedFullSweep Λ n) hvnn
    linarith [hi, hbd]
  -- the interior term tends to `0`, so `A ≤ B`
  have htend : Filter.Tendsto (fun n => (∑ x ∈ Λ, heatBathListOscBound G β J
        (repeatedFullSweep Λ n) (fun z => siteOsc z f) x) + B) Filter.atTop (nhds (0 + B)) :=
    (interiorMass_repeatedFullSweep_tendsto_zero G hβJ hα1 Λ hvnn).add_const B
  rw [zero_add] at htend
  exact ge_of_tendsto' htend hper

/-- **The single-site Dobrushin comparison theorem, resolvent form** (GJ §17.1): the same
comparison, written with the resolvent double sum `∑_x ∑_{y∈S} R_{xy}·siteOsc x f` — the literal
comparison inequality `|⟨f⟩_η − ⟨f⟩_{η'}| ≤ ∑_{x,y} R_{xy}·osc_x(f)·[η,η' differ at y]`. -/
theorem gibbsExpectationBC_dist_le_resolvent_sum {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hΔ : β * J * G.maxDegree < 1) (h : ℝ) (Λ S : Finset ι) {η η' : Config ι}
    (hagree : agreesOff S η η') (f : Config ι → ℝ) :
    |gibbsExpectationBC G β (fun _ => J) h Λ η f - gibbsExpectationBC G β (fun _ => J) h Λ η' f|
      ≤ ∑ x, ∑ y ∈ S, dobrushinResolvent G β J x y * siteOsc x f := by
  refine (gibbsExpectationBC_dist_le_dobrushinBoundaryWeight G hβJ hΔ h Λ S hagree f).trans
    (le_of_eq ?_)
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [dobrushinBoundaryWeight, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

end Dobrushin

end IsingModel
