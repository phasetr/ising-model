import IsingModel.Concrete.LatticeGraphCorrelation.LocalObservableExtremalCoincidence
import IsingModel.Concrete.LatticeGraphCorrelation.CubicBoxFreeLimit

/-!
# Full-box free-boundary ∞-volume limit for a general local observable (GJ §17.1, Issue #4264)

PR 1 of Issue #4264 (`LocalObservableExtremalCoincidence.lean`) established the extremal-state
coincidence and the screened infinite-volume limit for a general `O : LocalObservable d`.  This file
closes the remaining piece — the literal **full-box free-boundary** (`Λ' = Finset.univ`, no frozen
boundary) limit — generalising `CubicBoxFreeLimit.lean` (#4263) from the single-site origin
observable to a general monotone `O`.

## Headline

`tendsto_gibbsExpectationBC_localObs_free_limit` — at high temperature, for a **monotone** `O`, the
free-boundary Gibbs expectation of `O` on the growing cubic boxes converges to the common extremal
value `plusStateExpectation J h β O hS`, for **every** boundary family `η` (the free measure being
boundary-condition-independent via `gibbsExpectationBC_boundary_congr`, `agreesOff univ` vacuous).

## Method

The same two-sided **volume-monotonicity squeeze** as #4263: at `Λ' = univ` the free measure equals
both `±` boundary measures; freezing the shell of an inner box to `+`/`−` brackets it
(`gibbsExpectationBC_{plus_volume_antitone, minus_volume_monotone}`, both already general); both
bracketing sequences are the `±` instances of the general screened limit
`tendsto_gibbsExpectationBC_localObs_extremal_limit` (#4264 PR 1), both `→` the common value.
Because the support radius `N` is symbolic the box indices already align, so no index
renormalisation is needed.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306;
Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.4 (Lemmas 3.22–3.23), §6.5;
Georgii, *Gibbs Measures and Phase Transitions*, Ch. 8.
-/

namespace IsingModel

namespace Ambient

open IsingModel.Dobrushin Finset Filter Topology

/-- **Full-box free-boundary infinite-volume limit for a general monotone local observable**
(GJ §17.1; ℤ^d Dobrushin uniqueness, Issue #4264).  For a **monotone** `O` and high temperature, the
free-boundary (`Λ' = Finset.univ`) Gibbs expectation of `O` on the growing cubic boxes converges to
the common extremal value `plusStateExpectation J h β O hS`, for every boundary family `η`.

Proof: a two-sided volume-monotonicity squeeze.  At `Λ' = univ` the free measure equals both the `+`
and `−` boundary measures (`gibbsExpectationBC_boundary_congr`, `agreesOff univ` vacuous); freezing
the shell of the inner box to `+`/`−` brackets it (`gibbsExpectationBC_{plus_volume_antitone,
minus_volume_monotone}`); both bracketing sequences are the `±` instances of the general screened
limit `tendsto_gibbsExpectationBC_localObs_extremal_limit`, both converging to
`plusStateExpectation J h β O hS`. -/
theorem tendsto_gibbsExpectationBC_localObs_free_limit (d : ℕ) (hd : 1 ≤ d) {β J : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (hα : β * J * (2 * (d : ℝ)) < 1) (h : ℝ) (O : LocalObservable d)
    (hO_mono : Monotone O.φ) {N : ℕ} (hS : O.S ⊆ cubicBox d N)
    (η : ∀ k : ℕ, Config (↑(cubicBox d (N + k + 1)) : Type _)) :
    Tendsto (fun k : ℕ =>
        gibbsExpectationBC (inducedGraph (latticeGraph d) (cubicBox d (N + k + 1))) β (fun _ => J) h
          Finset.univ (η k)
          (fun σ => O.φ (restrictConfig
            (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1))) σ)))
      atTop (𝓝 (plusStateExpectation J h β O hS)) := by
  -- Step A: at `Λ' = univ` the free measure equals the `+` and `−` boundary measures.
  have hfree_plus : ∀ k,
      gibbsExpectationBC (inducedGraph (latticeGraph d) (cubicBox d (N + k + 1))) β (fun _ => J) h
          Finset.univ (η k) (fun σ => O.φ (restrictConfig
            (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1))) σ))
        = gibbsExpectationBC (inducedGraph (latticeGraph d) (cubicBox d (N + k + 1))) β
            (fun _ => J) h Finset.univ (plusConfig _) (fun σ => O.φ (restrictConfig
              (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1))) σ)) := fun k =>
    gibbsExpectationBC_boundary_congr _ _ _ _ _ (fun i hi => absurd (Finset.mem_univ i) hi) _
  have hfree_minus : ∀ k,
      gibbsExpectationBC (inducedGraph (latticeGraph d) (cubicBox d (N + k + 1))) β (fun _ => J) h
          Finset.univ (η k) (fun σ => O.φ (restrictConfig
            (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1))) σ))
        = gibbsExpectationBC (inducedGraph (latticeGraph d) (cubicBox d (N + k + 1))) β
            (fun _ => J) h Finset.univ (minusConfig _) (fun σ => O.φ (restrictConfig
              (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1))) σ)) := fun k =>
    gibbsExpectationBC_boundary_congr _ _ _ _ _ (fun i hi => absurd (Finset.mem_univ i) hi) _
  -- Endpoints: the ± instances of the general screened limit (#4264 PR 1), both → the common value.
  have hU := tendsto_gibbsExpectationBC_localObs_extremal_limit d hd hβ hJ hα h O hO_mono hS
    (fun _ => plusConfig _)
  have hLo := tendsto_gibbsExpectationBC_localObs_extremal_limit d hd hβ hJ hα h O hO_mono hS
    (fun _ => minusConfig _)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hLo hU (fun k => ?_) (fun k => ?_)
  · rw [hfree_minus k]
    exact gibbsExpectationBC_minus_volume_monotone
      (inducedGraph (latticeGraph d) (cubicBox d (N + k + 1)))
      hβ (fun _ => hJ) (Finset.subset_univ (plusBoxInterior d (N + k) (N + k + 1)))
      (fun σ => O.φ (restrictConfig (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1))) σ))
      (hO_mono.comp (restrictConfig_monotone
        (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1)))))
  · rw [hfree_plus k]
    exact gibbsExpectationBC_plus_volume_antitone
      (inducedGraph (latticeGraph d) (cubicBox d (N + k + 1)))
      hβ (fun _ => hJ) (Finset.subset_univ (plusBoxInterior d (N + k) (N + k + 1)))
      (fun σ => O.φ (restrictConfig (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1))) σ))
      (hO_mono.comp (restrictConfig_monotone
        (hS.trans (cubicBox_mono d (by omega : N ≤ N + k + 1)))))

end Ambient

end IsingModel
