import IsingModel.ClusterExpansion.HighTempAnalyticityCapstone
import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1.HighTempMassGap

/-!
# The §18 cluster-expansion route supersedes the transfer-matrix infinite-volume gap

Glimm–Jaffe §17.1 sets up the transfer-matrix method for the Ising model.  A natural
infinite-volume programme built on it would prove a **transverse-volume-uniform**
high-temperature bound on the subdominant spectral ratio `θ(βJ) < 1` of the interacting
cubic layer — a uniform spectral gap from which exponential correlation decay and
free-energy regularity would follow in the thermodynamic limit.

That route is **obstructed**.  The single-step Dobrushin/Doeblin contraction is provably
insufficient for the growing transverse box, and a Codex counterexample
(`u ≡ 1`, `k = exp(t·∑ a·b)`, `ρ ~ exp(O(|S|))`) shows the uniform Kotecký–Preiss /
Dobrushin estimate one would need cannot hold transversally uniformly; see the roadmap
`.self-local/docs/11-roadmap-to-completion-2026-06-20.md`, Phase 5, and the documented
obstruction in `IsingModel/TransferMatrix/Layer*` (`LayerDobrushinContraction.lean`,
`LayerDoeblin.lean`, `LayerDoobSpectralGap.lean`, …).

This module records the **resolution** prescribed by Issue #4214 item B, option (ii):
the §18 *cluster-expansion* route already delivers, **unconditionally**, the
infinite-volume high-temperature conclusions the transfer-matrix gap programme aimed at:

* **No phase transition** — the infinite-volume `ℤ^d` Ising free energy and its
  thermodynamic derivatives (internal energy `∂_β f`, specific heat `∂_β² f`) are
  real-analytic on a high-temperature interval `(0, β₀)`
  (`exists_high_temp_no_phase_transition`, GJ §18.6, Kotecký–Preiss discharged from
  `Δ²e|t| < 1/6`);
* **Mass gap** — the infinite-volume truncated two-point function decays exponentially,
  with a positive rate, throughout the same interval
  (`hasExponentialDecay_latticeGraph_of_betaJ_two_d_lt_one`, GJ §18.7, Simon–Lieb route).

The headline `clusterExpansion_supersedes_transferMatrix_gap` bundles both on a single
common interval `(0, β₀)`, making explicit that the cluster-expansion route **supersedes**
the obstructed transfer-matrix transverse-uniform spectral gap: every infinite-volume
high-temperature payoff the gap aimed at is already available, with no spectral-gap
hypothesis and no remaining documented obstruction.

## Main results
* `clusterExpansion_supersedes_transferMatrix_gap` — `∃ β₀ > 0` on which both the
  free-energy analyticity (no phase transition) **and** the two-point exponential decay
  (mass gap) hold for the infinite-volume `ℤ^d` Ising model.

## References
* Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1 (transfer matrix),
  §18.5–18.6 (cluster expansion, analyticity), §18.7 (correlation decay).
* Issue #4214, item B (and the documented obstruction of option (i)).
-/

namespace IsingModel

open Set

/-- **The §18 cluster-expansion route supersedes the transfer-matrix infinite-volume
spectral gap** (Glimm–Jaffe §17.1 vs §18.6/§18.7; Issue #4214 item B, option (ii)).

For every dimension `d ≥ 1` and coupling `J > 0`, there is a single high-temperature
threshold `β₀ > 0` on which the *infinite-volume* `ℤ^d` Ising model simultaneously
exhibits, via the cluster expansion:

* **No phase transition** — the free energy `f`, its internal energy density `∂_β f`, and
  its specific heat `∂_β² f` are all real-analytic on `(0, β₀)`; and
* **A mass gap** — for every `β ∈ (0, β₀)` the truncated two-point function decays
  exponentially with a strictly positive rate `−log(βJ·2d)`.

These are exactly the infinite-volume high-temperature conclusions that a
transverse-volume-uniform transfer-matrix spectral gap would have produced.  Since that
gap route is the documented obstruction of option (i), this bundling is the formal record
that the §18 route supersedes it: the obstruction is no longer an obstacle to the
infinite-volume high-temperature theory.

The common threshold is `β₀ = min β₁ (1/(J·2d))`, where `β₁` is the analyticity radius of
`exists_high_temp_no_phase_transition`; the analyticity transfers to the smaller interval
by `AnalyticOnNhd.mono`, while `β < 1/(J·2d)` is exactly the elementary high-temperature
condition `βJ·2d < 1` feeding the Simon–Lieb exponential decay. -/
theorem clusterExpansion_supersedes_transferMatrix_gap
    (d : ℕ) (hd : 1 ≤ d) {J : ℝ} (hJ : 0 < J) :
    ∃ β₀ : ℝ, 0 < β₀ ∧
      -- (a) no phase transition: free energy and its β-derivatives are analytic
      AnalyticOnNhd ℝ (fun β' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ)) (Set.Ioo 0 β₀) ∧
      AnalyticOnNhd ℝ (deriv (fun β' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ))) (Set.Ioo 0 β₀) ∧
      AnalyticOnNhd ℝ (deriv (deriv (fun β' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ)))) (Set.Ioo 0 β₀) ∧
      -- (b) mass gap: exponential two-point decay throughout the same interval
      (∀ β : ℝ, β ∈ Set.Ioo (0 : ℝ) β₀ →
        0 < -Real.log (β * J * (2 * d)) ∧
          Ambient.HasExponentialDecay d (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) (-Real.log (β * J * (2 * d)))) := by
  obtain ⟨β₁, hβ₁_pos, hf, hdf, hd2f⟩ := exists_high_temp_no_phase_transition d hJ
  -- elementary high-temperature radius for the Simon–Lieb decay: `β < 1/(J·2d)`
  have hJ2d_pos : 0 < J * (2 * d) := mul_pos hJ (by positivity)
  set β₀ : ℝ := min β₁ (1 / (J * (2 * d))) with hβ₀
  have hβ₀_pos : 0 < β₀ := lt_min hβ₁_pos (by positivity)
  have hsub : Set.Ioo (0 : ℝ) β₀ ⊆ Set.Ioo (0 : ℝ) β₁ :=
    Set.Ioo_subset_Ioo_right (min_le_left _ _)
  refine ⟨β₀, hβ₀_pos, hf.mono hsub, hdf.mono hsub, hd2f.mono hsub, ?_⟩
  intro β hβ
  obtain ⟨hβ_pos, hβ_lt⟩ := hβ
  -- `β < β₀ ≤ 1/(J·2d)` gives `β·J·2d < 1`
  have hβ_lt_inv : β < 1 / (J * (2 * d)) := lt_of_lt_of_le hβ_lt (min_le_right _ _)
  have hht : β * J * (2 * d) < 1 := by
    have h := (lt_div_iff₀ hJ2d_pos).mp hβ_lt_inv
    calc β * J * (2 * d) = β * (J * (2 * d)) := by ring
      _ < 1 := by simpa using h
  exact Ambient.hasExponentialDecay_latticeGraph_of_betaJ_two_d_lt_one d hd hJ hβ_pos hht

end IsingModel
