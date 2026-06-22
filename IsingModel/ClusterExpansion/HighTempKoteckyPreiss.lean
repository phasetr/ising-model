import IsingModel.ClusterExpansion.MayerSeriesConvergence
import IsingModel.ClusterExpansion.MayerTsumPerSite
import IsingModel.ClusterExpansion.MayerTsumPerSiteAmbient
import IsingModel.ClusterExpansion.MayerCore.CubicMayerCouplingAnalyticity
import IsingModel.ClusterExpansion.MayerCore.CubicMayerHighTempIntervalAnalyticity

/-!
# Discharging the Kotecký–Preiss conditions at high temperature (GJ §18.5–§18.6)

The Mayer-series convergence and free-energy analyticity results of §18.5–§18.6 are stated under the
two Kotecký–Preiss tail conditions
\[
  \text{(hkp)}\quad Δ^2\,e\,|t| < 1,
  \qquad
  \text{(hρ)}\quad \frac{4\,Δ^2 e |t|}{(1 − Δ^2 e |t|)^2} < 1,
\]
where `Δ = G.maxDegree`, `t` is the polymer activity, and `e = exp 1`. This file discharges both
from a single, clean **high-temperature threshold**: writing `r = Δ^2 e |t|`,
\[
  r < \tfrac{1}{6} \;\Longrightarrow\; \text{(hkp)} \wedge \text{(hρ)}.
\]
Indeed `r < 1/6 < 1` gives (hkp), and `4r/(1−r)^2 < 1 ⟺ 4r < (1−r)^2 ⟺ 0 < (1 − 6r) + r^2`, which
holds since `1 − 6r > 0` and `r^2 ≥ 0`. (The threshold `1/6 ≈ 0.1667` is a clean sufficient bound,
just below the tight value `3 − 2√2 ≈ 0.1716`, and avoids `√2`.) Feeding this into the conditional
theorems makes the §18.5 Mayer-series convergence, the per-site bound, and the §18.6 cubic
free-energy analyticity hold under the single explicit high-temperature smallness condition.

* `kp_tail_conditions_of_lt` — the abstract discharge `r < 1/6 → r < 1 ∧ 4r/(1−r)^2 < 1`.
* `kp_tail_conditions_of_activity_lt` — the graph-level discharge from `Δ^2 e |t| < 1/6`.
* `summable_mayerExpansionTerm_of_activity_lt`, `tendsto_mayerPartialSum_of_activity_lt` — §18.5
  Mayer-series convergence under the single threshold.
* `tsum_abs_mayerExpansionTerm_succ_div_card_le_of_activity_lt` — the per-site Mayer bound.
* `latticeGraph_kp_tsum_per_site_of_activity_lt`,
  `latticeGraph_kp_tsum_per_site_cubicExhaustion_of_activity_lt` — the ℤ^d cubic per-site bound from
  `(2d)^2 e |t| < 1/6`.
* `freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticAt_beta_h_zero_of_activity` — the §18.6
  pointwise cubic free-energy analyticity from the two thresholds `(2d)^2 e R < 1/6`,
  `(2d)^2 e T < 1/6`.
* `freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticOnNhd_high_temp_of_activity`,
  `…_analyticOnNhd_unitCoupling_of_activity` — the §18.6 free-energy analyticity on the whole
  high-temperature interval from the same two thresholds.

The derived-regularity corollaries of the interval statement (continuity, `contDiffOn`, energy
density, specific heat) and the coupling-direction analyticity still expose the KP pair and are left
to a follow-up; each is a mechanical wrapper of the analyticity statements discharged here.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4–§18.6, pp. 332–340.
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §5.4 (Theorem 5.4, Kotecký–Preiss).
-/

namespace IsingModel

open Finset Filter Topology Ambient

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Abstract Kotecký–Preiss discharge**: the single smallness `r < 1/6` implies both KP tail
conditions `r < 1` and `4r/(1−r)^2 < 1`. (For `r < 1/6` one has `1 − r > 0`, and
`4r < (1−r)^2 ⟺ 0 < (1 − 6r) + r^2`, true since `1 − 6r > 0` and `r^2 ≥ 0`.) -/
theorem kp_tail_conditions_of_lt {r : ℝ} (hr : r < 1 / 6) :
    r < 1 ∧ 4 * r / (1 - r) ^ 2 < 1 := by
  refine ⟨by linarith, ?_⟩
  have h1r : 0 < 1 - r := by linarith
  rw [div_lt_one (pow_pos h1r 2)]
  nlinarith [sq_nonneg r]

omit [DecidableEq ι] in
/-- **Graph-level Kotecký–Preiss discharge at high temperature**: for a graph `G` and activity `t`,
the threshold `Δ^2 e |t| < 1/6` (`Δ = G.maxDegree`) yields both KP tail conditions. -/
theorem kp_tail_conditions_of_activity_lt (G : SimpleGraph ι) [DecidableRel G.Adj] {t : ℝ}
    (ht : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1 / 6) :
    ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) ∧
      4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
          / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2 < 1 :=
  kp_tail_conditions_of_lt ht

/-- **§18.5 Mayer-series summability at high temperature** (unconditional in the KP region): under
the single threshold `Δ^2 e |t| < 1/6`, the Mayer expansion terms are summable. -/
theorem summable_mayerExpansionTerm_of_activity_lt (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] {t : ℝ}
    (ht : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1 / 6) :
    Summable fun n : ℕ => mayerExpansionTerm G n t :=
  let ⟨hkp, hρ⟩ := kp_tail_conditions_of_activity_lt G ht
  summable_mayerExpansionTerm_of_tail_condition G hkp hρ

/-- **§18.5 Mayer-partial-sum convergence at high temperature**: under `Δ^2 e |t| < 1/6`, the Mayer
partial sums converge to the Mayer series `∑'_n mayerExpansionTerm G n t`. -/
theorem tendsto_mayerPartialSum_of_activity_lt (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] {t : ℝ}
    (ht : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1 / 6) :
    Tendsto (fun N => mayerPartialSum G N t) atTop (𝓝 (∑' n, mayerExpansionTerm G n t)) :=
  let ⟨hkp, hρ⟩ := kp_tail_conditions_of_activity_lt G ht
  tendsto_mayerPartialSum_of_tail_condition G hkp hρ

/-- **Per-site Mayer bound at high temperature**: under `Δ^2 e |t| < 1/6`, the per-site tail
`(∑'_n |mayerExpansionTerm G (n+1) t|)/|ι|` is bounded by the explicit KP constant. -/
theorem tsum_abs_mayerExpansionTerm_succ_div_card_le_of_activity_lt (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] [Nonempty ι] {t : ℝ}
    (ht : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1 / 6) :
    (∑' n : ℕ, |mayerExpansionTerm G (n + 1) t|) / (Fintype.card ι : ℝ)
      ≤ ((1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
          * (1 - 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
                / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2))⁻¹ :=
  let ⟨hkp, hρ⟩ := kp_tail_conditions_of_activity_lt G ht
  tsum_abs_mayerExpansionTerm_succ_div_card_le G hkp hρ

/-- **ℤ^d cubic per-site Mayer bound at high temperature**: under `(2d)^2 e |t| < 1/6`, the per-site
Mayer tail on the induced lattice graph of a box `Λ` is bounded by `kpBound (2d) t`. -/
theorem latticeGraph_kp_tsum_per_site_of_activity_lt (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)] {t : ℝ}
    (ht : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1 / 6) :
    (∑' n : ℕ,
          |mayerExpansionTerm (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) (n + 1) t|)
        / (Fintype.card (↑Λ : Type _) : ℝ)
      ≤ kpBound (2 * d) t :=
  let ⟨hkp, hρ⟩ := kp_tail_conditions_of_lt ht
  latticeGraph_kp_tsum_per_site_le d Λ hkp hρ

/-- **ℤ^d cubic-exhaustion per-site Mayer bound at high temperature**: the per-site bound
`kpBound (2d) t` uniform over all stages of the cubic exhaustion, under `(2d)^2 e |t| < 1/6`. -/
theorem latticeGraph_kp_tsum_per_site_cubicExhaustion_of_activity_lt (d : ℕ) (n : ℕ)
    [Nonempty (↑((Ambient.cubicExhaustion d).volume n) : Type _)] {t : ℝ}
    (ht : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1 / 6) :
    (∑' k : ℕ, |mayerExpansionTerm
          (Ambient.inducedGraph (IsingModel.latticeGraph d)
            ((Ambient.cubicExhaustion d).volume n)) (k + 1) t|)
        / (Fintype.card (↑((Ambient.cubicExhaustion d).volume n) : Type _) : ℝ)
      ≤ kpBound (2 * d) t :=
  let ⟨hkp, hρ⟩ := kp_tail_conditions_of_lt ht
  latticeGraph_kp_tsum_per_site_cubicExhaustion_le d n hkp hρ

/-- **§18.6 cubic free-energy analyticity at high temperature** (unconditional in the KP region):
the infinite-volume free energy of the ℤ^d Ising model along the cubic exhaustion is analytic in
`β'` near `β` at zero field, under the geometric hypotheses on the radii `R, T` and the two
high-temperature thresholds `(2d)^2 e R < 1/6` and `(2d)^2 e T < 1/6`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticAt_beta_h_zero_of_activity
    (d : ℕ) {R T J β : ℝ} (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T ≤ 1)
    (hkpR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1 / 6)
    (hkpT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1 / 6)
    (hβJ_pos : 0 < β * J) (hβJ_tanh : Real.tanh (β * J) < T) :
    AnalyticAt ℝ (fun β' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ)) β :=
  let ⟨hkp2dR, hρ2dR⟩ := kp_tail_conditions_of_lt hkpR
  let ⟨hkp2dT, hρ2dT⟩ := kp_tail_conditions_of_lt hkpT
  freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticAt_beta_h_zero
    d hR hT hTR hT1 hkp2dR hρ2dR hkp2dT hρ2dT hβJ_pos hβJ_tanh

/-- **§18.6 cubic free-energy interval analyticity at high temperature** (unconditional in the KP
region): the infinite-volume free-energy density at zero field is real-analytic on the
high-temperature interval `β ∈ (0, artanh T / J)`, under the two thresholds `(2d)^2 e R < 1/6`,
`(2d)^2 e T < 1/6`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticOnNhd_high_temp_of_activity
    (d : ℕ) {R T J : ℝ} (hJ : 0 < J) (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T < 1)
    (hkpR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1 / 6)
    (hkpT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1 / 6) :
    AnalyticOnNhd ℝ (fun β' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ))
      (Set.Ioo 0 (Real.artanh T / J)) :=
  let ⟨hkp2dR, hρ2dR⟩ := kp_tail_conditions_of_lt hkpR
  let ⟨hkp2dT, hρ2dT⟩ := kp_tail_conditions_of_lt hkpT
  freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticOnNhd_high_temp
    d hJ hR hT hTR hT1 hkp2dR hρ2dR hkp2dT hρ2dT

/-- **§18.6 interval analyticity at unit coupling, high temperature** (unconditional in the KP
region): the `J = 1` case, real-analytic on `β ∈ (0, artanh T)`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticOnNhd_unitCoupling_of_activity
    (d : ℕ) {R T : ℝ} (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T < 1)
    (hkpR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1 / 6)
    (hkpT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1 / 6) :
    AnalyticOnNhd ℝ (fun β' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨1, 0, β'⟩ : IsingParams ℝ))
      (Set.Ioo 0 (Real.artanh T)) :=
  let ⟨hkp2dR, hρ2dR⟩ := kp_tail_conditions_of_lt hkpR
  let ⟨hkp2dT, hρ2dT⟩ := kp_tail_conditions_of_lt hkpT
  freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticOnNhd_unitCoupling
    d hR hT hTR hT1 hkp2dR hρ2dR hkp2dT hρ2dT

end IsingModel
