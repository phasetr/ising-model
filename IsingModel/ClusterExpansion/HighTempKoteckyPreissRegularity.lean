import IsingModel.ClusterExpansion.HighTempKoteckyPreiss
import IsingModel.ClusterExpansion.MayerCore.CubicMayerCouplingDirectionAnalyticity

/-!
# High-temperature Kotecký–Preiss discharge for the §18.6 regularity and coupling capstones

Completes the unconditional-in-the-KP-region story of §18.6 begun in `HighTempKoteckyPreiss.lean`.
That file discharged the two Kotecký–Preiss tail conditions from the single threshold
`r = Δ²e|t| < 1/6` (`kp_tail_conditions_of_lt`) and applied it to the §18.5 Mayer-series
convergence and the §18.6 free-energy *analyticity* (pointwise + interval + unit coupling). Here the
same discharge is applied to the remaining KP-conditional §18.6 capstones, all in terms of the two
thresholds `(2d)^2 e R < 1/6` and `(2d)^2 e T < 1/6`:

* the **β-direction regularity** corollaries of the interval analyticity — continuity, `C^n`
  smoothness, real-analyticity of the internal energy density `∂_β f` and of the specific heat
  `∂_β² f` (no singularity / no phase transition in the high-temperature interval);
* the **coupling-direction (`J`)** analyticity family — GJ §18.6 is literally about analyticity in
  the coupling — pointwise, on the whole coupling interval, with continuity, `C^n` smoothness, and
  real-analyticity of the bond energy density `∂_J f`.

Each result is a mechanical wrapper: discharge the KP pair via `kp_tail_conditions_of_lt` and feed
it to the corresponding conditional theorem. Together with `HighTempKoteckyPreiss.lean` this removes
the explicit `hkp`/`hρ` hypotheses from every public §18.6 high-temperature analyticity/regularity
statement.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.6, pp. 335–340.
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §5.4 (Theorem 5.4, Kotecký–Preiss).
-/

namespace IsingModel

open Finset Filter Topology Ambient

/-- **§18.6 free-energy continuity at high temperature** (unconditional in the KP region): the
infinite-volume free-energy density is continuous on the high-temperature interval
`β ∈ (0, artanh T / J)`, under the two thresholds `(2d)^2 e R < 1/6`, `(2d)^2 e T < 1/6`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_continuousOn_high_temp_of_activity
    (d : ℕ) {R T J : ℝ} (hJ : 0 < J) (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T < 1)
    (hkpR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1 / 6)
    (hkpT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1 / 6) :
    ContinuousOn (fun β' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ))
      (Set.Ioo 0 (Real.artanh T / J)) :=
  let ⟨hkp2dR, hρ2dR⟩ := kp_tail_conditions_of_lt hkpR
  let ⟨hkp2dT, hρ2dT⟩ := kp_tail_conditions_of_lt hkpT
  freeEnergyInfinite_latticeGraph_cubicExhaustion_continuousOn_high_temp
    d hJ hR hT hTR hT1 hkp2dR hρ2dR hkp2dT hρ2dT

/-- **§18.6 free-energy `C^n` smoothness at high temperature** (unconditional in the KP region): the
infinite-volume free-energy density is `C^n` on the high-temperature interval, for every `n`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_contDiffOn_high_temp_of_activity
    (d : ℕ) {R T J : ℝ} (hJ : 0 < J) (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T < 1)
    (hkpR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1 / 6)
    (hkpT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1 / 6) {n : ℕ∞} :
    ContDiffOn ℝ n (fun β' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ))
      (Set.Ioo 0 (Real.artanh T / J)) :=
  let ⟨hkp2dR, hρ2dR⟩ := kp_tail_conditions_of_lt hkpR
  let ⟨hkp2dT, hρ2dT⟩ := kp_tail_conditions_of_lt hkpT
  freeEnergyInfinite_latticeGraph_cubicExhaustion_contDiffOn_high_temp
    d hJ hR hT hTR hT1 hkp2dR hρ2dR hkp2dT hρ2dT

/-- **§18.6 internal energy density analyticity at high temperature** (unconditional in the KP
region): the `β`-derivative of the free energy (internal energy density) is real-analytic on the
high-temperature interval. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_energyDensity_high_temp_of_activity
    (d : ℕ) {R T J : ℝ} (hJ : 0 < J) (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T < 1)
    (hkpR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1 / 6)
    (hkpT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1 / 6) :
    AnalyticOnNhd ℝ (deriv (fun β' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ)))
      (Set.Ioo 0 (Real.artanh T / J)) :=
  let ⟨hkp2dR, hρ2dR⟩ := kp_tail_conditions_of_lt hkpR
  let ⟨hkp2dT, hρ2dT⟩ := kp_tail_conditions_of_lt hkpT
  freeEnergyInfinite_latticeGraph_cubicExhaustion_energyDensity_analyticOnNhd_high_temp
    d hJ hR hT hTR hT1 hkp2dR hρ2dR hkp2dT hρ2dT

/-- **§18.6 specific heat analyticity at high temperature** (unconditional in the KP region): the
second `β`-derivative of the free energy (specific heat) is real-analytic on the high-temperature
interval — no singularity, hence no phase transition there. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_specificHeat_high_temp_of_activity
    (d : ℕ) {R T J : ℝ} (hJ : 0 < J) (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T < 1)
    (hkpR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1 / 6)
    (hkpT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1 / 6) :
    AnalyticOnNhd ℝ (deriv (deriv (fun β' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ))))
      (Set.Ioo 0 (Real.artanh T / J)) :=
  let ⟨hkp2dR, hρ2dR⟩ := kp_tail_conditions_of_lt hkpR
  let ⟨hkp2dT, hρ2dT⟩ := kp_tail_conditions_of_lt hkpT
  freeEnergyInfinite_latticeGraph_cubicExhaustion_specificHeat_analyticOnNhd_high_temp
    d hJ hR hT hTR hT1 hkp2dR hρ2dR hkp2dT hρ2dT

/-- **§18.6 coupling-direction analyticity at high temperature** (unconditional in the KP region):
the free energy at zero field is real-analytic in the **coupling** `J` near a high-temperature point
(`0 < βJ`, `tanh(βJ) < T`), under the two thresholds. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticAt_J_h_zero_of_activity
    (d : ℕ) {R T J β : ℝ} (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T ≤ 1)
    (hkpR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1 / 6)
    (hkpT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1 / 6)
    (hβJ_pos : 0 < β * J) (hβJ_tanh : Real.tanh (β * J) < T) :
    AnalyticAt ℝ (fun J' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J', 0, β⟩ : IsingParams ℝ)) J :=
  let ⟨hkp2dR, hρ2dR⟩ := kp_tail_conditions_of_lt hkpR
  let ⟨hkp2dT, hρ2dT⟩ := kp_tail_conditions_of_lt hkpT
  freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticAt_J_h_zero
    d hR hT hTR hT1 hkp2dR hρ2dR hkp2dT hρ2dT hβJ_pos hβJ_tanh

/-- **§18.6 coupling-interval analyticity at high temperature** (unconditional in the KP region):
the free energy at zero field is real-analytic in the coupling on the whole interval
`J ∈ (0, artanh T / β)` (`β > 0`), under the two thresholds. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticOnNhd_J_high_temp_of_activity
    (d : ℕ) {R T β : ℝ} (hβ : 0 < β) (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T < 1)
    (hkpR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1 / 6)
    (hkpT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1 / 6) :
    AnalyticOnNhd ℝ (fun J' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J', 0, β⟩ : IsingParams ℝ))
      (Set.Ioo 0 (Real.artanh T / β)) :=
  let ⟨hkp2dR, hρ2dR⟩ := kp_tail_conditions_of_lt hkpR
  let ⟨hkp2dT, hρ2dT⟩ := kp_tail_conditions_of_lt hkpT
  freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticOnNhd_J_high_temp
    d hβ hR hT hTR hT1 hkp2dR hρ2dR hkp2dT hρ2dT

/-- **§18.6 coupling-direction continuity at high temperature** (unconditional in the KP region):
the free energy is continuous in the coupling on `J ∈ (0, artanh T / β)`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_continuousOn_J_high_temp_of_activity
    (d : ℕ) {R T β : ℝ} (hβ : 0 < β) (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T < 1)
    (hkpR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1 / 6)
    (hkpT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1 / 6) :
    ContinuousOn (fun J' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J', 0, β⟩ : IsingParams ℝ))
      (Set.Ioo 0 (Real.artanh T / β)) :=
  let ⟨hkp2dR, hρ2dR⟩ := kp_tail_conditions_of_lt hkpR
  let ⟨hkp2dT, hρ2dT⟩ := kp_tail_conditions_of_lt hkpT
  freeEnergyInfinite_latticeGraph_cubicExhaustion_continuousOn_J_high_temp
    d hβ hR hT hTR hT1 hkp2dR hρ2dR hkp2dT hρ2dT

/-- **§18.6 coupling-direction `C^n` smoothness at high temperature** (unconditional in the KP
region): the free energy is `C^n` in the coupling on `J ∈ (0, artanh T / β)`, for every `n`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_contDiffOn_J_high_temp_of_activity
    (d : ℕ) {R T β : ℝ} (hβ : 0 < β) (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T < 1)
    (hkpR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1 / 6)
    (hkpT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1 / 6) {n : ℕ∞} :
    ContDiffOn ℝ n (fun J' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J', 0, β⟩ : IsingParams ℝ))
      (Set.Ioo 0 (Real.artanh T / β)) :=
  let ⟨hkp2dR, hρ2dR⟩ := kp_tail_conditions_of_lt hkpR
  let ⟨hkp2dT, hρ2dT⟩ := kp_tail_conditions_of_lt hkpT
  freeEnergyInfinite_latticeGraph_cubicExhaustion_contDiffOn_J_high_temp
    d hβ hR hT hTR hT1 hkp2dR hρ2dR hkp2dT hρ2dT

/-- **§18.6 bond energy density analyticity at high temperature** (unconditional in the KP region):
the coupling derivative `∂_J f` (bond energy density) is real-analytic on the coupling interval. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_couplingEnergy_J_high_temp_of_activity
    (d : ℕ) {R T β : ℝ} (hβ : 0 < β) (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T < 1)
    (hkpR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1 / 6)
    (hkpT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1 / 6) :
    AnalyticOnNhd ℝ (deriv (fun J' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J', 0, β⟩ : IsingParams ℝ)))
      (Set.Ioo 0 (Real.artanh T / β)) :=
  let ⟨hkp2dR, hρ2dR⟩ := kp_tail_conditions_of_lt hkpR
  let ⟨hkp2dT, hρ2dT⟩ := kp_tail_conditions_of_lt hkpT
  freeEnergyInfinite_latticeGraph_cubicExhaustion_couplingEnergy_analyticOnNhd_J_high_temp
    d hβ hR hT hTR hT1 hkp2dR hρ2dR hkp2dT hρ2dT

end IsingModel
