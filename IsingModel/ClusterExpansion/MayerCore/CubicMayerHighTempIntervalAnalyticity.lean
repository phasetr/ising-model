import IsingModel.ClusterExpansion.MayerCore.CubicMayerCouplingAnalyticity

/-!
# High-temperature interval analyticity and absence of phase transition (GJ §18.6)

The §18.6 capstone `freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticAt_beta_h_zero` proves
the infinite-volume cubic-Ising free-energy density is real-analytic **at a single point** `β` with
`tanh (β J) < T`. This file upgrades that to analyticity on the **whole high-temperature interval**
and reads off the physical consequence: the infinite-volume thermodynamic functions (free energy,
internal energy density, specific heat) are real-analytic throughout the high-temperature phase, so
the model has **no phase transition** there.

For fixed Kotecký–Preiss parameters `T, R` (with the convergence conditions on `2d·e·T` and
`2d·e·R`) and coupling `J > 0`, the condition `tanh (β J) < T` is `β J < artanh T`, i.e. the
open interval `β ∈ (0, artanh T / J)`. As `tanh` is strictly monotone with `tanh (artanh T) = T`,
the single-point capstone applies at every interior point, giving `AnalyticOnNhd` on that interval.
The thermodynamic-derivative consequences follow from the analytic calculus (`AnalyticOnNhd.deriv`,
`_.contDiffOn_of_completeSpace`, `_.continuousOn`).

* `..._analyticOnNhd_high_temp` — interval analyticity (general `J`).
* `..._analyticOnNhd_unitCoupling` — the `J = 1` specialisation.
* `..._continuousOn_high_temp` / `..._contDiffOn_high_temp` — continuity and `C^∞` smoothness
  (no singularity in the high-temperature phase).
* `..._energyDensity_analyticOnNhd_high_temp` — the internal energy density `∂f/∂β` is
  real-analytic on the interval.
* `..._specificHeat_analyticOnNhd_high_temp` — specific heat `∂²f/∂β²` analytic.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §18.6.
-/

namespace IsingModel

open Ambient Set Filter Topology

/-- `Real.tanh` is strictly monotone (local copy; the global version lives in `PseudoMass/Profile`,
which is not on this import path). Proved from `sinh (y − x) > 0` for `x < y`. -/
private theorem real_tanh_strictMono : StrictMono Real.tanh := by
  intro x y hxy
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
  have hcx : 0 < Real.cosh x := Real.cosh_pos _
  have hcy : 0 < Real.cosh y := Real.cosh_pos _
  rw [div_lt_div_iff₀ hcx hcy]
  have hsub_pos : 0 < Real.sinh (y - x) := Real.sinh_pos_iff.mpr (sub_pos.mpr hxy)
  have heq : Real.sinh (y - x) =
      Real.sinh y * Real.cosh x - Real.cosh y * Real.sinh x := Real.sinh_sub y x
  linarith

/-- **High-temperature interval analyticity** (GJ §18.6): for `J > 0` and KP parameters
`T, R` satisfying the convergence conditions, the infinite-volume cubic-Ising free-energy density at
zero field is real-analytic on the whole high-temperature interval `β ∈ (0, artanh T / J)`. The
single-point capstone applies at every point because `β < artanh T / J` is exactly
`tanh (β J) < T`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticOnNhd_high_temp
    (d : ℕ) {R T J : ℝ} (hJ : 0 < J)
    (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T < 1)
    (hkp2dR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρ2dR : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1)
    (hkp2dT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1)
    (hρ2dT : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T)) ^ 2 < 1) :
    AnalyticOnNhd ℝ (fun β' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ))
      (Set.Ioo 0 (Real.artanh T / J)) := by
  intro β hβ
  obtain ⟨hβ0, hβlt⟩ := hβ
  have hT_mem : T ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hT1⟩
  have hβJ_pos : 0 < β * J := mul_pos hβ0 hJ
  have hβJ_tanh : Real.tanh (β * J) < T := by
    have hlt : β * J < Real.artanh T := (lt_div_iff₀ hJ).mp hβlt
    calc Real.tanh (β * J) < Real.tanh (Real.artanh T) := real_tanh_strictMono hlt
      _ = T := Real.tanh_artanh hT_mem
  exact freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticAt_beta_h_zero d hR hT hTR
    (le_of_lt hT1) hkp2dR hρ2dR hkp2dT hρ2dT hβJ_pos hβJ_tanh

/-- **Interval analyticity, unit coupling (`J = 1`)** (GJ §18.6): the infinite-volume
cubic-Ising free-energy density at zero field and unit coupling is real-analytic on the
high-temperature interval `β ∈ (0, artanh T)`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticOnNhd_unitCoupling
    (d : ℕ) {R T : ℝ}
    (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T < 1)
    (hkp2dR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρ2dR : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1)
    (hkp2dT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1)
    (hρ2dT : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T)) ^ 2 < 1) :
    AnalyticOnNhd ℝ (fun β' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨1, 0, β'⟩ : IsingParams ℝ))
      (Set.Ioo 0 (Real.artanh T)) := by
  have h := freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticOnNhd_high_temp d
    (one_pos) hR hT hTR hT1 hkp2dR hρ2dR hkp2dT hρ2dT
  rwa [div_one] at h

/-- **No singularity in the high-temperature phase — continuity** (GJ §18.6): the infinite-volume
free-energy density is continuous on the high-temperature interval. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_continuousOn_high_temp
    (d : ℕ) {R T J : ℝ} (hJ : 0 < J)
    (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T < 1)
    (hkp2dR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρ2dR : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1)
    (hkp2dT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1)
    (hρ2dT : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T)) ^ 2 < 1) :
    ContinuousOn (fun β' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ))
      (Set.Ioo 0 (Real.artanh T / J)) :=
  (freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticOnNhd_high_temp d hJ hR hT hTR hT1
    hkp2dR hρ2dR hkp2dT hρ2dT).continuousOn

/-- **No phase transition in the high-temperature phase — `C^∞` smoothness** (GJ §18.6): the
infinite-volume free-energy density is `C^∞` (indeed `C^ω`) on the high-temperature interval,
has no singularity there. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_contDiffOn_high_temp
    (d : ℕ) {R T J : ℝ} (hJ : 0 < J)
    (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T < 1)
    (hkp2dR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρ2dR : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1)
    (hkp2dT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1)
    (hρ2dT : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T)) ^ 2 < 1)
    {n : ℕ∞} :
    ContDiffOn ℝ n (fun β' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ))
      (Set.Ioo 0 (Real.artanh T / J)) :=
  (freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticOnNhd_high_temp d hJ hR hT hTR hT1
    hkp2dR hρ2dR hkp2dT hρ2dT).contDiffOn_of_completeSpace

/-- **Internal energy density is real-analytic in the high-temperature phase** (GJ §18.6): the
`β`-derivative of the infinite-volume free energy — the internal energy density (up to the
standard thermodynamic sign) — is real-analytic on the high-temperature interval. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_energyDensity_analyticOnNhd_high_temp
    (d : ℕ) {R T J : ℝ} (hJ : 0 < J)
    (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T < 1)
    (hkp2dR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρ2dR : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1)
    (hkp2dT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1)
    (hρ2dT : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T)) ^ 2 < 1) :
    AnalyticOnNhd ℝ (deriv (fun β' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ)))
      (Set.Ioo 0 (Real.artanh T / J)) :=
  (freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticOnNhd_high_temp d hJ hR hT hTR hT1
    hkp2dR hρ2dR hkp2dT hρ2dT).deriv

/-- **Specific heat is real-analytic in the high-temperature phase** (GJ §18.6): the second
`β`-derivative of the infinite-volume free energy — the specific heat (up to thermodynamic
normalisation) — is real-analytic on the high-temperature interval. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_specificHeat_analyticOnNhd_high_temp
    (d : ℕ) {R T J : ℝ} (hJ : 0 < J)
    (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T < 1)
    (hkp2dR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρ2dR : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1)
    (hkp2dT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1)
    (hρ2dT : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T)) ^ 2 < 1) :
    AnalyticOnNhd ℝ (deriv (deriv (fun β' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ))))
      (Set.Ioo 0 (Real.artanh T / J)) :=
  ((freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticOnNhd_high_temp d hJ hR hT hTR hT1
    hkp2dR hρ2dR hkp2dT hρ2dT).deriv).deriv

end IsingModel
