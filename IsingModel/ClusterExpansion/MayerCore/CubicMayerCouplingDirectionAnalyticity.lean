import IsingModel.ClusterExpansion.MayerCore.CubicMayerHighTempIntervalAnalyticity

/-!
# Coupling-direction analyticity of the infinite-volume free energy (GJ §18.6)

The §18.6 capstone and its interval upgrade are stated in the inverse temperature `β` (at fixed
coupling `J`). Glimm--Jaffe §18.6 is, however, literally about analyticity in the **coupling**. This
file supplies the coupling-direction (`J`) results, obtained from the `β`-direction unit-coupling
capstone via the zero-field scaling symmetry
`freeEnergyInfinite ⟨J,0,β⟩ = freeEnergyInfinite ⟨β·J,0,1⟩` (`freeEnergyInfinite_scaling`): writing
`g(c) := freeEnergyInfinite ⟨c,0,1⟩`, the `J`-section is `g ∘ (·β)`, an analytic function composed
with the linear map `J' ↦ β J'`, so `AnalyticAt.comp` transports the unit-coupling analyticity of
`g` (at the point `β J`) to the coupling direction.

* `..._analyticAt_J_h_zero` — analyticity in the coupling `J` at a high-temperature point.
* `..._analyticOnNhd_J_high_temp` — analyticity on the whole high-temperature coupling interval
  `J ∈ (0, artanh T / β)`.
* `..._continuousOn_J_high_temp` / `..._contDiffOn_J_high_temp` — continuity and `C^∞` smoothness in
  the coupling (no singularity in the coupling at high temperature).
* `..._couplingEnergy_analyticOnNhd_J_high_temp` — the coupling derivative `∂f/∂J` is real-analytic.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §18.6.
-/

namespace IsingModel

open Ambient Set Filter Topology

/-- `Real.tanh` is strictly monotone (local copy; the global version lives in `PseudoMass/Profile`,
which is not on this import path). -/
private theorem real_tanh_strictMono_coupling : StrictMono Real.tanh := by
  intro x y hxy
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
  have hcx : 0 < Real.cosh x := Real.cosh_pos _
  have hcy : 0 < Real.cosh y := Real.cosh_pos _
  rw [div_lt_div_iff₀ hcx hcy]
  have hsub_pos : 0 < Real.sinh (y - x) := Real.sinh_pos_iff.mpr (sub_pos.mpr hxy)
  have heq : Real.sinh (y - x) =
      Real.sinh y * Real.cosh x - Real.cosh y * Real.sinh x := Real.sinh_sub y x
  linarith

/-- **Coupling-direction analyticity at a high-temperature point** (GJ §18.6): the infinite-volume
cubic-Ising free-energy density at zero field is real-analytic in the **coupling** `J` at any point
with `0 < β J` and `tanh (β J) < T`. Obtained from the `β`-direction unit-coupling capstone via the
zero-field scaling symmetry and analytic composition with the linear map `J' ↦ β J'`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticAt_J_h_zero
    (d : ℕ) {R T J β : ℝ}
    (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T ≤ 1)
    (hkp2dR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρ2dR : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1)
    (hkp2dT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1)
    (hρ2dT : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T)) ^ 2 < 1)
    (hβJ_pos : 0 < β * J) (hβJ_tanh : Real.tanh (β * J) < T) :
    AnalyticAt ℝ (fun J' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J', 0, β⟩ : IsingParams ℝ)) J := by
  have hg : AnalyticAt ℝ (fun b : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨1, 0, b⟩ : IsingParams ℝ)) (β * J) :=
    freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticAt_beta_unitCoupling d
      hR hT hTR hT1 hkp2dR hρ2dR hkp2dT hρ2dT hβJ_pos hβJ_tanh
  have hgc : AnalyticAt ℝ (fun c : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨c, 0, 1⟩ : IsingParams ℝ)) (β * J) := by
    have hfun : (fun b : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨1, 0, b⟩ : IsingParams ℝ))
        = (fun c : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨c, 0, 1⟩ : IsingParams ℝ)) := by
      funext b
      rw [freeEnergyInfinite_scaling (latticeGraph d) (Ambient.cubicExhaustion d) 1 b, mul_one]
    rwa [hfun] at hg
  have htarget : (fun J' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J', 0, β⟩ : IsingParams ℝ))
      = (fun c : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨c, 0, 1⟩ : IsingParams ℝ)) ∘ (fun J' : ℝ => β * J') := by
    funext J'
    simp only [Function.comp_apply]
    rw [freeEnergyInfinite_scaling (latticeGraph d) (Ambient.cubicExhaustion d) J' β]
  rw [htarget]
  exact hgc.comp (analyticAt_const.mul analyticAt_id)

/-- **Coupling-interval analyticity** (GJ §18.6): for `β > 0`, the infinite-volume free-energy
density is real-analytic on the whole high-temperature coupling interval `J ∈ (0, artanh T / β)`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticOnNhd_J_high_temp
    (d : ℕ) {R T β : ℝ} (hβ : 0 < β)
    (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T < 1)
    (hkp2dR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρ2dR : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1)
    (hkp2dT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1)
    (hρ2dT : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T)) ^ 2 < 1) :
    AnalyticOnNhd ℝ (fun J' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J', 0, β⟩ : IsingParams ℝ))
      (Set.Ioo 0 (Real.artanh T / β)) := by
  intro J hJ
  obtain ⟨hJ0, hJlt⟩ := hJ
  have hT_mem : T ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hT1⟩
  have hβJ_pos : 0 < β * J := mul_pos hβ hJ0
  have hβJ_tanh : Real.tanh (β * J) < T := by
    have hlt : β * J < Real.artanh T := by
      rw [mul_comm]; exact (lt_div_iff₀ hβ).mp hJlt
    calc Real.tanh (β * J) < Real.tanh (Real.artanh T) := real_tanh_strictMono_coupling hlt
      _ = T := Real.tanh_artanh hT_mem
  exact freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticAt_J_h_zero d hR hT hTR
    (le_of_lt hT1) hkp2dR hρ2dR hkp2dT hρ2dT hβJ_pos hβJ_tanh

/-- **Continuity in the coupling** on the high-temperature interval (GJ §18.6). -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_continuousOn_J_high_temp
    (d : ℕ) {R T β : ℝ} (hβ : 0 < β)
    (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T < 1)
    (hkp2dR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρ2dR : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1)
    (hkp2dT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1)
    (hρ2dT : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T)) ^ 2 < 1) :
    ContinuousOn (fun J' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J', 0, β⟩ : IsingParams ℝ))
      (Set.Ioo 0 (Real.artanh T / β)) :=
  (freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticOnNhd_J_high_temp d hβ hR hT hTR hT1
    hkp2dR hρ2dR hkp2dT hρ2dT).continuousOn

/-- **`C^∞` smoothness in the coupling** on the high-temperature interval (GJ §18.6): no singularity
in the coupling at high temperature. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_contDiffOn_J_high_temp
    (d : ℕ) {R T β : ℝ} (hβ : 0 < β)
    (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T < 1)
    (hkp2dR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρ2dR : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1)
    (hkp2dT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1)
    (hρ2dT : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T)) ^ 2 < 1)
    {n : ℕ∞} :
    ContDiffOn ℝ n (fun J' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J', 0, β⟩ : IsingParams ℝ))
      (Set.Ioo 0 (Real.artanh T / β)) :=
  (freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticOnNhd_J_high_temp d hβ hR hT hTR hT1
    hkp2dR hρ2dR hkp2dT hρ2dT).contDiffOn_of_completeSpace

/-- **Coupling energy density is real-analytic** (GJ §18.6): the coupling derivative `∂f/∂J` — the
bond energy density (up to the standard thermodynamic sign) — is real-analytic on the
high-temperature coupling interval. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_couplingEnergy_analyticOnNhd_J_high_temp
    (d : ℕ) {R T β : ℝ} (hβ : 0 < β)
    (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T < 1)
    (hkp2dR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρ2dR : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1)
    (hkp2dT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1)
    (hρ2dT : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T)) ^ 2 < 1) :
    AnalyticOnNhd ℝ (deriv (fun J' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J', 0, β⟩ : IsingParams ℝ)))
      (Set.Ioo 0 (Real.artanh T / β)) :=
  (freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticOnNhd_J_high_temp d hβ hR hT hTR hT1
    hkp2dR hρ2dR hkp2dT hρ2dT).deriv

end IsingModel
