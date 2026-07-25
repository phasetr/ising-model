import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityFiniteVolumeMajorant
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityIncidentRatio

/-!
# GJ §17.5 Theorem 17.5.1 — PR-FV3e: the finite-volume per-incident-dart correlation ratio (p.312)

The finite-volume analogue of `correlationInfinite_incident_ratio_le` (#4342): for a distinct in-box
**binding** pair `x ≠ z` and an incident dart `v ∼ x` (`z ≠ v`, `v` in the box),
`⟨φ_z φ_v⟩_{σ,A} / ⟨φ_x φ_z⟩_{σ,A}
  ≤ (1+(m⁻_FV·d(x,z))^α)·(1/(1+(m⁻_FV·d(z,v))^α))·e^{m⁻_FV}`.

Numerator majorized by the finite-region profile (FV3a
`correlationAlongExhaustion_le_pseudoMassG_finiteRegionFV`); denominator equals the profile at the
binding pair (FV3a `correlationAlongExhaustion_eq_pseudoMassG_finiteVolume` + the FV binding
`hbind`); the **pure** single-factor ratio algebra `pseudoMassG_single_ratio_le` (#4342) with the
incident
exp-cancellation `exp_neg_scaled_incident_le_exp` (#4342) — both reused verbatim.  This is the
per-incident-dart building block of the GJ p.312 bounded `2A` incident error.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Finite-volume per-incident-dart correlation ratio (binding pair)** (GJ p.312): for a distinct
in-box binding pair `x ≠ z` (`pseudoMassFromParamsAtPairFV = m⁻_FV(σ,A)`) and an incident dart
`v ∼ x` with `z ≠ v`, all in the box,
`⟨φ_z φ_v⟩_{σ,A}/⟨φ_x φ_z⟩_{σ,A} ≤ (1+(m⁻_FV·d(x,z))^α)·(1/(1+(m⁻_FV·d(z,v))^α))·e^{m⁻_FV}`.
Faithful finite-volume mirror of `correlationInfinite_incident_ratio_le` (#4342). -/
theorem correlationAlongExhaustion_incident_ratio_le_finiteRegionFV {α d : ℕ} (hα : 1 ≤ α)
    {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) {n : ℕ}
    (hA : (finiteRegionDistinctPairs ((cubicExhaustion d).volume n)).Nonempty)
    {x z v : Fin d → ℤ} (hxz : x ≠ z) (hzv : z ≠ v)
    (hadj : (IsingModel.latticeGraph d).Adj x v)
    (hx : x ∈ (cubicExhaustion d).volume n) (hz : z ∈ (cubicExhaustion d).volume n)
    (hv : v ∈ (cubicExhaustion d).volume n)
    (hbind : pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z
      = finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA) :
    Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {z, v} n /
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n
      ≤ (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA
              * (latticeDistance d x z : ℝ)) ^ α)
          * (1 / (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA
              * (latticeDistance d z v : ℝ)) ^ α))
          * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA) := by
  set m : ℝ := finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA with hm_def
  have hm_nn : 0 ≤ m := by rw [hm_def]; exact (finiteRegionPseudoMassDistFV_pos hα hJ hβ hA).le
  have hxzsub : ({x, z} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n := by
    intro w hw; rw [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hx
    · exact hz
  have hzvsub : ({z, v} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n := by
    intro w hw; rw [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hz
    · exact hv
  set cxz : ℝ := Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n with hcxz_def
  set czv : ℝ := Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {z, v} n with hczv_def
  have hc_eq : cxz = pseudoMassG α (latticeDistance d x z : ℝ) m := by
    rw [hcxz_def, correlationAlongExhaustion_eq_pseudoMassG_finiteVolume hα hJ hβ hxz hxzsub, hbind]
  have hcxz_pos : 0 < cxz := by
    rw [hcxz_def]
    exact (correlationAlongExhaustion_cubicExhaustion_pair_active hJ hβ hxz hxzsub).1
  have hzv_maj : czv ≤ pseudoMassG α (latticeDistance d z v : ℝ) m := by
    rw [hczv_def, hm_def]
    exact correlationAlongExhaustion_le_pseudoMassG_finiteRegionFV hα hJ hβ hA hzv hzvsub
  have hexp := exp_neg_scaled_incident_le_exp (d := d) (t := m) hm_nn x z v hadj
  have halg := pseudoMassG_single_ratio_le (α := α) (m := m)
    (a := (latticeDistance d z v : ℝ)) (c := (latticeDistance d x z : ℝ))
    hm_nn (Nat.cast_nonneg _) (Nat.cast_nonneg _) hexp
  calc czv / cxz
      ≤ pseudoMassG α (latticeDistance d z v : ℝ) m / cxz :=
        div_le_div_of_nonneg_right hzv_maj hcxz_pos.le
    _ = pseudoMassG α (latticeDistance d z v : ℝ) m
          / pseudoMassG α (latticeDistance d x z : ℝ) m := by rw [hc_eq]
    _ ≤ (1 + (m * (latticeDistance d x z : ℝ)) ^ α)
          * (1 / (1 + (m * (latticeDistance d z v : ℝ)) ^ α))
          * Real.exp m := halg

end Ambient
end IsingModel
