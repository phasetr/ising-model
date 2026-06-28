import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityDartRatio

/-!
# GJ §17.5 Theorem 17.5.1 — PR-1f: single-factor (incident) exp-cancellation and profile ratio

The c-cancelling incident bound (#4339–#4341) reduces the GJ p.312 incident error to a sum of
infinite-volume two-point functions `g{z,v}` over darts `v ∼ x` (the neighbours of `x`).  Dividing
each such factor by `c = ⟨φ_x φ_z⟩` requires the **single-factor** (one numerator) analogs of the
dart-pair building blocks #4337:

* `exp_neg_scaled_incident_le_exp` — for `v` adjacent to `x`,
  `exp(−t·(d(z,v) − d(x,z))) ≤ exp t` (triangle through the edge `{x,v}`, `d(x,z) ≤ 1 + d(z,v)`);
* `pseudoMassG_single_ratio_le` — the single-factor profile ratio algebra: with
  `P(r) = pseudoMassG α r m`,
  `P(a)/P(c) = (1+(mc)^α)·(1/(1+(ma)^α))·e^{−m(a−c)} ≤ (1+(mc)^α)·(1/(1+(ma)^α))·e^{m}` for
  `m,a,c ≥ 0`, given the exp bound (the `2`'s cancel — no factor `2` here).

Combined with the system-mass majorant + (17.5.3) identity (#4335) these give the per-incident-dart
correlation ratio `g{z,v}/c` and the incident-sum/`c` bound (the subject of the PR-1f assembly).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Single-factor (incident) exp-cancellation.**  For `t ≥ 0` and `v` adjacent to `x`,
`exp(−t·(d(z,v) − d(x,z))) ≤ exp t`.  The triangle inequality through the edge `{x,v}`
(`d(x,z) ≤ d(x,v) + d(v,z) = 1 + d(z,v)`) gives `d(x,z) − d(z,v) ≤ 1`, so the exponent
`t·(d(x,z) − d(z,v)) ≤ t`. -/
theorem exp_neg_scaled_incident_le_exp {d : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (x z v : Fin d → ℤ) (hadj : (IsingModel.latticeGraph d).Adj x v) :
    Real.exp (-(t * ((latticeDistance d z v : ℝ) - (latticeDistance d x z : ℝ)))) ≤ Real.exp t := by
  apply Real.exp_le_exp.mpr
  have hxv : latticeDistance d x v = 1 :=
    (latticeGraph_adj_iff_latticeDistance_eq_one d x v).mp hadj
  -- d(x,z) ≤ d(x,v) + d(v,z) = 1 + d(z,v).
  have htri : latticeDistance d x z ≤ latticeDistance d x v + latticeDistance d v z :=
    latticeDistance_triangle d x v z
  have hvz : latticeDistance d v z = latticeDistance d z v := latticeDistance_comm d v z
  have hxz_le : (latticeDistance d x z : ℝ) ≤ 1 + (latticeDistance d z v : ℝ) := by
    have : latticeDistance d x z ≤ 1 + latticeDistance d z v := by rw [hxv, hvz] at htri; omega
    exact_mod_cast this
  have hge : (latticeDistance d x z : ℝ) - (latticeDistance d z v : ℝ) ≤ 1 := by linarith
  nlinarith [ht, hge]

/-- **`pseudoMassG` single-factor profile ratio algebra.**  With `P(r) = pseudoMassG α r m =
2 e^{−mr}/(1+(mr)^α)`, the `2`'s cancel in the ratio:
`P(a)/P(c) = (1+(mc)^α)·(1/(1+(ma)^α))·e^{−m(a−c)}`, which is therefore
`≤ (1+(mc)^α)·(1/(1+(ma)^α))·e^{m}` whenever `e^{−m(a−c)} ≤ e^{m}` (the incident exp-cancellation).
This is the single-numerator analog of `pseudoMassG_ratio_le` (#4337), for the GJ p.312 incident
error term. -/
theorem pseudoMassG_single_ratio_le {α : ℕ} {m a c : ℝ}
    (hm : 0 ≤ m) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hexp : Real.exp (-(m * (a - c))) ≤ Real.exp m) :
    pseudoMassG α a m / pseudoMassG α c m
      ≤ (1 + (m * c) ^ α) * (1 / (1 + (m * a) ^ α)) * Real.exp m := by
  have hda : (0 : ℝ) < 1 + (m * a) ^ α := by positivity
  have hkey : pseudoMassG α a m / pseudoMassG α c m
      = (1 + (m * c) ^ α) * (1 / (1 + (m * a) ^ α)) * Real.exp (-(m * (a - c))) := by
    unfold pseudoMassG
    rw [show -(m * (a - c)) = -(m * a) - -(m * c) by ring, Real.exp_sub]
    field_simp
  rw [hkey]
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- **Per-incident-dart correlation ratio bound (binding pair).**  For a distinct binding pair
`x ≠ z` (`m⁻(x,z) = globalPseudoMassDist`) and an incident dart `v ∼ x` with `z ≠ v`:
`⟨φ_z φ_v⟩ / ⟨φ_x φ_z⟩ ≤ (1+(m⁻·d(x,z))^α)·(1/(1+(m⁻·d(z,v))^α))·e^{m⁻}`.

The numerator `⟨φ_z φ_v⟩` is majorized by the system-mass profile `pseudoMassG α (d(z,v)) m⁻` (#4335
`correlationInfinite_le_pseudoMassG_globalPseudoMassDist`); the denominator equals the profile at
the binding pair `pseudoMassG α (d(x,z)) m⁻` (#4335 `correlationInfinite_eq_pseudoMassG_pairDist` +
`hbind`); the single-factor ratio algebra `pseudoMassG_single_ratio_le` with the incident
exp-cancellation `exp_neg_scaled_incident_le_exp` closes.  This is the per-incident-dart analog of
the per-dart ratio `correlationInfinite_dart_ratio_le` (#4338). -/
theorem correlationInfinite_incident_ratio_le
    {α d : ℕ} (hα : 1 ≤ α)
    {J β : ℝ} (hJ_pos : 0 < J) (hβ : 0 < β)
    {x z v : Fin d → ℤ} (hxz : x ≠ z) (hzv : z ≠ v)
    (hadj : (IsingModel.latticeGraph d).Adj x v)
    (hbind : pseudoMassFromParamsAtPairDist hα (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      = globalPseudoMassDist hα (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {z, v} /
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
      ≤ (1 + (globalPseudoMassDist hα (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) * (latticeDistance d x z : ℝ)) ^ α)
          * (1 / (1 + (globalPseudoMassDist hα (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) * (latticeDistance d z v : ℝ)) ^ α))
          * Real.exp (globalPseudoMassDist hα (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ)) := by
  set m : ℝ := globalPseudoMassDist hα (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
    with hm_def
  have hm_nn : 0 ≤ m := by rw [hm_def]; exact globalPseudoMassDist_nonneg hα _ _
  set cxz : ℝ := Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} with hcxz_def
  set czv : ℝ := Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {z, v} with hczv_def
  -- denominator = profile at binding pair.
  have hc_eq : cxz = pseudoMassG α (latticeDistance d x z : ℝ) m := by
    rw [hcxz_def, correlationInfinite_eq_pseudoMassG_pairDist hα hJ_pos hβ hxz, hbind]
  have hcxz_pos : 0 < cxz := by
    rw [hcxz_def]; exact (correlationInfinite_pair_active_of_betaJ_pos_exhaustion
      (Ambient.cubicExhaustion d) hβ (mul_pos hβ hJ_pos) x z hxz).1
  -- numerator majorant.
  have hzv_maj : czv ≤ pseudoMassG α (latticeDistance d z v : ℝ) m := by
    rw [hczv_def, hm_def]
    exact correlationInfinite_le_pseudoMassG_globalPseudoMassDist hα hJ_pos hβ hzv
  -- ratio ≤ profile ratio ≤ single-factor algebra.
  have hexp := exp_neg_scaled_incident_le_exp (d := d) (t := m) hm_nn x z v hadj
  have halg := pseudoMassG_single_ratio_le (α := α) (m := m)
    (a := (latticeDistance d z v : ℝ)) (c := (latticeDistance d x z : ℝ))
    hm_nn (by positivity) (by positivity) hexp
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
