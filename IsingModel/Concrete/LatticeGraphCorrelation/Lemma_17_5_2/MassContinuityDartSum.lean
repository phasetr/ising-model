import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityDartRatio

/-!
# GJ §17.5 Theorem 17.5.1 — PR-1d: the per-dart correlation ratio (binding pair)

Combines the system-mass majorant + (17.5.3) identity (#4335) with the dart exp-cancellation +
profile-ratio algebra (#4337) into the per-dart correlation ratio at a binding pair:
`⟨φ_x φ_u⟩·⟨φ_y φ_v⟩ / c ≤ 2·e^{m⁻}·(1+(m⁻·d(x,y))^α)·s(x,u)·s(y,v)`,
where `c = ⟨φ_x φ_y⟩`, `m⁻ = globalPseudoMassDist`, `s(a,b) = 1/(1+(m⁻·d(a,b))^α)`, for an adjacent
dart `u ∼ v`.  This is the per-term bound of the GJ p.312 sum (the dart-sum assembly via #4336 is
PR-1e).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Per-dart correlation ratio bound (binding pair).**  For a distinct binding pair `x ≠ y` (i.e.
`m⁻(x,y) = globalPseudoMassDist`) and an adjacent dart `u ∼ v` with `x ≠ u`, `y ≠ v`:
`⟨φ_x φ_u⟩·⟨φ_y φ_v⟩ / ⟨φ_x φ_y⟩`
`≤ 2·e^{m⁻}·(1+(m⁻·d(x,y))^α)·(1/(1+(m⁻·d(x,u))^α))·(1/(1+(m⁻·d(y,v))^α))`.

Numerator factors majorized by the system-mass profile (#4335
`correlationInfinite_le_pseudoMassG_globalPseudoMassDist`); denominator equals the profile at the
binding pair (#4335 `correlationInfinite_eq_pseudoMassG_pairDist` + `hbind`); the ratio algebra
`pseudoMassG_ratio_le` (#4337) with the dart exp-cancellation `exp_neg_scaled_dart_pair_le_exp`
(#4337). -/
theorem correlationInfinite_dart_ratio_le
    {α d : ℕ} (hα : 1 ≤ α)
    {J β : ℝ} (hJ_pos : 0 < J) (hβ : 0 < β)
    {x y u v : Fin d → ℤ} (hxy : x ≠ y) (hxu : x ≠ u) (hyv : y ≠ v)
    (hadj : (IsingModel.latticeGraph d).Adj u v)
    (hbind : pseudoMassFromParamsAtPairDist hα (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x y
      = globalPseudoMassDist hα (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, u} *
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {y, v} /
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y}
      ≤ 2 * (1 + (globalPseudoMassDist hα (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) * (latticeDistance d x y : ℝ)) ^ α)
          * (1 / (1 + (globalPseudoMassDist hα (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) * (latticeDistance d x u : ℝ)) ^ α))
          * (1 / (1 + (globalPseudoMassDist hα (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) * (latticeDistance d y v : ℝ)) ^ α))
          * Real.exp (globalPseudoMassDist hα (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ)) := by
  set m : ℝ := globalPseudoMassDist hα (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
    with hm_def
  have hm_nn : 0 ≤ m := by rw [hm_def]; exact globalPseudoMassDist_nonneg hα _ _
  have hdxu_pos : (0 : ℝ) < (latticeDistance d x u : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (fun h => hxu ((IsingModel.latticeDistance_eq_zero_iff d x u).mp h))
  set cxy : ℝ := Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y} with hcxy_def
  set cxu : ℝ := Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, u} with hcxu_def
  set cyv : ℝ := Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {y, v} with hcyv_def
  -- denominator = profile at binding pair.
  have hc_eq : cxy = pseudoMassG α (latticeDistance d x y : ℝ) m := by
    rw [hcxy_def, correlationInfinite_eq_pseudoMassG_pairDist hα hJ_pos hβ hxy, hbind]
  have hcxy_pos : 0 < cxy := by
    rw [hcxy_def]; exact (correlationInfinite_pair_active_of_betaJ_pos_exhaustion
      (Ambient.cubicExhaustion d) hβ (mul_pos hβ hJ_pos) x y hxy).1
  -- numerator majorants (nonneg correlations).
  have hcxu_nn : 0 ≤ cxu := by
    rw [hcxu_def]
    exact (correlationInfinite_pair_active_of_betaJ_pos_exhaustion
      (Ambient.cubicExhaustion d) hβ (mul_pos hβ hJ_pos) x u hxu).1.le
  have hcyv_nn : 0 ≤ cyv := by
    rw [hcyv_def]
    exact (correlationInfinite_pair_active_of_betaJ_pos_exhaustion
      (Ambient.cubicExhaustion d) hβ (mul_pos hβ hJ_pos) y v hyv).1.le
  have hxu_maj : cxu ≤ pseudoMassG α (latticeDistance d x u : ℝ) m := by
    rw [hcxu_def, hm_def]
    exact correlationInfinite_le_pseudoMassG_globalPseudoMassDist hα hJ_pos hβ hxu
  have hyv_maj : cyv ≤ pseudoMassG α (latticeDistance d y v : ℝ) m := by
    rw [hcyv_def, hm_def]
    exact correlationInfinite_le_pseudoMassG_globalPseudoMassDist hα hJ_pos hβ hyv
  -- numerator product ≤ profile product.
  have hnum : cxu * cyv ≤ pseudoMassG α (latticeDistance d x u : ℝ) m
      * pseudoMassG α (latticeDistance d y v : ℝ) m :=
    mul_le_mul hxu_maj hyv_maj hcyv_nn (pseudoMassG_pos α hm_nn hdxu_pos).le
  -- ratio ≤ profile ratio ≤ algebra.
  have hexp := exp_neg_scaled_dart_pair_le_exp (d := d) (t := m) hm_nn x y u v hadj
  have halg := pseudoMassG_ratio_le (α := α) (m := m)
    (a := (latticeDistance d x u : ℝ)) (b := (latticeDistance d y v : ℝ))
    (c := (latticeDistance d x y : ℝ)) hm_nn (by positivity) (by positivity) (by positivity) hexp
  calc cxu * cyv / cxy
      ≤ (pseudoMassG α (latticeDistance d x u : ℝ) m
          * pseudoMassG α (latticeDistance d y v : ℝ) m) / cxy :=
        div_le_div_of_nonneg_right hnum hcxy_pos.le
    _ = pseudoMassG α (latticeDistance d x u : ℝ) m
          * pseudoMassG α (latticeDistance d y v : ℝ) m
          / pseudoMassG α (latticeDistance d x y : ℝ) m := by rw [hc_eq]
    _ ≤ 2 * (1 + (m * (latticeDistance d x y : ℝ)) ^ α)
          * (1 / (1 + (m * (latticeDistance d x u : ℝ)) ^ α))
          * (1 / (1 + (m * (latticeDistance d y v : ℝ)) ^ α))
          * Real.exp m := halg

end Ambient
end IsingModel
