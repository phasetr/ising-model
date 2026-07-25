import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityFiniteVolumeMajorant
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityDartRatio

/-!
# GJ §17.5 Theorem 17.5.1 — PR-FV3b: the finite-volume per-dart correlation ratio (p.312)

The finite-volume analogue of `correlationInfinite_dart_ratio_le` (#4338): for a distinct
**binding** pair `x ≠ y` of the box (FV per-pair mass = finite-region mass `m⁻_FV(σ,A)`) and an
adjacent dart `u ∼ v` inside the box,
`⟨φ_x φ_u⟩_{σ,A}·⟨φ_y φ_v⟩_{σ,A} / ⟨φ_x φ_y⟩_{σ,A}
  ≤ 2·e^{m⁻_FV}·(1+(m⁻_FV·d(x,y))^α)·s(x,u)·s(y,v)`  (`s(a,b)=1/(1+(m⁻_FV·d(a,b))^α)`).

Numerator factors majorized by the finite-region profile (FV3a
`correlationAlongExhaustion_le_pseudoMassG_finiteRegionFV`); denominator equals the profile at the
binding pair (FV3a `correlationAlongExhaustion_eq_pseudoMassG_finiteVolume` + the FV binding
`hbind`);
the **pure** profile-ratio algebra `pseudoMassG_ratio_le` (#4335) with the dart exp-cancellation
`exp_neg_scaled_dart_pair_le_exp` (#4337) — both reused verbatim.  Unlike the infinite-volume route,
the binding `hbind` is automatic at the in-box binding pair and every in-box correlation decays at
rate `≥ m⁻_FV(σ,A)`, so there is no `exp` blow-up.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Finite-volume per-dart correlation ratio (binding pair)** (GJ p.312): for a distinct in-box
binding pair `x ≠ y` (`pseudoMassFromParamsAtPairFV = m⁻_FV(σ,A)`) and an adjacent dart `u ∼ v` with
`x ≠ u`, `y ≠ v`, all in the box,
`⟨φ_x φ_u⟩_{σ,A}·⟨φ_y φ_v⟩_{σ,A} / ⟨φ_x φ_y⟩_{σ,A}
  ≤ 2·(1+(m⁻_FV·d(x,y))^α)·s(x,u)·s(y,v)·e^{m⁻_FV}`.
Faithful finite-volume mirror of `correlationInfinite_dart_ratio_le` (#4338) using the FV3a
majorant/identity at scale `m⁻_FV(σ,A)` and the reused pure ratio algebra `pseudoMassG_ratio_le`. -/
theorem correlationAlongExhaustion_dart_ratio_le_finiteRegionFV {α d : ℕ} (hα : 1 ≤ α) {J β : ℝ}
    (hJ : 0 < J) (hβ : 0 < β) {n : ℕ}
    (hA : (finiteRegionDistinctPairs ((cubicExhaustion d).volume n)).Nonempty)
    {x y u v : Fin d → ℤ} (hxy : x ≠ y) (hxu : x ≠ u) (hyv : y ≠ v)
    (hadj : (IsingModel.latticeGraph d).Adj u v)
    (hxysub : ({x, y} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n)
    (hxusub : ({x, u} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n)
    (hyvsub : ({y, v} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n)
    (hbind : pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x y
      = finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA) :
    Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, u} n *
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {y, v} n /
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, y} n
      ≤ 2 * (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA
              * (latticeDistance d x y : ℝ)) ^ α)
          * (1 / (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA
              * (latticeDistance d x u : ℝ)) ^ α))
          * (1 / (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA
              * (latticeDistance d y v : ℝ)) ^ α))
          * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA) := by
  set m : ℝ := finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA with hm_def
  have hm_nn : 0 ≤ m := by rw [hm_def]; exact (finiteRegionPseudoMassDistFV_pos hα hJ hβ hA).le
  have hdxu_pos : (0 : ℝ) < (latticeDistance d x u : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (fun h => hxu ((IsingModel.latticeDistance_eq_zero_iff d x u).mp h))
  set cxy : ℝ := Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {x, y} n with hcxy_def
  set cxu : ℝ := Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {x, u} n with hcxu_def
  set cyv : ℝ := Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {y, v} n with hcyv_def
  -- denominator = profile at binding pair.
  have hc_eq : cxy = pseudoMassG α (latticeDistance d x y : ℝ) m := by
    rw [hcxy_def, correlationAlongExhaustion_eq_pseudoMassG_finiteVolume hα hJ hβ hxy hxysub, hbind]
  have hcxy_pos : 0 < cxy := by
    rw [hcxy_def]
    exact (correlationAlongExhaustion_cubicExhaustion_pair_active hJ hβ hxy hxysub).1
  -- numerator majorants and nonnegativity.
  have hcyv_nn : 0 ≤ cyv := by
    rw [hcyv_def]
    exact (correlationAlongExhaustion_cubicExhaustion_pair_active hJ hβ hyv hyvsub).1.le
  have hxu_maj : cxu ≤ pseudoMassG α (latticeDistance d x u : ℝ) m := by
    rw [hcxu_def, hm_def]
    exact correlationAlongExhaustion_le_pseudoMassG_finiteRegionFV hα hJ hβ hA hxu hxusub
  have hyv_maj : cyv ≤ pseudoMassG α (latticeDistance d y v : ℝ) m := by
    rw [hcyv_def, hm_def]
    exact correlationAlongExhaustion_le_pseudoMassG_finiteRegionFV hα hJ hβ hA hyv hyvsub
  have hnum : cxu * cyv ≤ pseudoMassG α (latticeDistance d x u : ℝ) m
      * pseudoMassG α (latticeDistance d y v : ℝ) m :=
    mul_le_mul hxu_maj hyv_maj hcyv_nn (pseudoMassG_pos α hm_nn hdxu_pos).le
  have hexp := exp_neg_scaled_dart_pair_le_exp (d := d) (t := m) hm_nn x y u v hadj
  have halg := pseudoMassG_ratio_le (α := α) (m := m)
    (a := (latticeDistance d x u : ℝ)) (b := (latticeDistance d y v : ℝ))
    (c := (latticeDistance d x y : ℝ)) hm_nn (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hexp
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
