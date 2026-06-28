import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityFiniteVolumeDartRatio
import IsingModel.Concrete.LatticeGraphCorrelation.UniformMagCorrelationTrivialHZero

/-!
# GJ §17.5 Theorem 17.5.1 — PR-FV3c: the finite-volume unified per-dart `/c` bound (p.312)

The finite-volume analogue of `dart_term_div_c_le` (#4346): for a distinct in-box **binding** pair
`x ≠ z` and *any* dart `dt` of the induced cubic graph, the ordered product
`⟨φ_x φ_{dt.fst}⟩_{σ,A}·⟨φ_z φ_{dt.snd}⟩_{σ,A}` divided by `c = ⟨φ_x φ_z⟩_{σ,A}` is bounded
*uniformly over every dart* by `2·(1+(m⁻_FV·d(x,z))^α)·s(x,dt.fst)·s(z,dt.snd)·e^{m⁻_FV}`.

* **degenerate darts** (`dt.fst.val = x` or `dt.snd.val = z`): a single-site factor
  `⟨φ_x φ_x⟩_{σ,A} = ⟨φ_x⟩_{σ,A}` vanishes at zero field (odd cardinality;
  `correlationAlongExhaustion_latticeGraph_h_zero`), so the term is `0 ≤ RHS`;
* **non-degenerate darts**: the per-dart ratio
  `correlationAlongExhaustion_dart_ratio_le_finiteRegionFV` (PR-FV3b) applies with `dt.adj`.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Finite-volume unified per-dart `/c` bound** (GJ p.312): for a distinct in-box binding pair
`x ≠ z` (`pseudoMassFromParamsAtPairFV = m⁻_FV(σ,A)`) and *any* dart `dt` of the induced graph,
`⟨φ_x φ_{dt.fst}⟩_{σ,A}·⟨φ_z φ_{dt.snd}⟩_{σ,A} / ⟨φ_x φ_z⟩_{σ,A}
  ≤ 2·(1+(m⁻_FV·d(x,z))^α)·(1/(1+(m⁻_FV·d(x,dt.fst))^α))·(1/(1+(m⁻_FV·d(z,dt.snd))^α))·e^{m⁻_FV}`.
Degenerate darts vanish via `correlationAlongExhaustion_latticeGraph_h_zero` (single-site, odd
card); non-degenerate darts are the FV per-dart ratio (PR-FV3b) with `dt.adj`. -/
theorem dart_term_div_c_le_finiteRegionFV {α d : ℕ} (hα : 1 ≤ α) {J β : ℝ}
    (hJ : 0 < J) (hβ : 0 < β) {n : ℕ}
    (hA : (finiteRegionDistinctPairs ((cubicExhaustion d).volume n)).Nonempty)
    {x z : Fin d → ℤ} (hxz : x ≠ z) (hx : x ∈ (cubicExhaustion d).volume n)
    (hz : z ∈ (cubicExhaustion d).volume n)
    (dt : (inducedGraph (IsingModel.latticeGraph d) ((cubicExhaustion d).volume n)).Dart)
    (hbind : pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z
      = finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA) :
    Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, dt.fst.val} n *
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {z, dt.snd.val} n /
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n
      ≤ 2 * (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA
              * (latticeDistance d x z : ℝ)) ^ α)
          * (1 / (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA
              * (latticeDistance d x dt.fst.val : ℝ)) ^ α))
          * (1 / (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA
              * (latticeDistance d z dt.snd.val : ℝ)) ^ α))
          * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA) := by
  classical
  set m : ℝ := finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA with hm_def
  have hm_nn : 0 ≤ m := by rw [hm_def]; exact (finiteRegionPseudoMassDistFV_pos hα hJ hβ hA).le
  -- the uniform RHS is non-negative.
  have hA1 : (0 : ℝ) ≤ 1 + (m * (latticeDistance d x z : ℝ)) ^ α := by positivity
  have hB1 : (0 : ℝ) ≤ 1 / (1 + (m * (latticeDistance d x dt.fst.val : ℝ)) ^ α) := by positivity
  have hC1 : (0 : ℝ) ≤ 1 / (1 + (m * (latticeDistance d z dt.snd.val : ℝ)) ^ α) := by positivity
  have hRHS_nn : (0 : ℝ) ≤ 2 * (1 + (m * (latticeDistance d x z : ℝ)) ^ α)
        * (1 / (1 + (m * (latticeDistance d x dt.fst.val : ℝ)) ^ α))
        * (1 / (1 + (m * (latticeDistance d z dt.snd.val : ℝ)) ^ α)) * Real.exp m :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA1) hB1) hC1) (Real.exp_nonneg m)
  by_cases hfx : dt.fst.val = x
  · -- ⟨φ_x φ_x⟩ = ⟨φ_x⟩ = 0 (single-site, odd card).
    have hzero : Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, dt.fst.val} n = 0 := by
      rw [hfx, show ({x, x} : Finset (Fin d → ℤ)) = {x} from by simp]
      exact correlationAlongExhaustion_latticeGraph_h_zero d J β {x} (by simp) n
    rw [hzero, zero_mul, zero_div]
    exact hRHS_nn
  · by_cases hsz : dt.snd.val = z
    · -- ⟨φ_z φ_z⟩ = ⟨φ_z⟩ = 0.
      have hzero : Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d)
          (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {z, dt.snd.val} n = 0 := by
        rw [hsz, show ({z, z} : Finset (Fin d → ℤ)) = {z} from by simp]
        exact correlationAlongExhaustion_latticeGraph_h_zero d J β {z} (by simp) n
      rw [hzero, mul_zero, zero_div]
      exact hRHS_nn
    · -- non-degenerate: the FV per-dart ratio applies.
      have hxu : x ≠ dt.fst.val := fun h => hfx h.symm
      have hzv : z ≠ dt.snd.val := fun h => hsz h.symm
      have hadj : (IsingModel.latticeGraph d).Adj dt.fst.val dt.snd.val := dt.adj
      have hxusub : ({x, dt.fst.val} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n := by
        intro w hw
        rw [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hx
        · exact dt.fst.property
      have hzvsub : ({z, dt.snd.val} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n := by
        intro w hw
        rw [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hz
        · exact dt.snd.property
      have hxzsub : ({x, z} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n := by
        intro w hw
        rw [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hx
        · exact hz
      rw [hm_def]
      exact correlationAlongExhaustion_dart_ratio_le_finiteRegionFV hα hJ hβ hA hxz hxu hzv
        hadj hxzsub hxusub hzvsub hbind

end Ambient
end IsingModel
