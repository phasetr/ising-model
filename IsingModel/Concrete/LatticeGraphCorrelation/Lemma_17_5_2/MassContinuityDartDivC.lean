import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityDartSum
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuitySingletonZero

/-!
# GJ §17.5 Theorem 17.5.1 — PR-1i: the unified per-dart `/c` bound (p.312)

Converting the c-cancelling Lebowitz cross-sum (#4341) to a dart sum via the handshake identity
`sum_edgeFinset_sym2_lift_prod_eq_sum_dart` yields, for each dart `dt`, the ordered product
`⟨φ_x φ_{dt.fst}⟩·⟨φ_z φ_{dt.snd}⟩`.  This bounds each such term divided by `c = ⟨φ_x φ_z⟩`,
*uniformly for every dart*, by the per-dart profile-ratio bound:

* **degenerate darts** (`dt.fst.val = x` or `dt.snd.val = z`): the term has a single-site factor
  `⟨φ_x φ_x⟩ = ⟨φ_x⟩` or `⟨φ_z φ_z⟩ = ⟨φ_z⟩`, which vanishes at zero field
  (#4345 `correlationInfinite_latticeGraph_singleton_zero_field`), so the term is `0 ≤ RHS`;
* **non-degenerate darts** (`x ≠ dt.fst.val`, `z ≠ dt.snd.val`): the per-dart ratio
  `correlationInfinite_dart_ratio_le` (#4338) applies directly (the dart adjacency
  `dt.adj` is exactly the lattice adjacency needed).

The uniform RHS is the #4338 form `2·(1+(m⁻·d(x,z))^α)·s(x,dt.fst)·s(z,dt.snd)·e^{m⁻}`
(`s(a,b) = 1/(1+(m⁻·d(a,b))^α)`), summable over darts via the m⁻-scaled HLS convolution (#4336).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Unified per-dart `/c` bound** (GJ p.312): for a distinct binding pair `x ≠ z`
(`m⁻(x,z) = globalPseudoMassDist`) and *any* dart `dt` of the induced cubic graph,
`⟨φ_x φ_{dt.fst}⟩·⟨φ_z φ_{dt.snd}⟩ / ⟨φ_x φ_z⟩
  ≤ 2·(1+(m⁻·d(x,z))^α)·(1/(1+(m⁻·d(x,dt.fst))^α))·(1/(1+(m⁻·d(z,dt.snd))^α))·e^{m⁻}`.

Degenerate darts (`dt.fst.val = x` / `dt.snd.val = z`) give a vanishing single-site factor (#4345),
so the term is `0 ≤ RHS`; non-degenerate darts are exactly the per-dart ratio #4338 with the dart
adjacency `dt.adj`. -/
theorem dart_term_div_c_le {α d : ℕ} (hα : 1 ≤ α)
    {J β : ℝ} (hJ_pos : 0 < J) (hβ : 0 < β)
    {n : ℕ} {x z : Fin d → ℤ} (hxz : x ≠ z)
    (dt : (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).Dart)
    (hbind : pseudoMassFromParamsAtPairDist hα (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      = globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)) :
    Ambient.correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, dt.fst.val} *
      Ambient.correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {z, dt.snd.val} /
      Ambient.correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
      ≤ 2 * (1 + (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              * (latticeDistance d x z : ℝ)) ^ α)
          * (1 / (1 + (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              * (latticeDistance d x dt.fst.val : ℝ)) ^ α))
          * (1 / (1 + (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              * (latticeDistance d z dt.snd.val : ℝ)) ^ α))
          * Real.exp (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)) := by
  classical
  set m : ℝ := globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) with hm_def
  have hm_nn : 0 ≤ m := by rw [hm_def]; exact globalPseudoMassDist_nonneg hα _ _
  -- the uniform RHS is non-negative.
  have hp1 : (0 : ℝ) ≤ (m * (latticeDistance d x z : ℝ)) ^ α :=
    pow_nonneg (mul_nonneg hm_nn (by positivity)) α
  have hp2 : (0 : ℝ) ≤ (m * (latticeDistance d x dt.fst.val : ℝ)) ^ α :=
    pow_nonneg (mul_nonneg hm_nn (by positivity)) α
  have hp3 : (0 : ℝ) ≤ (m * (latticeDistance d z dt.snd.val : ℝ)) ^ α :=
    pow_nonneg (mul_nonneg hm_nn (by positivity)) α
  have hA : (0 : ℝ) ≤ 1 + (m * (latticeDistance d x z : ℝ)) ^ α := by linarith
  have hB : (0 : ℝ) ≤ 1 / (1 + (m * (latticeDistance d x dt.fst.val : ℝ)) ^ α) :=
    (one_div_nonneg).mpr (by linarith)
  have hC : (0 : ℝ) ≤ 1 / (1 + (m * (latticeDistance d z dt.snd.val : ℝ)) ^ α) :=
    (one_div_nonneg).mpr (by linarith)
  have hRHS_nn : (0 : ℝ) ≤ 2 * (1 + (m * (latticeDistance d x z : ℝ)) ^ α)
        * (1 / (1 + (m * (latticeDistance d x dt.fst.val : ℝ)) ^ α))
        * (1 / (1 + (m * (latticeDistance d z dt.snd.val : ℝ)) ^ α)) * Real.exp m :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA) hB) hC) (Real.exp_nonneg m)
  by_cases hfx : dt.fst.val = x
  · -- ⟨φ_x φ_x⟩ = ⟨φ_x⟩ = 0.
    have hzero : Ambient.correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, dt.fst.val} = 0 := by
      rw [hfx, show ({x, x} : Finset (Fin d → ℤ)) = {x} from by simp]
      exact correlationInfinite_latticeGraph_singleton_zero_field _ hJ_pos.le hβ x
    rw [hzero, zero_mul, zero_div]
    exact hRHS_nn
  · by_cases hsz : dt.snd.val = z
    · -- ⟨φ_z φ_z⟩ = ⟨φ_z⟩ = 0.
      have hzero : Ambient.correlationInfinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {z, dt.snd.val} = 0 := by
        rw [hsz, show ({z, z} : Finset (Fin d → ℤ)) = {z} from by simp]
        exact correlationInfinite_latticeGraph_singleton_zero_field _ hJ_pos.le hβ z
      rw [hzero, mul_zero, zero_div]
      exact hRHS_nn
    · -- non-degenerate: the per-dart ratio applies.
      have hxu : x ≠ dt.fst.val := fun h => hfx h.symm
      have hyv : z ≠ dt.snd.val := fun h => hsz h.symm
      have hadj : (latticeGraph d).Adj dt.fst.val dt.snd.val := dt.adj
      rw [hm_def]
      exact correlationInfinite_dart_ratio_le hα hJ_pos hβ hxz hxu hyv hadj hbind

end Ambient
end IsingModel
