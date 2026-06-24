import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeFromSimonLieb
import IsingModel.Inequalities.HighTemp.SummabilityCluster

/-!
# Unconditional adjacent-pair HLS bridge in the strict high-temperature window

This file discharges the adjacent-pair hypothesis `h_adj_exp` of
`PseudoMassLatticeDistanceBridge_of_simonLieb_trichotomy_adjacent` **unconditionally** in
the strict high-temperature window `0 < βJ·2d` and `βJ·2d < 1/2`, using the finite
high-temperature susceptibility bound
`correlationInfinite_latticeGraph_le_susceptibility_bound_of_high_temp`
(`Inequalities/HighTemp/SummabilityCluster.lean`).

## The key step

At `h = 0`, `correlationInfinite {0,w} = U₂(0,w) ≥ 0` (GKS-II), so a single pair term is
bounded by the whole nonnegative susceptibility sum:
`correlationInfinite {0,w} ≤ βJ·2d/(1−βJ·2d) =: B`.  In the strict window `βJ·2d < 1/2` we
have `0 < B < 1`, hence `−log B > 0`.  The Simon–Lieb peeling alone only gives `≤ 1` at
distance `1`, which is exactly why the adjacent input was previously assumed; the
susceptibility ceiling closes that distance-`1` gap.

Choosing `M := min (min 1 (−log B)) (simonLiebRate β J d / (2(α+1)))` simultaneously
satisfies `0 < M`, `M ≤ 1`, `(α+1)·M ≤ simonLiebRate/2`, and the adjacent bound
`correlationInfinite {0,w} ≤ exp(−M)`, so the full Simon–Lieb trichotomy bridge constructor
produces an **unconditional** `PseudoMassLatticeDistanceBridge`.  Feeding it into
`tsum_correlationInfinite_pair_product_le_HLS_const` makes the §17.5 HLS pair-product sum
bound unconditional in the strict window.

**Reference:** Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311–312; §5.1, pp. 73–74;
Friedli–Velenik §3.7.3.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Unconditional adjacent-pair exponential bound in the strict high-temperature
window**: for `0 < βJ·2d` and `βJ·2d < 1/2`, with
`M ≤ −log(βJ·2d/(1−βJ·2d))`, every pair (in particular every adjacent pair) satisfies
`correlationInfinite (latticeGraph d) (cubicExhaustion d) ⟨J,0,β⟩ {0,w} ≤ exp(−M)`.

Proof: `correlationInfinite {0,w} ≤ B := βJ·2d/(1−βJ·2d)` by the finite-susceptibility
ceiling, and `B = exp(log B) ≤ exp(−M)` since `log B ≤ −M`. -/
theorem correlationInfinite_latticeGraph_pair_le_exp_neg_of_high_temp
    {d : ℕ} {J β : ℝ} (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_half : β * J * (2 * d) < 1 / 2)
    {M : ℝ}
    (hM_le : M ≤ -Real.log (β * J * (2 * d) / (1 - β * J * (2 * d))))
    (w : Fin d → ℤ) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
      ≤ Real.exp (-M) := by
  set B := β * J * (2 * d) / (1 - β * J * (2 * d)) with hB_def
  have hβJd_lt1 : β * J * (2 * d) < 1 := by linarith
  have hden_pos : 0 < 1 - β * J * (2 * d) := by linarith
  have hB_pos : 0 < B := div_pos hβJd_pos hden_pos
  have hB_lt1 : B < 1 := by
    rw [hB_def, div_lt_one hden_pos]; linarith
  have hcorr_le_B :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w} ≤ B :=
    correlationInfinite_latticeGraph_le_susceptibility_bound_of_high_temp hf hβJd_lt1 0 w
  have hlogB : Real.log B ≤ -M := by linarith [hM_le]
  have hB_le_exp : B ≤ Real.exp (-M) := by
    calc B = Real.exp (Real.log B) := (Real.exp_log hB_pos).symm
      _ ≤ Real.exp (-M) := Real.exp_le_exp.mpr hlogB
  exact hcorr_le_B.trans hB_le_exp

/-- **Unconditional `PseudoMassLatticeDistanceBridge` in the strict high-temperature
window** `0 < βJ·2d < 1/2`.

Discharges the adjacent hypothesis `h_adj_exp` of
`PseudoMassLatticeDistanceBridge_of_simonLieb_trichotomy_adjacent` from the
finite-susceptibility ceiling, choosing the pseudo-mass rate
`M := min (min 1 (−log B)) (simonLiebRate β J d / (2(α+1)))` with
`B := βJ·2d/(1−βJ·2d) ∈ (0,1)`.  No adjacent-decay hypothesis is required. -/
noncomputable def pseudoMassLatticeDistanceBridge_of_high_temp
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_half : β * J * (2 * d) < 1 / 2) :
    PseudoMassLatticeDistanceBridge hα hr d J β := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  have hβJd_lt1 : β * J * (2 * d) < 1 := by linarith
  set B := β * J * (2 * d) / (1 - β * J * (2 * d)) with hB_def
  have hden_pos : 0 < 1 - β * J * (2 * d) := by linarith
  have hB_pos : 0 < B := div_pos hβJd_pos hden_pos
  have hB_lt1 : B < 1 := by rw [hB_def, div_lt_one hden_pos]; linarith
  have hnlogB_pos : 0 < -Real.log B := by
    have := Real.log_neg hB_pos hB_lt1; linarith
  have hSL_pos : 0 < simonLiebRate β J d := simonLiebRate_pos hβJd_pos hβJd_lt1
  have hαR_pos : (0 : ℝ) < (α : ℝ) + 1 := by positivity
  have hSLfrac_pos : 0 < simonLiebRate β J d / (2 * ((α : ℝ) + 1)) := by positivity
  set M := min (min 1 (-Real.log B)) (simonLiebRate β J d / (2 * ((α : ℝ) + 1))) with hM_def
  have hM_pos : 0 < M :=
    lt_min (lt_min one_pos hnlogB_pos) hSLfrac_pos
  have hM_le1 : M ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hM_le_nlogB : M ≤ -Real.log B := (min_le_left _ _).trans (min_le_right _ _)
  have hM_le_SLfrac : M ≤ simonLiebRate β J d / (2 * ((α : ℝ) + 1)) := min_le_right _ _
  have hMrate_sl : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2 := by
    calc ((α : ℝ) + 1) * M
        ≤ ((α : ℝ) + 1) * (simonLiebRate β J d / (2 * ((α : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hM_le_SLfrac (le_of_lt hαR_pos)
      _ = simonLiebRate β J d / 2 := by
          field_simp
  exact PseudoMassLatticeDistanceBridge_of_simonLieb_trichotomy_adjacent
    hα hr d hJ hβ hβJ_pos hβJd_pos (le_of_lt hβJd_lt1) hM_pos hM_le1 hMrate_sl
    (fun w _ =>
      correlationInfinite_latticeGraph_pair_le_exp_neg_of_high_temp hf hβJd_pos
        hβJd_half hM_le_nlogB w)

/-- **Unconditional HLS pair-product sum bound in the strict high-temperature
window** (§17.5, the B1 payoff).

For `1 ≤ α`, `0 < r`, `d < 2α`, ferromagnetic `⟨J,0,β⟩` with `0 < βJ` and
`0 < βJ·2d < 1/2`, and any anchors `x₀, y₀`,
`∃ K > 0, ∑'_z correlationInfinite {x₀,z}·correlationInfinite {y₀,z} ≤ K`,
with **no** adjacent-decay or pseudo-mass-bridge hypothesis. -/
theorem tsum_correlationInfinite_pair_product_le_const_of_high_temp
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_half : β * J * (2 * d) < 1 / 2)
    (x₀ y₀ : Fin d → ℤ) :
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z}
      ≤ K :=
  tsum_correlationInfinite_pair_product_le_HLS_const hα hr d hαd J β
    (pseudoMassLatticeDistanceBridge_of_high_temp hα hr d hJ hβ hβJ_pos hβJd_pos hβJd_half)
    x₀ y₀

/-- **Unconditional HLS sum at the diagonal anchor `(x₀, x₀)`** in the strict
high-temperature window (the `χ_∞(x₀)²`-type shape). -/
theorem tsum_correlationInfinite_pair_product_diagonal_le_const_of_high_temp
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_half : β * J * (2 * d) < 1 / 2)
    (x₀ : Fin d → ℤ) :
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z}
      ≤ K :=
  tsum_correlationInfinite_pair_product_le_const_of_high_temp
    hα hr d hαd hJ hβ hβJ_pos hβJd_pos hβJd_half x₀ x₀

end Ambient
end IsingModel
