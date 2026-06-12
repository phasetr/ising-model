import IsingModel.Concrete.LatticeGraphCorrelation.CubicShellDecaySum
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CubicDerivativeProfileInfiniteVolume

/-!
# Geometric bound on the new-shell-edge Ursell sum (Issue #2965, Phase C)

The β-derivative increment formula `lemma_17_5_2_finite_derivative_increment_eq`
splits the stage-`(k+1)` Ursell edge sum into the interior edges (shared with stage
`k`) and the *new shell edges* of the `box_k`-slice. This module bounds the
new-shell-edge contribution geometrically: summing the per-edge Ursell bound
`ursell_cubic_le_infiniteVolume_cross` over the cut shell, each straddle edge has a
fresh endpoint `∈ box_{k+1} \ box_k` (`straddle_fresh_vertex`) whose infinite-volume
correlation to the interior sites `x, z` decays as `cf^{(k+1−R)/(r₀+2)}`
(`cf_pow_fresh_le` + the spatial decay), so the Ursell sum is at most
`|shell| · 2·cf^{(k+1−R)/(r₀+2)}` — geometric in the stage `k`.

This is the Part B (shell) contribution to the per-stage β-derivative increment
bound; it mirrors the correlation-side `derivBoundTight_cubic_shell_le_card_pow`.

## Main declaration

* `IsingModel.Ambient.ursell_shell_sum_le_card_pow`.
-/

namespace IsingModel
namespace Ambient

open Finset

/-- **Infinite-volume correlation to a fresh cubic vertex decays geometrically.**
For `x ∈ box_R`, a fresh vertex `w ∈ box_{k+1} \ box_k` (`R ≤ k`), and `cf < 1`, the
infinite-volume two-point function satisfies `g{x,w} ≤ cf^{(k+1−R)/(r₀+2)}`.
Composes the spatial decay
`correlationInfinite_latticeGraph_le_contractionFactor_pow_dist_pair`
(`g{x,w} ≤ cf^{dist/(r₀+2)}`, valid since `x ≠ w` as `x ∈ box_k` but `w ∉ box_k`)
with the fresh-vertex distance growth `cf_pow_fresh_le`. -/
theorem correlationInfinite_fresh_le (d : ℕ) (hd : 1 ≤ d) (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β)
    (hα : contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ < 1)
    (k R : ℕ) (hRk : R ≤ k) {x w : Fin d → ℤ} (hx : x ∈ cubicBox d R)
    (hw1 : w ∈ cubicBox d (k + 1)) (hw2 : w ∉ cubicBox d k) :
    correlationInfinite (latticeGraph d) (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {x, w}
      ≤ contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
          ((k + 1 - R) / (r₀ + 2)) := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  have hxw : x ≠ w := by
    intro h; subst h; exact hw2 (cubicBox_mono d hRk hx)
  exact (correlationInfinite_latticeGraph_le_contractionFactor_pow_dist_pair d hd r₀ hr₀
    (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) hf rfl hα hxw).trans
    (cf_pow_fresh_le (⟨J, 0, β⟩ : IsingParams ℝ) hf hα hx hRk hw1 hw2)

/-- **Geometric bound on the new-shell-edge Ursell sum** (Issue #2965, Phase C):
for `d ≥ 1`, ferromagnetic `h = 0`, high temperature (`cf < 1`), interior sites
`x, z ∈ box_R` (`R ≤ k`, `x ≠ z`) lying on no cut edge of the `box_k`-slice, the sum
of the stage-`(k+1)` Ursell summands over the cut shell is at most `|shell|` times
`2·cf^{(k+1−R)/(r₀+2)}`. Per straddle edge, `ursell_cubic_le_infiniteVolume_cross`
bounds the Ursell summand by the infinite-volume cross product, and the fresh
endpoint (`straddle_fresh_vertex`) carries the geometric decay
(`correlationInfinite_fresh_le`), the partner factor being `≤ 1`. Mirrors
`derivBoundTight_cubic_shell_le_card_pow`; this is the Part B (shell) contribution
to the per-stage β-derivative increment. -/
theorem ursell_shell_sum_le_card_pow (d : ℕ) (hd : 1 ≤ d) (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β)
    (hα : contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ < 1)
    (k R : ℕ) (hRk : R ≤ k) {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hx : x ∈ cubicBox d R) (hz : z ∈ cubicBox d R)
    (hsep : ∀ e ∈ (inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
        (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1)))),
      ¬ Sym2.Mem (⟨x, cubicBox_mono d (by omega) hx⟩ : (↑(cubicBox d (k + 1)) : Type _)) e ∧
        ¬ Sym2.Mem (⟨z, cubicBox_mono d (by omega) hz⟩ :
          (↑(cubicBox d (k + 1)) : Type _)) e) :
    ∑ e ∈ (inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
        (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1)))),
        Sym2.lift ⟨fun u v =>
          correlation (inducedGraph (latticeGraph d) (cubicBox d (k + 1)))
              (⟨J, 0, β⟩ : IsingParams ℝ)
              (symmDiff {⟨x, cubicBox_mono d (by omega) hx⟩,
                ⟨z, cubicBox_mono d (by omega) hz⟩} {u, v}) -
            correlation (inducedGraph (latticeGraph d) (cubicBox d (k + 1)))
                (⟨J, 0, β⟩ : IsingParams ℝ)
                {⟨x, cubicBox_mono d (by omega) hx⟩, ⟨z, cubicBox_mono d (by omega) hz⟩} *
              correlation (inducedGraph (latticeGraph d) (cubicBox d (k + 1)))
                (⟨J, 0, β⟩ : IsingParams ℝ) {u, v},
          fun u v => by simp [Finset.pair_comm v u]⟩ e
      ≤ ((inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
          (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1))))).card •
        (2 * contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
          ((k + 1 - R) / (r₀ + 2))) := by
  set cf := contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀
  have hxk1 : x ∈ cubicBox d (k + 1) := cubicBox_mono d (by omega) hx
  have hzk1 : z ∈ cubicBox d (k + 1) := cubicBox_mono d (by omega) hz
  have hle1 : ∀ a b : Fin d → ℤ,
      correlationInfinite (latticeGraph d) (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {a, b} ≤ 1 :=
    fun a b => correlationInfinite_le_one _ _ _ _
  apply Finset.sum_le_card_nsmul
  intro e he
  obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
  simp only [Sym2.lift_mk]
  obtain ⟨hxmem, hzmem⟩ := hsep _ he
  have hxu : (⟨x, hxk1⟩ : (↑(cubicBox d (k + 1)) : Type _)) ≠ u :=
    fun h => hxmem (Sym2.mem_iff.mpr (Or.inl h))
  have hxv : (⟨x, hxk1⟩ : (↑(cubicBox d (k + 1)) : Type _)) ≠ v :=
    fun h => hxmem (Sym2.mem_iff.mpr (Or.inr h))
  have hzu : (⟨z, hzk1⟩ : (↑(cubicBox d (k + 1)) : Type _)) ≠ u :=
    fun h => hzmem (Sym2.mem_iff.mpr (Or.inl h))
  have hzv : (⟨z, hzk1⟩ : (↑(cubicBox d (k + 1)) : Type _)) ≠ v :=
    fun h => hzmem (Sym2.mem_iff.mpr (Or.inr h))
  have hxzlift : (⟨x, hxk1⟩ : (↑(cubicBox d (k + 1)) : Type _)) ≠ ⟨z, hzk1⟩ := by
    simpa [Subtype.ext_iff] using hxz
  have huv : u ≠ v := by
    intro h; subst h
    exact (inducedGraph (latticeGraph d) (cubicBox d (k + 1))).not_isDiag_of_mem_edgeFinset
      (Finset.mem_of_mem_filter _ he) (Sym2.mk_isDiag_iff.mpr rfl)
  have hstr : straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1)))
      (Quot.mk (Sym2.Rel _) (u, v)) := (Finset.mem_filter.mp he).2
  -- Bound the Ursell summand by the infinite-volume cross product, then by `2·cf^_`.
  refine (ursell_cubic_le_infiniteVolume_cross d J β hJ hβ hxk1 hzk1 u v
    hxzlift hxu hxv hzu hzv huv).trans ?_
  have hnn : ∀ m : ℕ, 0 ≤ cf ^ m := fun m => pow_nonneg
    (contractionFactor_nonneg d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      ⟨hJ, le_refl 0, hβ⟩ r₀) m
  rcases straddle_fresh_vertex hstr with hfu | hfv
  · -- `u` is the fresh vertex
    have gxu := correlationInfinite_fresh_le d hd r₀ hr₀ J β hJ hβ hα k R hRk hx u.property hfu
    have gzu := correlationInfinite_fresh_le d hd r₀ hr₀ J β hJ hβ hα k R hRk hz u.property hfu
    calc correlationInfinite (latticeGraph d) (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              {x, u.val} *
            correlationInfinite (latticeGraph d) (cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {z, v.val} +
          correlationInfinite (latticeGraph d) (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              {x, v.val} *
            correlationInfinite (latticeGraph d) (cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {z, u.val}
        ≤ cf ^ ((k + 1 - R) / (r₀ + 2)) * 1 + 1 * cf ^ ((k + 1 - R) / (r₀ + 2)) :=
          add_le_add
            (mul_le_mul gxu (hle1 z v.val)
              (correlationInfinite_nonneg _ _ _ ⟨hJ, le_refl 0, hβ⟩ _) (hnn _))
            (mul_le_mul (hle1 x v.val) gzu
              (correlationInfinite_nonneg _ _ _ ⟨hJ, le_refl 0, hβ⟩ _) zero_le_one)
      _ = 2 * cf ^ ((k + 1 - R) / (r₀ + 2)) := by ring
  · -- `v` is the fresh vertex
    have gxv := correlationInfinite_fresh_le d hd r₀ hr₀ J β hJ hβ hα k R hRk hx v.property hfv
    have gzv := correlationInfinite_fresh_le d hd r₀ hr₀ J β hJ hβ hα k R hRk hz v.property hfv
    calc correlationInfinite (latticeGraph d) (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              {x, u.val} *
            correlationInfinite (latticeGraph d) (cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {z, v.val} +
          correlationInfinite (latticeGraph d) (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              {x, v.val} *
            correlationInfinite (latticeGraph d) (cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {z, u.val}
        ≤ 1 * cf ^ ((k + 1 - R) / (r₀ + 2)) + cf ^ ((k + 1 - R) / (r₀ + 2)) * 1 :=
          add_le_add
            (mul_le_mul (hle1 x u.val) gzv
              (correlationInfinite_nonneg _ _ _ ⟨hJ, le_refl 0, hβ⟩ _) zero_le_one)
            (mul_le_mul gxv (hle1 z u.val)
              (correlationInfinite_nonneg _ _ _ ⟨hJ, le_refl 0, hβ⟩ _) (hnn _))
      _ = 2 * cf ^ ((k + 1 - R) / (r₀ + 2)) := by ring

end Ambient
end IsingModel
