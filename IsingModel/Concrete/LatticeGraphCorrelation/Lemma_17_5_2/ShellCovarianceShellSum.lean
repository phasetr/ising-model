import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.ShellCovarianceInfiniteVolume
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CubicUrsellShellSum

/-!
# Geometric bound on the cubic shell covariance sum (Issue #2965, Phase C)

Sums the per-edge bound `scaledCovariance_zero_edgeSpin_le_infiniteVolume_cross`
over the cut shell of the cubic exhaustion to obtain a geometric bound on the
localized shell term of the β-derivative increment.

For interior sites `x, z ∈ box_R` (`R ≤ k`, `x ≠ z`) lying on no cut edge, each
straddle edge `{u,v}` of the shell `box_{k+1} \ box_k` has a fresh endpoint
(`straddle_fresh_vertex`) whose infinite-volume correlation to the interior decays
geometrically (`correlationInfinite_fresh_le`), the partner factor being `≤ 1`. Hence

  `∑_{e∈shell} Cov_0(σ^{x,z}, σ_e) ≤ |shell| · 2·cf^{(k+1−R)/(r₀+2)}`,

`cf = contractionFactor < 1`. This is the **shell** (Part-B-type) contribution to the
per-stage β-derivative increment bound, mirroring the correlation-side
`ursell_shell_sum_le_card_pow`. Combined with `scaledCovariance_sum_right`
(`Cov_0(σ^A, ∑_e σ_e) = ∑_e Cov_0(σ^A, σ_e)`), it bounds the localized shell term
`J·Cov_0(σ^A, ∑_{E₀} σ_e)` of the β-derivative increment decomposition.

## Main declaration

* `IsingModel.Ambient.scaledCovariance_shell_sum_le_card_pow`.
-/

namespace IsingModel
namespace Ambient

open Finset

/-- **Geometric bound on the cubic shell covariance sum** (Issue #2965, Phase C).
For `d ≥ 1`, ferromagnetic `h=0`, high temperature (`cf < 1`), interior sites
`x, z ∈ box_R` (`R ≤ k`, `x ≠ z`) on no cut edge of the shell, the bond-deleted
(`s=0`) covariance sum of `σ^{x,z}` against the shell edge spins is geometric:
`∑_{e∈shell} Cov_0(σ^{x,z}, σ_e) ≤ |shell| · 2·cf^{(k+1−R)/(r₀+2)}`.

Each shell summand is bounded by the infinite-volume Lebowitz cross
(`scaledCovariance_zero_edgeSpin_le_infiniteVolume_cross`); for a straddle edge a
fresh endpoint carries the geometric decay (`straddle_fresh_vertex`,
`correlationInfinite_fresh_le`), the partner factor `≤ 1`. Mirrors
`ursell_shell_sum_le_card_pow`; this is the shell contribution to the per-stage
β-derivative increment bound. -/
theorem scaledCovariance_shell_sum_le_card_pow (d : ℕ) (hd : 1 ≤ d) (r₀ : ℕ) (hr₀ : 1 ≤ r₀)
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
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
        scaledCovariance (inducedGraph (latticeGraph d) (cubicBox d (k + 1)))
          ((inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
            (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1)))))
          (⟨J, 0, β⟩ : IsingParams ℝ) 0
          (spinProduct {⟨x, cubicBox_mono d (by omega) hx⟩,
            ⟨z, cubicBox_mono d (by omega) hz⟩})
          (fun σ => edgeSpin (K := ℝ) σ e)
      ≤ ((inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
          (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1))))).card •
        (2 * contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
          ((k + 1 - R) / (r₀ + 2))) := by
  set cf := contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀
  have hxk1 : x ∈ cubicBox d (k + 1) := cubicBox_mono d (by omega) hx
  have hzk1 : z ∈ cubicBox d (k + 1) := cubicBox_mono d (by omega) hz
  set E₀ := (inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset.filter
    (straddlePred ((cubicBox d k).subtype (· ∈ cubicBox d (k + 1)))) with hE₀
  have hE₀_sub : E₀ ⊆ (inducedGraph (latticeGraph d) (cubicBox d (k + 1))).edgeFinset :=
    Finset.filter_subset _ _
  have hE₀_nd : ∀ e ∈ E₀, ¬ e.IsDiag := fun e he =>
    (inducedGraph (latticeGraph d) (cubicBox d (k + 1))).not_isDiag_of_mem_edgeFinset
      (hE₀_sub he)
  have hle1 : ∀ a b : Fin d → ℤ,
      correlationInfinite (latticeGraph d) (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        {a, b} ≤ 1 :=
    fun a b => correlationInfinite_le_one _ _ _ _
  have hnn : ∀ m : ℕ, 0 ≤ cf ^ m := fun m => pow_nonneg
    (contractionFactor_nonneg d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      ⟨hJ, le_refl 0, hβ⟩ r₀) m
  apply Finset.sum_le_card_nsmul
  intro e he
  obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
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
  -- Bound the covariance summand by the infinite-volume cross product, then by `2·cf^_`.
  refine (scaledCovariance_zero_edgeSpin_le_infiniteVolume_cross d J β hJ hβ E₀
    hE₀_nd hE₀_sub ⟨x, hxk1⟩ ⟨z, hzk1⟩ u v hxzlift hxu hxv hzu hzv huv).trans ?_
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
