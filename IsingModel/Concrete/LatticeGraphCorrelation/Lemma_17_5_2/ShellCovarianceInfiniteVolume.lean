import IsingModel.Concrete.LatticeGraphCorrelation.CubicShellInfiniteVolumeBound
import IsingModel.ScaledBetaDerivative

/-!
# Cubic shell covariance bounded by the infinite-volume Lebowitz cross (Issue #2965, Phase C)

Specializes the abstract per-edge shell-term bound
`scaledCovariance_zero_edgeSpin_le_lebowitz_full` to the cubic exhaustion: on the
induced lattice graph over a cubic box, the bond-deleted (`s=0`) covariance of
`σ^{x,z}` with a cut-edge spin `σ_uσ_v` is bounded by the **infinite-volume**
Lebowitz cross
`g{x,u}·g{z,v} + g{x,v}·g{z,u}` (`g = correlationInfinite`).

This composes the full-graph bound `scaledCovariance_zero_edgeSpin_le_lebowitz_full`
with the finite-to-infinite bridge `correlation_inducedGraph_cubic_le_correlationInfinite`,
exactly mirroring the correlation-side `ursell_cubic_le_infiniteVolume_cross`. Since the
infinite-volume cross products decay in the distance from the interior sites `x, z` to a
fresh cut vertex (Phase B spatial decay), summing over the cubic shell yields a geometric
bound on the localized shell term `J·∑_{e∈E₀} Cov_0(σ^{x,z}, σ_e)` of the β-derivative
increment, reusing the correlation-side Part-B machinery
(`correlationInfinite_fresh_le`, `ursell_shell_sum_le_card_pow`).

## Main declaration

* `IsingModel.Ambient.scaledCovariance_zero_edgeSpin_le_infiniteVolume_cross`.
-/

namespace IsingModel
namespace Ambient

/-- **Cubic shell covariance bounded by the infinite-volume Lebowitz cross**
(Issue #2965, Phase C). On the induced lattice graph over the cubic box
`(cubicExhaustion d).volume n`, for ferromagnetic `h=0` and four distinct box
vertices `x, z, u, v`, the bond-deleted (`s=0`) covariance of `σ^{x,z}` with the
cut-edge spin `σ_uσ_v` is bounded by the infinite-volume Lebowitz cross
`g{x,u}·g{z,v} + g{x,v}·g{z,u}` (`g = correlationInfinite`).

Composes the abstract full-graph bound
`scaledCovariance_zero_edgeSpin_le_lebowitz_full` (per-edge covariance ≤ full-graph
Lebowitz cross, via GKS bond-monotonicity) with the finite-to-infinite bridge
`correlation_inducedGraph_cubic_le_correlationInfinite`, mirroring the
correlation-side `ursell_cubic_le_infiniteVolume_cross`. For a cut edge `{u,v}`
straddling the shell, a fresh endpoint carries the infinite-volume spatial decay, so
the per-edge summand of the localized shell term decays geometrically. -/
theorem scaledCovariance_zero_edgeSpin_le_infiniteVolume_cross (d : ℕ) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) {n : ℕ}
    (E₀ : Finset (Sym2 (↑((cubicExhaustion d).volume n) : Type _)))
    (hE₀_nd : ∀ e ∈ E₀, ¬ e.IsDiag)
    (hE₀_sub : E₀ ⊆ (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).edgeFinset)
    (x z u v : (↑((cubicExhaustion d).volume n) : Type _)) (hxz : x ≠ z) (hxu : x ≠ u)
    (hxv : x ≠ v) (hzu : z ≠ u) (hzv : z ≠ v) (huv : u ≠ v) :
    scaledCovariance (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)) E₀
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 (spinProduct {x, z})
        (fun σ => edgeSpin (K := ℝ) σ (Quot.mk _ (u, v)))
      ≤ correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x.val, u.val} *
          correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {z.val, v.val} +
        correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x.val, v.val} *
          correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {z.val, u.val} := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  refine (scaledCovariance_zero_edgeSpin_le_lebowitz_full
    (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)) E₀ hE₀_nd hE₀_sub
    J β hJ hβ x z hxz hxu hxv hzu hzv huv).trans ?_
  have bxu := correlation_inducedGraph_cubic_le_correlationInfinite d
    (⟨J, 0, β⟩ : IsingParams ℝ) n x u
  have bzv := correlation_inducedGraph_cubic_le_correlationInfinite d
    (⟨J, 0, β⟩ : IsingParams ℝ) n z v
  have bxv := correlation_inducedGraph_cubic_le_correlationInfinite d
    (⟨J, 0, β⟩ : IsingParams ℝ) n x v
  have bzu := correlation_inducedGraph_cubic_le_correlationInfinite d
    (⟨J, 0, β⟩ : IsingParams ℝ) n z u
  exact add_le_add
    (mul_le_mul bxu bzv (gks_first _ _ hf _) (correlationInfinite_nonneg _ _ _ hf _))
    (mul_le_mul bxv bzu (gks_first _ _ hf _) (correlationInfinite_nonneg _ _ _ hf _))

end Ambient
end IsingModel
