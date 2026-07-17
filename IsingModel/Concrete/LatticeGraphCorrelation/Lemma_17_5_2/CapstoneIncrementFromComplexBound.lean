import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CorrelationAlongExhaustionDeriv
import IsingModel.Concrete.LatticeGraphCorrelation.Regularity
import IsingModel.Lattice
import IsingModel.ComplexAnalyticity.Correlation
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CauchyDerivativeBridge

/-!
# Capstone per-stage β-derivative increment from complex inputs (Issue #3026)

Assembles the Cauchy-estimate route into the exact per-stage shape of the GJ §17.5
Lemma 17.5.2 capstone `hincr`: for consecutive covered exhaustion stages `k, k+1`,
the β-derivative increment of the exhaustion correlation is bounded by `B / R`, where
`R` is the radius of a complex disc on which both finite-volume partition functions are
zero-free and `B` bounds the complex correlation value increment on the boundary circle:
`dist(∂_β c_k, ∂_β c_{k+1}) ≤ B / R`.

This is the conditional reduction feeding
`lemma_17_5_2_derivative_limit_provider_of_poly_geometric_increments_on_covered_stages`
(`IncrementCapstone.lean`): once a stage-uniform zero-free radius `R` and a
`poly·geometric` boundary bound `B` are supplied (the remaining complex/Lee-Yang-region
hard core), the full Lemma 17.5.2 upper bound / sandwich follows.

References:

* Glimm–Jaffe, *Quantum Physics* (2nd ed.), §17.5, Lemma 17.5.2, pp. 311–312.
-/

namespace IsingModel
namespace Ambient

open Complex Metric

/-- **Capstone per-stage β-derivative increment from complex inputs** (Issue #3026).
For a lattice exhaustion `Λ`, a real coupling `J`, a pair `{x, z}` covered at stage `k`
(coverage at `k+1` follows by exhaustion monotonicity), and a real inverse temperature
`β`: if both finite-volume complex partition
functions (on the induced graphs over `Λ.volume k` and `Λ.volume (k+1)`) are nonzero on
the closed disc `closedBall β R` (`R > 0`), and the complex correlation value increment is
bounded by `B` on the boundary circle `sphere β R`, then `dist(∂_β c_k, ∂_β c_{k+1}) ≤
B / R`, where `c_k = correlationAlongExhaustion … k`.

Rewrites the exhaustion-correlation derivatives into induced-graph correlation derivatives
(`deriv_correlationAlongExhaustion_eq_inducedGraph`) and applies the Cauchy-estimate
derivative bridge `dist_deriv_le_of_complex_extension` to the two complex correlation
extensions (on `box_k` and `box_{k+1}`), whose difference is `DiffContOnCl` on the disc.
The finite-volume edge-set `Fintype` instances are the global computed ones (from
`DecidableRel (latticeGraph d).Adj`), matching the capstone's
`correlationAlongExhaustion` instances, so instance resolution stays coherent. -/
theorem dist_deriv_correlationAlongExhaustion_le_of_complex_circle_bound {d : ℕ}
    (Λ : Exhaustion (Fin d → ℤ))
    [hinst : ∀ n, Fintype (inducedGraph (latticeGraph d) (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ) (k : ℕ) (β : ℝ) {R B : ℝ} (hR : 0 < R)
    (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k)
    (hZk : ∀ w ∈ closedBall (β : ℂ) R,
      partitionFunctionComplex (inducedGraph (latticeGraph d) (Λ.volume k))
        (J : ℂ) (0 : ℂ) w ≠ 0)
    (hZk1 : ∀ w ∈ closedBall (β : ℂ) R,
      partitionFunctionComplex (inducedGraph (latticeGraph d) (Λ.volume (k + 1)))
        (J : ℂ) (0 : ℂ) w ≠ 0)
    (hB : ∀ w ∈ sphere (β : ℂ) R,
      ‖correlationComplex (inducedGraph (latticeGraph d) (Λ.volume k))
            (liftFinset {x, z} hk) (J : ℂ) (0 : ℂ) w -
          correlationComplex (inducedGraph (latticeGraph d) (Λ.volume (k + 1)))
            (liftFinset {x, z} (hk.trans (Λ.mono (Nat.le_succ k)))) (J : ℂ) (0 : ℂ) w‖ ≤ B) :
    dist (deriv (fun β' =>
            correlationAlongExhaustion (latticeGraph d) Λ (⟨J, 0, β'⟩ : IsingParams ℝ)
              {x, z} k) β)
        (deriv (fun β' =>
            correlationAlongExhaustion (latticeGraph d) Λ (⟨J, 0, β'⟩ : IsingParams ℝ)
              {x, z} (k + 1)) β) ≤ B / R := by
  -- Coverage at stage `k+1` follows from coverage at `k` by exhaustion monotonicity.
  have hk1 : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume (k + 1) :=
    hk.trans (Λ.mono (Nat.le_succ k))
  rw [deriv_correlationAlongExhaustion_eq_inducedGraph (latticeGraph d) Λ J 0 {x, z} k hk,
    deriv_correlationAlongExhaustion_eq_inducedGraph (latticeGraph d) Λ J 0 {x, z} (k + 1) hk1]
  -- Real-part agreement of a complex correlation extension (at `h = 0`) with the real
  -- correlation, with the edge-set `Fintype` instance pinned explicitly.
  have key : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : SimpleGraph ι)
      (instΓ : Fintype Γ.edgeSet) (S : Finset ι) (x' : ℝ),
      (@correlationComplex ι _ _ Γ instΓ S (J : ℂ) (0 : ℂ) (x' : ℂ)).re
        = @correlation ι _ _ Γ instΓ (⟨J, 0, x'⟩ : IsingParams ℝ) S := by
    intro ι _ _ Γ instΓ S x'
    have hofr := @correlation_ofReal_eq_correlationComplex ι _ _ Γ instΓ
      (⟨J, 0, x'⟩ : IsingParams ℝ) S
    rw [Complex.ofReal_zero] at hofr
    rw [← hofr, Complex.ofReal_re]
  refine dist_deriv_le_of_complex_extension hR ?_ ?_ ?_ ?_ hB
  · -- differentiability of `c_k` via the existing real β-derivative of `correlationΛ`
    obtain ⟨_, hc⟩ := @hasDerivAt_correlationΛ_latticeGraph_beta d (Λ.volume k) (hinst k) J β
      (liftFinset {x, z} hk)
    exact hc.differentiableAt
  · obtain ⟨_, hc⟩ := @hasDerivAt_correlationΛ_latticeGraph_beta d (Λ.volume (k + 1))
      (hinst (k + 1)) J β (liftFinset {x, z} hk1)
    exact hc.differentiableAt
  · intro x'
    rw [Complex.sub_re, key _ (hinst k) _ x', key _ (hinst (k + 1)) _ x']
  · exact (@correlationComplex_diffContOnCl_beta _ _ _
        (inducedGraph (latticeGraph d) (Λ.volume k)) (hinst k) (liftFinset {x, z} hk)
        (J : ℂ) (0 : ℂ) (β : ℂ) R hR hZk).sub
      (@correlationComplex_diffContOnCl_beta _ _ _
        (inducedGraph (latticeGraph d) (Λ.volume (k + 1))) (hinst (k + 1))
        (liftFinset {x, z} hk1) (J : ℂ) (0 : ℂ) (β : ℂ) R hR hZk1)

end Ambient
end IsingModel
