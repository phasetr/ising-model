import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CapstoneIncrementFromComplexBound
import IsingModel.AmbientComplexAnalyticity.VolumeUniformHZ

/-!
# Lemma 17.5.2: conditional capstone via the CE route (centred at `β = 0`)

This module composes the volume-uniform `Z_ℂ ≠ 0` bridge from
`AmbientComplexAnalyticity/VolumeUniformHZ.lean` (Issue #3054) with the
capstone-coordinate conditional reduction
`dist_deriv_correlationAlongExhaustion_le_of_complex_circle_bound` (PR #3032,
`CapstoneIncrementFromComplexBound.lean`) to produce the Lemma 17.5.2
β-derivative increment bound at the centred parameter `β = 0`.

The composition takes three structural inputs:

1. `VolumeUniformZComplexIdentity (latticeGraph d) Λ J` — the polymer
   high-temperature factorisation holds on a uniform complex disc across all
   stages.
2. `VolumeUniformComplexHTBound (latticeGraph d) Λ J` — the polymer-expansion
   RHS norm is bounded below uniformly across stages.
3. A volume-uniform complex circle bound `B` on the value increment for the
   relevant pair `{x, z}` (the `hB` input to #3032).

The result is the increment bound `dist(∂_β c_k, ∂_β c_{k+1}) ≤ B/R` at
`β = 0` for every covered stage `k`, the per-stage scalar input to the
Lemma 17.5.2 capstone increment infrastructure.

The two volume-uniform CE inputs (1)-(2) remain open (complex cluster-expansion
convergence, research-level); a centred circle bound on the correlation value
increment (3) is the parallel open input from the Simon-Lieb hB side
(Issue #3044).
-/

namespace IsingModel
namespace Ambient

open Complex Metric

/-- **Lemma 17.5.2 conditional dist-increment via the CE route at `β = 0`**
(Issue #3054). Composes the volume-uniform `Z_ℂ ≠ 0` bridge
`partitionFunctionComplex_inducedGraph_ne_zero_on_ball_at_zero_of_volume_uniform`
with the capstone-coordinate conditional reduction
`dist_deriv_correlationAlongExhaustion_le_of_complex_circle_bound` (PR #3032).

For each covered stage `k` (containing `{x, z}`), given a complex circle bound
`B` on the correlation value increment on the sphere `Metric.sphere (0:ℂ) R`,
the consecutive β-derivative increment is bounded by `B / R` at `β = 0`. The
volume-uniform structural inputs deliver a single `R > 0` independent of `k`,
matching the volume-uniform `hZk` / `hZk1` hypotheses of #3032.

The complementary input `hB` (volume-uniform circle bound) is the open
parallel input from Issue #3044 (complex Simon-Lieb / hB provider). -/
theorem dist_deriv_correlationAlongExhaustion_le_at_zero_beta_of_volume_uniform
    {d : ℕ} (Λ : Exhaustion (Fin d → ℤ))
    [hinst : ∀ n, Fintype
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ) (k : ℕ)
    (hHT : VolumeUniformComplexHTBound (IsingModel.latticeGraph d) Λ J)
    (hid : VolumeUniformZComplexIdentity (IsingModel.latticeGraph d) Λ J)
    (hk : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume k) :
    ∃ R > 0, ∀ {B : ℝ} (_hB : ∀ w ∈ Metric.sphere ((0 : ℝ) : ℂ) R,
        ‖correlationComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume k))
              (Ambient.liftFinset {x, z} hk) (J : ℂ) (0 : ℂ) w -
            correlationComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ.volume (k + 1)))
              (Ambient.liftFinset {x, z} (hk.trans (Λ.mono (Nat.le_succ k))))
              (J : ℂ) (0 : ℂ) w‖ ≤ B),
      dist
        (deriv (fun β : ℝ => Ambient.correlationAlongExhaustion
          (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ {x, z} k) 0)
        (deriv (fun β : ℝ => Ambient.correlationAlongExhaustion
          (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ {x, z} (k + 1)) 0)
        ≤ B / R := by
  -- Extract a single volume-uniform disc radius `R > 0` from the bridges.
  obtain ⟨R, hR, hne⟩ :=
    Ambient.partitionFunctionComplex_inducedGraph_ne_zero_on_ball_at_zero_of_volume_uniform
      (IsingModel.latticeGraph d) Λ J hHT hid
  -- Re-express the closedBall (0 : ℂ) R as closedBall ((0 : ℝ) : ℂ) R.
  have h_coe : ((0 : ℝ) : ℂ) = (0 : ℂ) := Complex.ofReal_zero
  refine ⟨R, hR, ?_⟩
  intro B hB
  refine dist_deriv_correlationAlongExhaustion_le_of_complex_circle_bound
    Λ J x z k (β := 0) (R := R) (B := B) hR hk ?_ ?_ ?_
  · -- `hZk` slot: Z_ℂ ≠ 0 on closedBall ((0:ℝ):ℂ) R at stage k.
    intro w hw
    rw [h_coe] at hw
    exact hne k w hw
  · -- `hZk1` slot: Z_ℂ ≠ 0 on closedBall ((0:ℝ):ℂ) R at stage k+1.
    intro w hw
    rw [h_coe] at hw
    exact hne (k + 1) w hw
  · -- `hB` slot: forwarded directly from the caller.
    exact hB

end Ambient
end IsingModel
