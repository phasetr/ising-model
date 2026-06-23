import IsingModel.AmbientComplexAnalyticity.VolumeUniformZIdentity
import IsingModel.ClusterExpansion.MayerCore.ComplexMayerMontroll
import IsingModel.ClusterExpansion.HighTempKoteckyPreiss
import IsingModel.ClusterExpansion.HighTempAnalyticityCapstone

/-!
# Volume-uniform complex `Z` non-vanishing on `ℤ^d` (GJ §18.4–18.6)

Discharges the volume-uniform partition non-vanishing `hZ` consumed by the infinite-volume
correlation-analyticity assembly
(`correlationComplexAlongExhaustion_analytic_of_volume_uniform_bound`,
PR #4235), at zero field for the lattice (Issue #4230, item D of #4214).

The argument is **direct**, bypassing any norm lower bound.  The complex `Z` factorizes
(`volumeUniformZComplexIdentity_of_forall`, PR #4236) as
`Z_ℂ = 2^{|V_n|}·cosh(βJ)^{|E_n|}·∑_Γ ∏_P tanh(βJ)^{|P|}`, and by the complex
Mayer–Montroll identity
(`vdPolymerFamilies_sum_pow_eq_exp_tsum_mayerExpansionTermComplex`, PR #4237) the polymer
sum equals `exp(∑ mayerExpansionTermComplex …)`, which is **never zero**.  Together with
`cosh(βJ) ≠ 0` on the `cosh`-disc and `2 ≠ 0`, all three factors are nonzero, so `Z_ℂ ≠ 0`
— uniformly in the exhaustion
stage `n`, on a single `n`-independent disc.

## Main result
* `partitionFunctionComplexAlongExhaustion_ne_zero_on_ball_uniform_latticeGraph` — `∃ r > 0`
  such that the along-exhaustion complex partition function is nonvanishing on `Metric.ball 0 r`
  for every stage `n`.

This is the volume-uniform `hZ` of #4235.  The only remaining Ising hypothesis for unconditional
infinite-volume correlation analyticity is then the volume-uniform correlation bound `hbdd`.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §18.4–18.6.
-/

namespace IsingModel

namespace Ambient

open Filter Topology

/-- **Volume-uniform complex `Z` non-vanishing on `ℤ^d`** (GJ §18.4–18.6): for the lattice at
zero field, there is a single radius `r > 0` such that the along-exhaustion complex partition
function is nonvanishing on `Metric.ball 0 r` for *every* exhaustion stage `n`.

Direct proof via the factorization
`Z_ℂ = 2^{|V_n|}·cosh(βJ)^{|E_n|}·∑_Γ ∏_P tanh(βJ)^{|P|}`
(`volumeUniformZComplexIdentity_of_forall`) and the complex Mayer–Montroll identity (the
polymer sum equals `exp(…) ≠ 0`): all three factors are nonzero (`2 ≠ 0`; `cosh(βJ) ≠ 0` on
the `cosh`-disc;
`Complex.exp_ne_zero`). -/
theorem partitionFunctionComplexAlongExhaustion_ne_zero_on_ball_uniform_latticeGraph
    (d : ℕ) (Λ : Exhaustion (Fin d → ℤ)) (J : ℝ) :
    ∃ r > 0, ∀ n : ℕ, ∀ β ∈ Metric.ball (0 : ℂ) r,
      partitionFunctionComplexAlongExhaustion (latticeGraph d) Λ (J : ℂ) 0 β n ≠ 0 := by
  classical
  -- the `(2d)`-Kotecký–Preiss radius `R = kpRadius d`
  set R : ℝ := kpRadius d with hRdef
  have hR : 0 < R := kpRadius_pos d
  have hKPlt : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1 / 6 := kpRadius_threshold d
  obtain ⟨hkp2d, hρ2d⟩ := kp_tail_conditions_of_lt hKPlt
  -- the volume-uniform polymer factorization radius `r₁`
  obtain ⟨r₁, hr₁, hId⟩ := volumeUniformZComplexIdentity_of_forall (latticeGraph d) Λ J
  -- the `n`-independent `cosh`-disc `ball 0 ρ`
  have h_cosh0 : Complex.cosh ((0 : ℂ) * (J : ℂ)) ≠ 0 := by
    rw [zero_mul, Complex.cosh_zero]; exact one_ne_zero
  have h_cosh_ev : ∀ᶠ β : ℂ in 𝓝 (0 : ℂ), Complex.cosh (β * (J : ℂ)) ≠ 0 :=
    (Complex.continuous_cosh.comp (continuous_id.mul continuous_const)).continuousAt.eventually_ne
      h_cosh0
  rw [Metric.eventually_nhds_iff_ball] at h_cosh_ev
  obtain ⟨ρ, hρpos, h_cosh_ne⟩ := h_cosh_ev
  -- the radius `rt` on which `‖tanh(βJ)‖ < R`
  have h_tanh0 : Complex.tanh ((0 : ℂ) * (J : ℂ)) = 0 := by
    rw [zero_mul, Complex.tanh_zero]
  have h_tanh_cont : ContinuousAt (fun β : ℂ => Complex.tanh (β * (J : ℂ))) 0 := by
    have hsinh : ContinuousAt (fun β : ℂ => Complex.sinh (β * (J : ℂ))) 0 :=
      (Complex.continuous_sinh.comp (continuous_id.mul continuous_const)).continuousAt
    have hcosh : ContinuousAt (fun β : ℂ => Complex.cosh (β * (J : ℂ))) 0 :=
      (Complex.continuous_cosh.comp (continuous_id.mul continuous_const)).continuousAt
    have hdiv : ContinuousAt
        (fun β : ℂ => Complex.sinh (β * (J : ℂ)) / Complex.cosh (β * (J : ℂ))) 0 :=
      hsinh.div hcosh h_cosh0
    exact hdiv
  have h_tanh_ev : ∀ᶠ β : ℂ in 𝓝 (0 : ℂ), ‖Complex.tanh (β * (J : ℂ))‖ < R := by
    have htend : Filter.Tendsto (fun β : ℂ => ‖Complex.tanh (β * (J : ℂ))‖)
        (𝓝 0) (𝓝 0) := by
      have h2 := h_tanh_cont.norm.tendsto
      rwa [h_tanh0, norm_zero] at h2
    exact htend.eventually (gt_mem_nhds hR)
  rw [Metric.eventually_nhds_iff_ball] at h_tanh_ev
  obtain ⟨rt, hrtpos, h_tanh_lt⟩ := h_tanh_ev
  -- the common radius
  refine ⟨min r₁ (min ρ rt), lt_min hr₁ (lt_min hρpos hrtpos), ?_⟩
  intro n β hβ
  have hβr : dist β 0 < min r₁ (min ρ rt) := Metric.mem_ball.mp hβ
  have hβId : β ∈ Metric.closedBall (0 : ℂ) r₁ :=
    Metric.mem_closedBall.mpr (le_of_lt (lt_of_lt_of_le hβr (min_le_left _ _)))
  have hβρ : β ∈ Metric.ball (0 : ℂ) ρ :=
    Metric.mem_ball.mpr (lt_of_lt_of_le hβr (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hβt : β ∈ Metric.ball (0 : ℂ) rt :=
    Metric.mem_ball.mpr (lt_of_lt_of_le hβr (le_trans (min_le_right _ _) (min_le_right _ _)))
  set G' : SimpleGraph (↑(Λ.volume n) : Type _) := inducedGraph (latticeGraph d) (Λ.volume n)
    with hG'
  -- the polymer activity `z = tanh(βJ)` lies in the KP ball
  have hz : Complex.tanh (β * (J : ℂ)) ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]; exact h_tanh_lt β hβt
  -- discharge the `G'`-KP hypotheses from the `(2d)`-KP ones (`maxDegree ≤ 2d`)
  have hdeg : G'.maxDegree ≤ 2 * d := induced_latticeGraph_maxDegree_le d (Λ.volume n)
  have hcast : (G'.maxDegree : ℝ) ≤ ((2 * d : ℕ) : ℝ) := by exact_mod_cast hdeg
  have heR : (0 : ℝ) ≤ Real.exp 1 * R := by positivity
  have h0 : (0 : ℝ) ≤ (G'.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R) := by positivity
  have h12 : (G'.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R)
      ≤ ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) := by gcongr
  obtain ⟨hkpG', hρG'⟩ := kpRegion_downward_closed h0 h12 hkp2d hρ2d
  -- the polymer sum equals an exponential, hence is nonzero
  have hsum := vdPolymerFamilies_sum_pow_eq_exp_tsum_mayerExpansionTermComplex G' hR hkpG' hρG' hz
  rw [hId n β hβId, hsum]
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ ?_) (pow_ne_zero _ (h_cosh_ne β hβρ)))
    (Complex.exp_ne_zero _)
  norm_num

end Ambient

end IsingModel
