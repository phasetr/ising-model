import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityDerivCombineUniform
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.UnconditionalFiniteRegionLipschitz
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.LebowitzAlongExhaustion

/-!
# GJ §17.5 Theorem 17.5.1 — PR-1j: the sharp infinite-volume β-derivative bound (p.312)

The `n → ∞` limit of the n-uniform finite-stage β-derivative bound (#4358), giving the GJ p.312
bound on the **infinite-volume** correlation β-derivative:
`|∂_β ⟨φ_x φ_z⟩^∞| ≤ ⟨sharp(C)⟩ · ⟨φ_x φ_z⟩^∞`,
where `⟨sharp(C)⟩ = J·[2(1+(m⁻r)^α)e^{m⁻}C(1+r)^{−(2α−d)}] + J·[4d(1+2^α)e^{m⁻}]`.

The finite-stage deriv is non-negative (GKS-II) and `≤ c·⟨sharp(C)⟩` (#4358); the limit
(`derivativeLimit_on_window` +
`correlationInfinite_hasDerivAt_beta_…`) transfers both to the infinite-volume derivative.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real Filter

/-- **Sharp infinite-volume β-derivative bound** (GJ p.312): for a non-adjacent binding pair `x ≠ z`
with `m⁻(x,z)=globalPseudoMassDist>0` at `β ∈ window`,
`∃ C>0, |∂_β ⟨φ_x φ_z⟩^∞| ≤ ⟨sharp(C)⟩·⟨φ_x φ_z⟩^∞`, the GJ p.312 derivative-ratio bound on the
infinite-volume two-point function.  `n→∞` limit of #4358: the finite-stage deriv is in
`[0, c·⟨sharp⟩]` (GKS-II monotonicity + #4358), so the limit `∂_β c^∞` is bounded in absolute value
by `c·⟨sharp⟩`. -/
theorem abs_deriv_correlationInfinite_le_sharp {α d : ℕ} (hα : 1 ≤ α) (hd : 1 ≤ d)
    (hαd : d < 2 * α) (hαd2 : α < d) {J β : ℝ} (hJ : 0 < J)
    (hβ_win : β ∈ ConvergenceRegion.window d J)
    {x z : Fin d → ℤ} (hxz : x ≠ z) (hxz_nonadj : ¬ (latticeGraph d).Adj x z)
    (hm_pos : 0 < globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ))
    (hbind : pseudoMassFromParamsAtPairDist hα (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      = globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)) :
    ∃ C : ℝ, 0 < C ∧
      |deriv (fun β' => correlationInfinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}) β|
      ≤ (J * (2 * (1 + (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              * (latticeDistance d x z : ℝ)) ^ α)
            * Real.exp (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ))
            * (C * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ)))))
          + J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α)
              * Real.exp (globalPseudoMassDist hα (cubicExhaustion d)
                  (⟨J, 0, β⟩ : IsingParams ℝ)))))
        * correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} := by
  classical
  have hβ_pos : 0 < β := (ConvergenceRegion.window_subset_highTemp d J hJ hd hβ_win).1
  have hc_pos : 0 < correlationInfinite (latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} :=
    (correlationInfinite_pair_active_of_betaJ_pos_exhaustion
      (cubicExhaustion d) hβ_pos (mul_pos hβ_pos hJ) x z hxz).1
  obtain ⟨C, hC, hbd⟩ :=
    combined_derivative_div_c_bound_tight_uniform hα hd hαd hαd2 hJ hβ_pos hxz hxz_nonadj hm_pos
      hbind
  refine ⟨C, hC, ?_⟩
  -- the infinite-volume derivative is the limit `g' β`.
  obtain ⟨g', hderiv_lim⟩ :=
    ConvergenceRegion.derivativeLimit_on_window d J (cubicExhaustion d) hJ hxz
  have hHasDeriv : HasDerivAt (fun β' => correlationInfinite (latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}) (g' β) β :=
    correlationInfinite_hasDerivAt_beta_of_tendstoLocallyUniformlyOn_deriv
      hd (cubicExhaustion d) x z hxz J hJ g' isOpen_Ioo
      (ConvergenceRegion.window_subset_highTemp d J hJ hd) hderiv_lim β hβ_win
  rw [hHasDeriv.deriv]
  set S : ℝ := (J * (2 * (1 + (globalPseudoMassDist hα (cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) * (latticeDistance d x z : ℝ)) ^ α)
          * Real.exp (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ))
          * (C * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ)))))
        + J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α)
            * Real.exp (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)))))
    with hS_def
  -- pointwise tendsto of the finite-stage derivatives to `g' β`.
  have hpoint : Tendsto (fun n => deriv (fun β' =>
      correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β) atTop (nhds (g' β)) :=
    hderiv_lim.tendsto_at hβ_win
  -- eventually `|deriv(stage n) β| ≤ S · c`.
  have hev : ∀ᶠ n in atTop, |deriv (fun β' =>
      correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β|
      ≤ S * correlationInfinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} := by
    obtain ⟨N, hN⟩ := (cubicExhaustion d).exhaust ({x, z} : Finset (Fin d → ℤ))
    refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have hsub : ({x, z} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n := hN n hn
    have hnn : 0 ≤ deriv (fun β' =>
        correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β :=
      correlationAlongExhaustion_latticeGraph_beta_deriv_nonneg
        (cubicExhaustion d) J β hJ.le hβ_pos {x, z} n
    rw [abs_of_nonneg hnn]
    have hupper := hbd n hsub
    rwa [div_le_iff₀ hc_pos] at hupper
  exact le_of_tendsto ((continuous_abs.tendsto (g' β)).comp hpoint) hev

end Ambient
end IsingModel
