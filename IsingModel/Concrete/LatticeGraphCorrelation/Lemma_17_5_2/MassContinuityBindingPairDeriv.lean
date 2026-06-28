import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityDerivInfiniteSharp
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsRegularity
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.FiniteRegionPseudoMassDistLipschitz

/-!
# GJ §17.5 Theorem 17.5.1 — PR-B1: pointwise per-binding-pair pseudo-mass-power derivative bound

The pointwise derivative bound on `β ↦ (m⁻(x,z,β))^{2α+1}` *at a globally-binding pair* (p.~312).
The sharp infinite-volume correlation derivative bound `|∂_β c| ≤ S·c` (#4359) is fed — through the
per-pair power-chain consumer
`pseudoMassFromParamsAtPair_beta_pow_succ_deriv_bound_of_corr_hasDerivAt` with
`K = S·(m⁻)^{2α}` (so `K·c/(m⁻)^{2α} = S·c`) — into a pointwise `HasDerivAt` for the pseudo-mass
power with `|deriv| ≤ (2α+1)·S·(m⁻)^{2α}/d(x,z)`.

This is the per-point ingredient consumed by the lower-envelope fencing lemma
`abs_sub_le_of_isInf_binding_deriv` (PR-A) to make the system pseudo-mass `m⁻(β) = inf over pairs`
itself Lipschitz; the binding hypothesis `m⁻(x,z) = globalPseudoMassDist` is exactly the
*pinning* required by the fencing argument (cf. #4320).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real Filter

/-- **Pointwise per-binding-pair pseudo-mass-power derivative bound** (GJ p.312): for a non-adjacent
binding pair `x ≠ z` (`m⁻(x,z) = globalPseudoMassDist > 0`) at `β ∈ window`, the per-pair
pseudo-mass power `β' ↦ (m⁻(x,z,β'))^{2α+1}` is differentiable at `β` with
`|deriv| ≤ (2α+1)·S·(m⁻)^{2α}/d(x,z)`, where `S` is the sharp p.312 correlation-derivative
coefficient (#4359) and `m⁻ = globalPseudoMassDist`.

Feeds #4359 (`|∂_β c| ≤ S·c`) into `pseudoMassFromParamsAtPair_beta_pow_succ_deriv_bound_of_corr_…`
with `K = S·(m⁻)^{2α}` (so `K·c/(m⁻)^{2α} = S·c` cancels), then rewrites the per-pair `atPair`
function to the envelope's `atPairDist` via `pseudoMassFromParamsAtPairDist_eq_atPair_cubic`. -/
theorem pseudoMassFromParamsAtPairDist_pow_succ_hasDeriv_abs_le_binding {α d : ℕ} (hα : 1 ≤ α)
    (hd : 1 ≤ d) (hαd : d < 2 * α) (hαd2 : α < d) {J β : ℝ} (hJ : 0 < J)
    (hβ_win : β ∈ ConvergenceRegion.window d J)
    {x z : Fin d → ℤ} (hxz : x ≠ z) (hxz_nonadj : ¬ (latticeGraph d).Adj x z)
    (hm_pos : 0 < globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ))
    (hbind : pseudoMassFromParamsAtPairDist hα (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      = globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ dv : ℝ,
      HasDerivAt (fun β' => (pseudoMassFromParamsAtPairDist hα (cubicExhaustion d)
          (⟨J, 0, β'⟩ : IsingParams ℝ) x z) ^ (2 * α + 1)) dv β ∧
      |dv| ≤ ↑(2 * α + 1)
          * ((J * (2 * (1 + (globalPseudoMassDist hα (cubicExhaustion d)
                  (⟨J, 0, β⟩ : IsingParams ℝ) * (latticeDistance d x z : ℝ)) ^ α)
                * Real.exp (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ))
                * (C * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ)))))
              + J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α)
                  * Real.exp (globalPseudoMassDist hα (cubicExhaustion d)
                      (⟨J, 0, β⟩ : IsingParams ℝ)))))
            * (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)) ^ (2 * α))
          / (latticeDistance d x z : ℝ) := by
  classical
  have hpos : (0 : ℝ) < (latticeDistance d x z : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (fun h => hxz ((IsingModel.latticeDistance_eq_zero_iff d x z).mp h))
  have hβ_pos : 0 < β := (ConvergenceRegion.window_subset_highTemp d J hJ hd hβ_win).1
  -- the sharp p.312 derivative bound `|∂_β c| ≤ S·c`.
  obtain ⟨C, hC, hsharp⟩ := abs_deriv_correlationInfinite_le_sharp hα hd hαd hαd2 hJ hβ_win
    hxz hxz_nonadj hm_pos hbind
  refine ⟨C, hC, ?_⟩
  set Sval : ℝ := (J * (2 * (1 + (globalPseudoMassDist hα (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) * (latticeDistance d x z : ℝ)) ^ α)
          * Real.exp (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ))
          * (C * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ)))))
        + J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α)
            * Real.exp (globalPseudoMassDist hα (cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ))))) with hSval_def
  -- `HasDerivAt` of the correlation profile at `β`.
  obtain ⟨g', hderiv_lim⟩ :=
    ConvergenceRegion.derivativeLimit_on_window d J (cubicExhaustion d) hJ hxz
  have hHasDeriv : HasDerivAt (fun β' => correlationInfinite (latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}) (g' β) β :=
    correlationInfinite_hasDerivAt_beta_of_tendstoLocallyUniformlyOn_deriv
      hd (cubicExhaustion d) x z hxz J hJ g' isOpen_Ioo
      (ConvergenceRegion.window_subset_highTemp d J hJ hd) hderiv_lim β hβ_win
  have hcorr : correlationInfinite (latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2 :=
    correlationInfinite_pair_active_of_betaJ_pos_exhaustion
      (cubicExhaustion d) hβ_pos (mul_pos hβ_pos hJ) x z hxz
  -- the per-pair (distance-radius) pseudo-mass equals `m⁻` at the binding point.
  have hbridge : pseudoMassFromParamsAtPair hα hpos d (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) x z
      = globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) := by
    rw [← pseudoMassFromParamsAtPairDist_eq_atPair_cubic hα _ hxz hpos]; exact hbind
  have hm2α_pos : (0 : ℝ) < (pseudoMassFromParamsAtPair hα hpos d (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) x z) ^ (2 * α) := by
    rw [hbridge]; exact pow_pos hm_pos _
  -- assemble the `K·c/m^{2α}` form with `K = S·m^{2α}`.
  have hcomp : |g' β| ≤ (Sval * (pseudoMassFromParamsAtPair hα hpos d (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z) ^ (2 * α))
      * correlationInfinite (latticeGraph d) (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
      / (pseudoMassFromParamsAtPair hα hpos d (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z) ^ (2 * α) := by
    have hcancel : (Sval * (pseudoMassFromParamsAtPair hα hpos d (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z) ^ (2 * α))
        * correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
        / (pseudoMassFromParamsAtPair hα hpos d (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) x z) ^ (2 * α)
        = Sval * correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} := by
      rw [mul_right_comm, mul_div_assoc, div_self (ne_of_gt hm2α_pos), mul_one]
    rw [hcancel, ← hHasDeriv.deriv]
    exact hsharp
  obtain ⟨dval, hderiv_dval, hbound⟩ :=
    pseudoMassFromParamsAtPair_beta_pow_succ_deriv_bound_of_corr_hasDerivAt
      hα hpos (cubicExhaustion d) J x z hHasDeriv hcorr hcomp
  -- transfer the `atPair` function to the envelope's `atPairDist` function.
  have hfun : (fun β' => (pseudoMassFromParamsAtPairDist hα (cubicExhaustion d)
        (⟨J, 0, β'⟩ : IsingParams ℝ) x z) ^ (2 * α + 1))
      = (fun β' => (pseudoMassFromParamsAtPair hα hpos d (cubicExhaustion d)
        (⟨J, 0, β'⟩ : IsingParams ℝ) x z) ^ (2 * α + 1)) := by
    funext β'
    rw [pseudoMassFromParamsAtPairDist_eq_atPair_cubic hα _ hxz hpos]
  refine ⟨dval, hfun ▸ hderiv_dval, ?_⟩
  -- the output constant `(2α+1)·K/r` with `K = S·m^{2α}` and `m = m⁻` (via the bridge).
  rw [hbridge] at hbound
  exact hbound

end Ambient
end IsingModel
