import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityFiniteVolumeDerivSharp
import IsingModel.Concrete.LatticeGraphCorrelation.RegularityAlongEx
import IsingModel.PseudoMass.Lipschitz

/-!
# GJ §17.5 Theorem 17.5.1 — PR-FV4a: finite-volume per-pair pseudo-mass-power derivative bound

The finite-volume analogue of `pseudoMassFromParamsAtPairDist_pow_succ_hasDeriv_abs_le_binding`
(PR-B1, #4363) — but at the finite volume `A = volume n`: at a non-adjacent in-box **binding** pair
`x ≠ z` (`pseudoMassFromParamsAtPairFV = m⁻_FV(σ,A)`), the per-pair pseudo-mass power
`β' ↦ (m_FV(x,z,β'))^{2α+1}` is differentiable at `β` with
`|deriv| ≤ (2α+1)·⟨sharp⟩·m^{2α}/d(x,z)`, where `⟨sharp⟩` is the FV sharp-derivative coefficient
(PR-FV3i) and `m = pseudoMassFromParamsAtPairFV = m⁻_FV(σ,A)` (binding).

Feeds PR-FV3i (`|∂_β c_A| ≤ ⟨sharp⟩·c_A`) into the **generic** `pseudoMass_pow_succ_deriv_bound`
(PseudoMass/Lipschitz.lean) with `K = ⟨sharp⟩·m^{2α}` (so `K·c/m^{2α} = ⟨sharp⟩·c`), using the FV
profile identity (`correlationAlongExhaustion = pseudoMassG(d, m_FV)`; reused generic
`pseudoMassG_pseudoMassExt_eventuallyEq_of_eventually_mem`) and the FV correlation/pseudo-mass
derivatives.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real Filter Topology

/-- **Core finite-volume per-pair pseudo-mass-power derivative bound** (GJ p.312): the chain-rule
body of `pseudoMassFromParamsAtPairFV_pow_succ_hasDeriv_abs_le_binding` with the convolution
constant `C` and the FV sharp β-derivative bound `hsharp` supplied as **parameters**.  This lets the
mass-uniform path feed the single `β`-independent `C` (from `combined_..._mass_uniform`, then the
GKS-II abs step) into the chain rule, producing a uniform per-pair power-derivative bound. -/
theorem pseudoMassFromParamsAtPairFV_pow_succ_hasDeriv_abs_le_binding_core {α d : ℕ} (hα : 1 ≤ α)
    {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) {n : ℕ}
    (hA : (finiteRegionDistinctPairs ((cubicExhaustion d).volume n)).Nonempty)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hx : x ∈ (cubicExhaustion d).volume n) (hz : z ∈ (cubicExhaustion d).volume n)
    (hbind : pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z
      = finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
    (C : ℝ)
    (hsharp : |deriv (fun β' => Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d)
          (cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β|
        ≤ (J * (2 * (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA
                * (latticeDistance d x z : ℝ)) ^ α)
              * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
              * (C * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ)))))
            + J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α)
                * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
              + (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA) ^ α)
                * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
                / 2)))
          * Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n) :
    ∃ dv : ℝ,
      HasDerivAt (fun β' => (pseudoMassFromParamsAtPairFV hα (⟨J, 0, β'⟩ : IsingParams ℝ) n x z)
          ^ (2 * α + 1)) dv β ∧
      |dv| ≤ ↑(2 * α + 1)
          * ((J * (2 * (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA
                  * (latticeDistance d x z : ℝ)) ^ α)
                * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
                * (C * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ)))))
              + J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α)
                  * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
                + (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA) ^ α)
                  * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
                  / 2)))
            * (pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z) ^ (2 * α))
          / (latticeDistance d x z : ℝ) := by
  classical
  have hpos : (0 : ℝ) < (latticeDistance d x z : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (fun h => hxz ((IsingModel.latticeDistance_eq_zero_iff d x z).mp h))
  have hxzsub : ({x, z} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n := by
    intro w hw; rw [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hx
    · exact hz
  set Sval : ℝ := (J * (2 * (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA
            * (latticeDistance d x z : ℝ)) ^ α)
          * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
          * (C * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ)))))
        + J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α)
            * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
          + (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA) ^ α)
            * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
            / 2)))
    with hSval_def
  -- the FV correlation derivative and active range.
  obtain ⟨c', hc_deriv⟩ :=
    correlationAlongExhaustion_latticeGraph_hasDerivAt_beta d (cubicExhaustion d) J β {x, z} n
  have hcorr : Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n ∈ Set.Ioo (0 : ℝ) 2 :=
    correlationAlongExhaustion_cubicExhaustion_pair_active hJ hβ hxz hxzsub
  -- the FV per-pair pseudo-mass as `pseudoMassExt ∘ correlation`.
  have hfun : (fun β' => pseudoMassFromParamsAtPairFV hα (⟨J, 0, β'⟩ : IsingParams ℝ) n x z)
      = (fun β' => pseudoMassExt hα hpos
          (Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n)) := by
    funext β'; exact pseudoMassFromParamsAtPairFV_of_ne hα (⟨J, 0, β'⟩ : IsingParams ℝ) n hxz hpos
  -- `h` (the pseudo-mass profile) has a derivative (chain rule through `pseudoMassExt`).
  have hdiff : DifferentiableAt ℝ
      (fun β' => pseudoMassFromParamsAtPairFV hα (⟨J, 0, β'⟩ : IsingParams ℝ) n x z) β := by
    rw [hfun]
    exact ((pseudoMassExt_hasStrictDerivAt hα hpos hcorr).hasDerivAt.comp β
      hc_deriv).differentiableAt
  have hh : HasDerivAt (fun β' =>
      pseudoMassFromParamsAtPairFV hα (⟨J, 0, β'⟩ : IsingParams ℝ) n x z)
      (deriv (fun β' => pseudoMassFromParamsAtPairFV hα (⟨J, 0, β'⟩ : IsingParams ℝ) n x z) β) β :=
    hdiff.hasDerivAt
  -- the eventual profile identity `pseudoMassG α r (h β') = c β'`.
  have hcorr_event : ∀ᶠ β' in nhds β,
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n ∈ Set.Ioo (0 : ℝ) 2 :=
    hc_deriv.continuousAt.eventually_mem (IsOpen.mem_nhds isOpen_Ioo hcorr)
  have hg_eq : (fun β' => pseudoMassG α (latticeDistance d x z : ℝ)
        (pseudoMassFromParamsAtPairFV hα (⟨J, 0, β'⟩ : IsingParams ℝ) n x z)) =ᶠ[nhds β]
      (fun β' => Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) := by
    have hbase := pseudoMassG_pseudoMassExt_eventuallyEq_of_eventually_mem hα hpos
      (c := fun β' => Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d)
        (cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) hcorr_event
    have hBA : (fun β' => pseudoMassG α (latticeDistance d x z : ℝ)
          (pseudoMassFromParamsAtPairFV hα (⟨J, 0, β'⟩ : IsingParams ℝ) n x z))
        = (fun β' => pseudoMassG α (latticeDistance d x z : ℝ)
          (pseudoMassExt hα hpos (Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d)
            (cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n))) := by
      funext β'
      rw [pseudoMassFromParamsAtPairFV_of_ne hα (⟨J, 0, β'⟩ : IsingParams ℝ) n hxz hpos]
    rw [hBA]; exact hbase
  have hm_pos : 0 < pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z :=
    pseudoMassFromParamsAtPairFV_pos hα hJ hβ hxz hxzsub
  have hm2α_pos : (0 : ℝ) < (pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z)
      ^ (2 * α) := pow_pos hm_pos _
  -- the `K·c/m^{2α} = Sval·c` form of the sharp bound.
  have hc_der : |c'| ≤ (Sval * (pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z)
        ^ (2 * α))
      * Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n
      / (pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z) ^ (2 * α) := by
    have hcancel : (Sval * (pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z)
          ^ (2 * α))
        * Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n
        / (pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z) ^ (2 * α)
        = Sval * Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n := by
      rw [mul_right_comm, mul_div_assoc, div_self (ne_of_gt hm2α_pos), mul_one]
    rw [hcancel, ← hc_deriv.deriv]
    exact hsharp
  -- apply the generic power-derivative bound.
  obtain ⟨dv, hdv_deriv, hdv_bd⟩ := pseudoMass_pow_succ_deriv_bound α hpos hh hc_deriv hm_pos.le
    hg_eq hm_pos hcorr.1 hc_der
  exact ⟨dv, hdv_deriv, hdv_bd⟩

/-- **Finite-volume per-pair pseudo-mass-power derivative bound (binding pair)** (GJ p.312): for an
in-box binding pair `x ≠ z` (adjacent or not), `∃C>0, ∃dv, HasDerivAt (β'↦(m_FV(x,z,β'))^{2α+1}) dv
β ∧ |dv| ≤ (2α+1)·⟨sharp(C)⟩·m^{2α}/d(x,z)`.  Obtains `C` and the FV sharp β-derivative bound from
PR-FV3i, then applies the core. -/
theorem pseudoMassFromParamsAtPairFV_pow_succ_hasDeriv_abs_le_binding {α d : ℕ} (hα : 1 ≤ α)
    (hd : 1 ≤ d) (hαd : d < 2 * α) (hαd2 : α < d) {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) {n : ℕ}
    (hA : (finiteRegionDistinctPairs ((cubicExhaustion d).volume n)).Nonempty)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hx : x ∈ (cubicExhaustion d).volume n) (hz : z ∈ (cubicExhaustion d).volume n)
    (hbind : pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z
      = finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA) :
    ∃ C : ℝ, 0 < C ∧ ∃ dv : ℝ,
      HasDerivAt (fun β' => (pseudoMassFromParamsAtPairFV hα (⟨J, 0, β'⟩ : IsingParams ℝ) n x z)
          ^ (2 * α + 1)) dv β ∧
      |dv| ≤ ↑(2 * α + 1)
          * ((J * (2 * (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA
                  * (latticeDistance d x z : ℝ)) ^ α)
                * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
                * (C * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ)))))
              + J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α)
                  * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
                + (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA) ^ α)
                  * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
                  / 2)))
            * (pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z) ^ (2 * α))
          / (latticeDistance d x z : ℝ) := by
  obtain ⟨C, hC, hsharp⟩ := abs_deriv_correlationAlongExhaustion_le_sharp_finiteRegionFV hα hd hαd
    hαd2 hJ hβ hA hxz hx hz hbind
  exact ⟨C, hC, pseudoMassFromParamsAtPairFV_pow_succ_hasDeriv_abs_le_binding_core hα hJ hβ hA hxz
    hx hz hbind C hsharp⟩

end Ambient
end IsingModel
