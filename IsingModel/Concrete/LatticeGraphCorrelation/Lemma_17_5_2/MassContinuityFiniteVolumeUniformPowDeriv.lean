import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityFiniteVolumeUniformCombine
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityFiniteVolumeBindingPairDeriv
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityFiniteVolumeMassUpper
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuitySharpRFactor

/-!
# GJ §17.5 Theorem 17.5.1 — PR-FV4b: the σ/A-uniform per-pair power-derivative bound (p.312)

The payoff of the finite-volume route: a **single** constant `M > 0` bounds the per-pair pseudo-mass
power derivative `|d/dβ (m_FV(x,z,β))^{2α+1}|` at *every* binding pair, *every* stage `n`, and
*every* `β` in the high-temperature window `[β₁,β₂]` (`β₂·J·2d < 1/2`).  This is precisely the slope
bound the GJ p.312 inf-envelope fencing consumes (`abs_sub_le_of_isInf_binding_deriv`), yielding the
**uniform-in-`σ`-and-`A`** Lipschitz constant of `m⁻_FV(σ,A)^{2α+1}`.

Assembly: the mass-uniform combine (PR-FV4b, single convolution `C` for the whole window) → the
GKS-II absolute value step → the per-pair power-derivative chain rule (PR-FV4a core) → the rpow
collapse `pow_succ_sharp_div_r_le_uniform` using the two-sided mass bounds `mmin ≤ m⁻_FV ≤ Mwitness`
(#4360/#4380/#4381) and `α ≥ d−1`.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **σ/A-uniform per-pair pseudo-mass-power derivative bound** (GJ p.312): for the high-temperature
window `[β₁,β₂]` (`0<β₁≤β₂`, `β₂·J·2d<1/2`) and `α ≥ d−1` (with `d/2<α<d`), there is one `M>0` such
that for every `n`, every `β ∈ [β₁,β₂]`, and every in-box binding pair `x≠z`, the per-pair
`(2α+1)`-power derivative satisfies `∃ dv, HasDerivAt … dv β ∧ |dv| ≤ M`.  The constant is
`M = (2α+1)·(J·2(1+Mwitness^α)e^{Mwitness}·C·Mwitness^{2α} +
J·4d((1+2^α)e^{Mwitness}+(1+Mwitness^α)e^{Mwitness}/2)·Mwitness^{2α})`, with `C` the mass-uniform
convolution constant and `Mwitness` the stage-1 adjacent-witness mass (#4381). -/
theorem pseudoMassFromParamsAtPairFV_pow_succ_hasDeriv_abs_le_uniform {α d : ℕ} (hα : 1 ≤ α)
    (hd : 1 ≤ d) (hαd : d < 2 * α) (hαd2 : α < d) (hαd1 : d ≤ α + 1)
    {J β₁ β₂ : ℝ} (hJ : 0 < J) (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hβ₂_half : β₂ * J * (2 * d) < 1 / 2) :
    ∃ M : ℝ, 0 < M ∧ ∀ (n : ℕ) (β : ℝ), β ∈ Set.Icc β₁ β₂ →
      ∀ (hA : (finiteRegionDistinctPairs ((cubicExhaustion d).volume n)).Nonempty)
        (x z : Fin d → ℤ), x ≠ z →
        x ∈ (cubicExhaustion d).volume n → z ∈ (cubicExhaustion d).volume n →
        pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z
          = finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA →
        ∃ dv : ℝ,
          HasDerivAt (fun β' => (pseudoMassFromParamsAtPairFV hα (⟨J, 0, β'⟩ : IsingParams ℝ) n x z)
              ^ (2 * α + 1)) dv β ∧ |dv| ≤ M := by
  classical
  -- the witness mass `Mwitness` (stage-1 adjacent pair `(0, e₀)`).
  set w₂ : Fin d → ℤ := Pi.single (⟨0, hd⟩ : Fin d) (1 : ℤ) with hw₂_def
  set Mw : ℝ := pseudoMassFromParamsAtPairFV hα (⟨J, 0, β₁⟩ : IsingParams ℝ) 1 (0 : Fin d → ℤ) w₂
    with hMw_def
  -- `Mw > 0`.
  have hne : (0 : Fin d → ℤ) ≠ w₂ := by
    intro h
    have h0 := congrFun h ⟨0, hd⟩
    rw [hw₂_def] at h0; simp at h0
  have hw1m1 : (0 : Fin d → ℤ) ∈ (cubicExhaustion d).volume 1 := by
    change (0 : Fin d → ℤ) ∈ cubicBox d 1; rw [mem_cubicBox]; intro i; norm_num
  have hw2m1 : w₂ ∈ (cubicExhaustion d).volume 1 := by
    change w₂ ∈ cubicBox d 1; rw [mem_cubicBox]; intro i; rw [hw₂_def]
    by_cases hi : i = ⟨0, hd⟩
    · subst hi; simp
    · rw [Pi.single_eq_of_ne hi]; norm_num
  have hsub_w : ({0, w₂} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume 1 := by
    intro y hy; rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact hw1m1
    · exact hw2m1
  have hMw_pos : 0 < Mw := by
    rw [hMw_def]; exact pseudoMassFromParamsAtPairFV_pos hα hJ hβ₁ hne hsub_w
  have hMw_nn : 0 ≤ Mw := hMw_pos.le
  -- the mass-uniform convolution constant `C`.
  obtain ⟨C, hC, hcombine⟩ :=
    combined_derivative_div_c_bound_mass_uniform_finiteRegionFV hα hd hαd hαd2 hJ hβ₁ hβ₁₂ hβ₂_half
  -- the uniform constant `M`.
  refine ⟨↑(2 * α + 1) * (J * (2 * (1 + Mw ^ α) * Real.exp Mw * (C * Mw ^ (2 * α)))
      + J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α) * Real.exp Mw
        + (1 + Mw ^ α) * Real.exp Mw / 2) * Mw ^ (2 * α))), ?_, ?_⟩
  · -- `M > 0`.
    have h1 : (0 : ℝ) < J * (2 * (1 + Mw ^ α) * Real.exp Mw * (C * Mw ^ (2 * α))) := by
      have : (0 : ℝ) < Mw ^ (2 * α) := pow_pos hMw_pos _
      have hα1 : (0 : ℝ) < 1 + Mw ^ α := by positivity
      positivity
    have h2 : (0 : ℝ) ≤ J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α) * Real.exp Mw
        + (1 + Mw ^ α) * Real.exp Mw / 2) * Mw ^ (2 * α)) := by positivity
    have hcast : (0 : ℝ) < ↑(2 * α + 1) := by positivity
    have hsum : (0 : ℝ) < J * (2 * (1 + Mw ^ α) * Real.exp Mw * (C * Mw ^ (2 * α)))
        + J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α) * Real.exp Mw
          + (1 + Mw ^ α) * Real.exp Mw / 2) * Mw ^ (2 * α)) := by linarith
    exact mul_pos hcast hsum
  · -- the uniform per-pair bound.
    intro n β hβmem hA x z hxz hx hz hbind
    have hβ : 0 < β := lt_of_lt_of_le hβ₁ hβmem.1
    -- `1 ≤ n` (a distinct in-box pair exists, so the box is not a singleton).
    have hn : 1 ≤ n := by
      by_contra hn0
      have hn0' : n = 0 := by omega
      subst hn0'
      have hx0 : x = 0 := by
        funext i; obtain ⟨h1, h2⟩ := mem_cubicBox.mp hx i
        simp only [Nat.cast_zero, neg_zero] at h1 h2; simp only [Pi.zero_apply]; omega
      have hz0 : z = 0 := by
        funext i; obtain ⟨h1, h2⟩ := mem_cubicBox.mp hz i
        simp only [Nat.cast_zero, neg_zero] at h1 h2; simp only [Pi.zero_apply]; omega
      exact hxz (hx0.trans hz0.symm)
    have hxzsub : ({x, z} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n := by
      intro w hw; rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hx
      · exact hz
    -- the c-cancelling `/c` bound at the mass-uniform `C`.
    have hbd := hcombine n β hβmem hA x z hxz hx hz hbind
    -- the GKS-II absolute β-derivative sharp bound (inline FV3i abs step).
    have hc_pos : 0 < Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d)
        (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n :=
      (correlationAlongExhaustion_cubicExhaustion_pair_active hJ hβ hxz hxzsub).1
    have hnn : 0 ≤ deriv (fun β' => Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d)
        (cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β :=
      correlationAlongExhaustion_latticeGraph_beta_deriv_nonneg (cubicExhaustion d) J β hJ.le hβ
        {x, z} n
    have hsharp : |deriv (fun β' => Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d)
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
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n := by
      rw [abs_of_nonneg hnn]
      exact (div_le_iff₀ hc_pos).mp hbd
    -- the per-pair power-derivative bound (FV4a core).
    obtain ⟨dv, hdv_deriv, hdv_bd⟩ :=
      pseudoMassFromParamsAtPairFV_pow_succ_hasDeriv_abs_le_binding_core hα hJ hβ hA hxz hx hz hbind
        C hsharp
    refine ⟨dv, hdv_deriv, ?_⟩
    -- two-sided mass bounds at this binding pair: `0 ≤ m⁻_FV ≤ Mw`, `1 ≤ d(x,z)`.
    have hm_nn : 0 ≤ finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA :=
      (finiteRegionPseudoMassDistFV_pos hα hJ hβ hA).le
    have hm_le_Mw : finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA ≤ Mw := by
      rw [hMw_def, hw₂_def]
      exact finiteRegionPseudoMassDistFV_le_witness hα hd hJ hβ₁ hn hβmem hA
    have hr1 : (1 : ℝ) ≤ (latticeDistance d x z : ℝ) := by
      have h1 : 1 ≤ latticeDistance d x z :=
        Nat.one_le_iff_ne_zero.mpr (fun h => hxz ((latticeDistance_eq_zero_iff d x z).mp h))
      exact_mod_cast h1
    -- collapse `m⁻_FV` and `d(x,z)` to the uniform constant.
    rw [hbind] at hdv_bd
    exact hdv_bd.trans
      (pow_succ_sharp_div_r_le_uniform hαd hαd1 hm_nn hm_le_Mw hr1 hC.le hJ.le)

end Ambient
end IsingModel
