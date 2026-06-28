import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityUniformInfLipschitz
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.GlobalPseudoMassDistCubicInf

/-!
# GJ §17.5 Theorem 17.5.1 — conditional capstone: `globalPseudoMassDist^{2α+1}` is Lipschitz

Assembles the `A↑` bridge (`globalPseudoMassDist_eq_csInf_finiteRegion_cubic`) and the Step-2
inf-of-uniformly-Lipschitz-is-Lipschitz lemma (`abs_csInf_range_sub_csInf_range_le`) into the GJ
p.312 conclusion: if the finite-region pseudo-mass power
`finiteRegionPseudoMassDist(σ, volume n)^{2α+1}` is Lipschitz with a constant **uniform in the
stage `n`** (the remaining GJ "Step-1" content), then
the *system* pseudo-mass power `globalPseudoMassDist(σ)^{2α+1}` is Lipschitz with the same constant.

The bridge gives `globalPseudoMassDist(σ) = sInf (range finiteRegion(σ,·))`; the helper
`sInf_range_pow_of_nonneg` (a continuous monotone power commutes with a bounded-below `sInf` over
nonnegatives) lifts this to the `(2α+1)`-power, so `globalPseudoMassDist(σ)^{2α+1}` is the `sInf` of
the range of the *uniformly-Lipschitz* finite-region powers, and Step-2 finishes.

This reduces GJ Theorem 17.5.1 to **Step-1 alone** (uniform-in-`A` finite-region sharp Lipschitz).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

open Real Filter Topology

/-- **A power commutes with a bounded-below `sInf` over nonnegatives**: for `f : ι → ℝ` with
`0 ≤ f i` and `BddBelow (range f)`, `sInf (range (fun i => f i ^ k)) = (sInf (range f)) ^ k`.

`≥`: `m := sInf (range f) ≥ 0`, `m ≤ f i` ⇒ `m^k ≤ (f i)^k` (`pow_le_pow_left₀`), so `m^k` is a
lower bound.  `≤`: for every `ε > 0` there is `i` with `f i < m + ε` (`exists_lt_of_csInf_lt`), so
`sInf (range f^k) ≤ (f i)^k ≤ (m+ε)^k`; letting `ε → 0⁺` and using continuity of `ε ↦ (m+ε)^k`
(`le_of_tendsto`) gives `sInf (range f^k) ≤ m^k`. -/
theorem sInf_range_pow_of_nonneg {ι : Type*} [Nonempty ι] {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i)
    (hbdd : BddBelow (Set.range f)) (k : ℕ) :
    sInf (Set.range (fun i => f i ^ k)) = (sInf (Set.range f)) ^ k := by
  set m : ℝ := sInf (Set.range f) with hm_def
  have hne : (Set.range f).Nonempty := Set.range_nonempty f
  have hm_nn : 0 ≤ m := le_csInf hne (by rintro _ ⟨i, rfl⟩; exact hf i)
  have hbdd_fk : BddBelow (Set.range (fun i => f i ^ k)) :=
    ⟨0, by rintro _ ⟨i, rfl⟩; exact pow_nonneg (hf i) k⟩
  have hne_fk : (Set.range (fun i => f i ^ k)).Nonempty := Set.range_nonempty _
  refine le_antisymm ?_ ?_
  · -- `sInf (range f^k) ≤ m^k` via the `ε → 0⁺` limit.
    have key : ∀ ε : ℝ, 0 < ε → sInf (Set.range (fun i => f i ^ k)) ≤ (m + ε) ^ k := by
      intro ε hε
      obtain ⟨_, ⟨i, rfl⟩, hi⟩ := exists_lt_of_csInf_lt hne (by linarith : m < m + ε)
      calc sInf (Set.range (fun i => f i ^ k)) ≤ f i ^ k := csInf_le hbdd_fk ⟨i, rfl⟩
        _ ≤ (m + ε) ^ k := pow_le_pow_left₀ (hf i) hi.le k
    have hcont : Tendsto (fun ε : ℝ => (m + ε) ^ k) (𝓝[>] 0) (𝓝 (m ^ k)) := by
      have : Tendsto (fun ε : ℝ => (m + ε) ^ k) (𝓝 0) (𝓝 (m ^ k)) := by
        have h0 : ((fun ε : ℝ => (m + ε) ^ k) 0) = m ^ k := by simp
        exact h0 ▸ (((continuous_const.add continuous_id).pow k).tendsto 0)
      exact this.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hcont ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact key ε hε
  · -- `m^k ≤ sInf (range f^k)`: `m^k` is a lower bound.
    refine le_csInf hne_fk ?_
    rintro _ ⟨i, rfl⟩
    exact pow_le_pow_left₀ hm_nn (csInf_le hbdd ⟨i, rfl⟩) k

/-- **GJ p.312 conditional capstone — `globalPseudoMassDist^{2α+1}` Lipschitz from uniform-in-`A`
finite-region Lipschitz**: on `Icc β₁ β₂` with `0 < β₁ ≤ β₂`, if for every cubic stage `n` the
finite-region pseudo-mass power is `L·(β₂−β₁)`-Lipschitz (the *same* `L` for all `n`), then
`|globalPseudoMassDist(β₂)^{2α+1} − globalPseudoMassDist(β₁)^{2α+1}| ≤ L·(β₂−β₁)`.

Bridge (`globalPseudoMassDist_eq_csInf_finiteRegion_cubic`) + `sInf_range_pow_of_nonneg` rewrite
both system powers as `sInf` of the ranges of the finite-region powers; Step-2
(`abs_csInf_range_sub_csInf_range_le`) finishes from the uniform hypothesis.  This reduces GJ
Theorem 17.5.1 to **Step-1** (the uniform-in-`A` finite-region sharp Lipschitz). -/
theorem globalPseudoMassDist_pow_succ_lipschitz_of_uniform_finiteRegion {α d : ℕ} (hα : 1 ≤ α)
    (hd : 1 ≤ d) {J β₁ β₂ L : ℝ} (hJ : 0 < J) (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hunif : ∀ n : cubicMassIndex d,
      |(finiteRegionPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β₂⟩ : IsingParams ℝ)
            ((cubicExhaustion d).volume n.1) n.2) ^ (2 * α + 1)
          - (finiteRegionPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β₁⟩ : IsingParams ℝ)
            ((cubicExhaustion d).volume n.1) n.2) ^ (2 * α + 1)|
        ≤ L * (β₂ - β₁)) :
    |(globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β₂⟩ : IsingParams ℝ)) ^ (2 * α + 1)
        - (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β₁⟩ : IsingParams ℝ)) ^ (2 * α + 1)|
      ≤ L * (β₂ - β₁) := by
  classical
  haveI : Nonempty (cubicMassIndex d) := cubicMassIndex_nonempty hd
  have hβ₂ : 0 < β₂ := lt_of_lt_of_le hβ₁ hβ₁₂
  -- per-endpoint finite-region family and its nonnegativity / boundedness.
  set fr : ℝ → cubicMassIndex d → ℝ := fun β n =>
    finiteRegionPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      ((cubicExhaustion d).volume n.1) n.2 with hfr
  have hfr_nn : ∀ (β : ℝ), 0 < β → ∀ n : cubicMassIndex d, 0 ≤ fr β n := by
    intro β hβ n
    exact (finiteRegionPseudoMassDist_pos_of_betaJ_pos hα (cubicExhaustion d)
      ((cubicExhaustion d).volume n.1) n.2 hJ hβ).le
  have hfr_bdd : ∀ (β : ℝ), 0 < β → BddBelow (Set.range (fr β)) := by
    intro β hβ
    exact ⟨0, by rintro _ ⟨n, rfl⟩; exact hfr_nn β hβ n⟩
  -- rewrite both system powers as `sInf` of the finite-region powers.
  have hrw : ∀ (β : ℝ), 0 < β →
      (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)) ^ (2 * α + 1)
        = sInf (Set.range (fun n : cubicMassIndex d => (fr β n) ^ (2 * α + 1))) := by
    intro β hβ
    rw [globalPseudoMassDist_eq_csInf_finiteRegion_cubic hα hd hJ hβ,
      ← sInf_range_pow_of_nonneg (hfr_nn β hβ) (hfr_bdd β hβ) (2 * α + 1)]
  rw [hrw β₂ hβ₂, hrw β₁ hβ₁]
  -- Step-2 with `fa = (·)^{2α+1} at β₁`, `fb = (·)^{2α+1} at β₂`.
  exact abs_csInf_range_sub_csInf_range_le
    ⟨0, by rintro _ ⟨n, rfl⟩; exact pow_nonneg (hfr_nn β₁ hβ₁ n) _⟩
    ⟨0, by rintro _ ⟨n, rfl⟩; exact pow_nonneg (hfr_nn β₂ hβ₂ n) _⟩
    hunif

end Ambient
end IsingModel
