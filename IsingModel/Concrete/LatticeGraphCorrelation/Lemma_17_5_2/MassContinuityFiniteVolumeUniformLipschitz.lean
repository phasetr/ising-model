import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityFiniteVolumeUniformPowDeriv
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityInfEnvelopeLipschitz
import IsingModel.Concrete.LatticeGraphCorrelation.PointwiseRegularityBetaHZero

/-!
# GJ §17.5 Theorem 17.5.1 — PR-FV4c: the uniform-in-`A` finite-region Lipschitz estimate (p.312)

The GJ p.312 conclusion at finite volume: `m⁻_FV(σ,A)^{2α+1}` is Lipschitz in `β` with a constant
**uniform in the region `A`** (= the cubic stage `n`).  This is the step that the infinite-volume
route could not reach (its per-pair constant `(2α+1)K/dist` is not controlled as `diam A → ∞`); the
finite-volume route supplies the σ/A-uniform per-pair slope bound `M` (PR-FV4b), so the inf-envelope
fencing `abs_sub_le_of_isInf_binding_deriv` collapses to the single `M`.

For each stage `n` and the high-temperature window `[β₁,β₂]` (`β₂·J·2d < 1/2`):
`|m⁻_FV(σ_{β₂},A)^{2α+1} − m⁻_FV(σ_{β₁},A)^{2α+1}| ≤ M·(β₂ − β₁)`, with the **same** `M` for every
`n`.  This is the exact hypothesis the FV capstone (PR-FV5) feeds to the `A ↑ ℤ^d` bridge (#4369).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Set

/-- **Per-pair finite-volume pseudo-mass is continuous in `β`**: for a distinct in-box pair `x≠z`
and `0<J`, `0<β₀`, `β ↦ pseudoMassFromParamsAtPairFV hα ⟨J,0,β⟩ n x z` is continuous at `β₀`.  The
FV correlation is continuous in `β` everywhere (finite volume) and lands in the active range
`Ioo 0 2` at `β₀`, where `pseudoMassExt` is continuous. -/
theorem pseudoMassFromParamsAtPairFV_beta_continuousAt {α d : ℕ} (hα : 1 ≤ α)
    {J β₀ : ℝ} (hJ : 0 < J) (hβ₀ : 0 < β₀) {n : ℕ} {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hx : x ∈ (cubicExhaustion d).volume n) (hz : z ∈ (cubicExhaustion d).volume n) :
    ContinuousAt (fun β => pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z)
      β₀ := by
  have hdist_pos : (0 : ℝ) < (IsingModel.latticeDistance d x z : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (fun h => hxz ((IsingModel.latticeDistance_eq_zero_iff d x z).mp h))
  have hsub : ({x, z} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n := by
    intro w hw; rw [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hx
    · exact hz
  have hmem₀ : Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β₀⟩ : IsingParams ℝ) {x, z} n ∈ Set.Ioo (0 : ℝ) 2 :=
    correlationAlongExhaustion_cubicExhaustion_pair_active hJ hβ₀ hxz hsub
  have hfun : (fun β => pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z)
      = (fun β => pseudoMassExt hα hdist_pos
          (Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n)) := by
    funext β
    exact pseudoMassFromParamsAtPairFV_of_ne hα (⟨J, 0, β⟩ : IsingParams ℝ) n hxz hdist_pos
  rw [hfun]
  change ContinuousAt ((pseudoMassExt hα hdist_pos) ∘
    (fun β => Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n)) β₀
  exact ContinuousAt.comp (pseudoMassExt_continuousAt hα hdist_pos hmem₀)
    (correlationAlongExhaustion_continuousAt_beta (cubicExhaustion d) {x, z} J β₀ n)

/-- **Finite-region finite-volume pseudo-mass is continuous in `β`**: for a region with a distinct
pair, `β ↦ finiteRegionPseudoMassDistFV hα ⟨J,0,β⟩ n hA` is continuous at every `β₀ > 0`.  A finite
infimum (`Finset.inf'`) of functions continuous at `β₀` (`ContinuousAt.finset_inf'_apply`), each the
per-pair continuity above. -/
theorem finiteRegionPseudoMassDistFV_beta_continuousAt {α d : ℕ} (hα : 1 ≤ α)
    {J β₀ : ℝ} (hJ : 0 < J) (hβ₀ : 0 < β₀) {n : ℕ}
    (hA : (finiteRegionDistinctPairs ((cubicExhaustion d).volume n)).Nonempty) :
    ContinuousAt (fun β => finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
      β₀ := by
  unfold finiteRegionPseudoMassDistFV
  refine ContinuousAt.finset_inf'_apply hA ?_
  intro q hq
  obtain ⟨hq1, hq2, hq_ne⟩ := mem_finiteRegionDistinctPairs.mp hq
  exact pseudoMassFromParamsAtPairFV_beta_continuousAt hα hJ hβ₀ hq_ne hq1 hq2

/-- **GJ §17.5 Theorem 17.5.1 (FV4c): the uniform-in-`A` finite-region Lipschitz estimate** (p.312):
for the high-temperature window `[β₁,β₂]` (`0<β₁≤β₂`, `β₂·J·2d<1/2`) and `α ≥ d−1` (`d/2<α<d`),
there is **one** `L>0` such that for *every* cubic stage `n` with a distinct pair,
`|m⁻_FV(σ_{β₂},volume n)^{2α+1} − m⁻_FV(σ_{β₁},volume n)^{2α+1}| ≤ L·(β₂−β₁)`.  Per stage, the
inf-envelope fencing `abs_sub_le_of_isInf_binding_deriv` over the distinct-pair family: the slope at
each `β` is bounded by the σ/A-uniform `M` (PR-FV4b) at the inf' achiever (binding pair), the
envelope `(finiteRegionPseudoMassDistFV)^{2α+1}` is continuous and dominates each per-pair
power. -/
theorem finiteRegionPseudoMassDistFV_pow_succ_lipschitz_uniform {α d : ℕ} (hα : 1 ≤ α)
    (hd : 1 ≤ d) (hαd : d < 2 * α) (hαd2 : α < d) (hαd1 : d ≤ α + 1)
    {J β₁ β₂ : ℝ} (hJ : 0 < J) (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hβ₂_half : β₂ * J * (2 * d) < 1 / 2) :
    ∃ L : ℝ, 0 < L ∧ ∀ n : cubicMassIndex d,
      |(finiteRegionPseudoMassDistFV hα (⟨J, 0, β₂⟩ : IsingParams ℝ) n.1 n.2) ^ (2 * α + 1)
          - (finiteRegionPseudoMassDistFV hα (⟨J, 0, β₁⟩ : IsingParams ℝ) n.1 n.2) ^ (2 * α + 1)|
        ≤ L * (β₂ - β₁) := by
  classical
  obtain ⟨M, hM, hMbd⟩ := pseudoMassFromParamsAtPairFV_pow_succ_hasDeriv_abs_le_uniform hα hd hαd
    hαd2 hαd1 hJ hβ₁ hβ₁₂ hβ₂_half
  refine ⟨M, hM, fun n => ?_⟩
  set hA := n.2 with hA_def
  -- the envelope and per-pair powered families.
  set g : ℝ → ℝ := fun β =>
    (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n.1 hA) ^ (2 * α + 1) with hg_def
  set f : {q : (Fin d → ℤ) × (Fin d → ℤ) //
      q ∈ finiteRegionDistinctPairs ((cubicExhaustion d).volume n.1)} → ℝ → ℝ := fun q β =>
    (pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n.1 q.1.1 q.1.2) ^ (2 * α + 1)
    with hf_def
  have hmono : Monotone (fun t : ℝ => t ^ (2 * α + 1)) :=
    (Odd.strictMono_pow ⟨α, by ring⟩).monotone
  -- continuity of the envelope on `[β₁,β₂]`.
  have hg_cont : ContinuousOn g (Set.Icc β₁ β₂) := by
    refine ContinuousOn.pow ?_ (2 * α + 1)
    intro β hβ
    exact (finiteRegionPseudoMassDistFV_beta_continuousAt hα hJ
      (lt_of_lt_of_le hβ₁ hβ.1) hA).continuousWithinAt
  -- envelope dominates each per-pair power.
  have hle : ∀ q, ∀ β ∈ Set.Icc β₁ β₂, g β ≤ f q β := by
    intro q β _
    simp only [hg_def, hf_def]
    refine hmono ?_
    unfold finiteRegionPseudoMassDistFV
    exact Finset.inf'_le _ q.2
  -- binding pair at each `β`: the inf' achiever, with the σ/A-uniform slope bound.
  have hbind : ∀ β ∈ Set.Icc β₁ β₂, ∃ q, g β = f q β ∧
      ∃ dv : ℝ, HasDerivAt (f q) dv β ∧ |dv| ≤ M := by
    intro β hβmem
    have hβ : 0 < β := lt_of_lt_of_le hβ₁ hβmem.1
    obtain ⟨q₀, hq₀_mem, hq₀_eq⟩ := Finset.exists_mem_eq_inf' hA
      (fun q => pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n.1 q.1 q.2)
    obtain ⟨hq1, hq2, hq_ne⟩ := mem_finiteRegionDistinctPairs.mp hq₀_mem
    have hbind' : pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n.1 q₀.1 q₀.2
        = finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n.1 hA := by
      unfold finiteRegionPseudoMassDistFV; exact hq₀_eq.symm
    refine ⟨⟨q₀, hq₀_mem⟩, ?_, ?_⟩
    · simp only [hg_def, hf_def]; rw [hbind']
    · obtain ⟨dv, hdv_deriv, hdv_bd⟩ := hMbd n.1 β hβmem hA q₀.1 q₀.2 hq_ne hq1 hq2 hbind'
      exact ⟨dv, hdv_deriv, hdv_bd⟩
  exact abs_sub_le_of_isInf_binding_deriv hβ₁₂ hg_cont hle hbind

end Ambient
end IsingModel
