import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityFiniteVolumeCapstone
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# GJ §17.5 Theorem 17.5.1 — PR-FV6: continuity of the system pseudo-mass (pp.~311–312)

The explicit continuity statement of GJ Theorem 17.5.1's core: the system pseudo-mass
`σ ↦ globalPseudoMassDist(σ)` (`= m⁻(σ)`) is **continuous** on the high-temperature window.

The key upgrade over PR-FV5 (which gave the endpoint bound for one chosen `[β₁,β₂]`): the
σ/A-uniform slope bound `M` (PR-FV4b) is uniform over the *whole* window, so the **same** `M` works
for every
sub-interval `[a,b] ⊆ [β₁,β₂]`.  Hence `globalPseudoMassDist(·)^{2α+1}` is genuinely
`LipschitzOnWith M` on `[β₁,β₂]`, so continuous; peeling the `(2α+1)`-power by the continuous rpow
inverse on `[0,∞)` gives continuity of `globalPseudoMassDist` itself.

With Lemma 17.5.2 (the sandwich, #4278/#4297) this is GJ Theorem 17.5.1 — the mass `m(σ)` is
continuous on the single-phase / high-temperature window.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

open Set

/-- **Continuity from continuity of a fixed power** (generic): for `f ≥ 0` on `s` and `n ≠ 0`, if
`fⁿ` is continuous on `s` then so is `f`.  Peel the power by the continuous rpow inverse `(·)^{n⁻¹}`
on `[0,∞)` (`Real.pow_rpow_inv_natCast`).  Stated abstractly so the heavy `globalPseudoMassDist`
term is never `whnf`-unfolded in the peel. -/
theorem continuousOn_of_pow_continuousOn {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ} (hn : n ≠ 0)
    (hf_nn : ∀ x ∈ s, 0 ≤ f x) (hpow : ContinuousOn (fun x => (f x) ^ n) s) :
    ContinuousOn f s := by
  have hrpow : ContinuousOn (fun x => ((f x) ^ n) ^ ((n : ℝ)⁻¹)) s :=
    hpow.rpow_const (fun _ _ => Or.inr (by positivity))
  exact hrpow.congr (fun x hx => (Real.pow_rpow_inv_natCast (hf_nn x hx) hn).symm)

/-- **Continuity from a sub-interval power increment bound** (generic): for `G ≥ 0` on `s`, `n ≠ 0`,
`0 ≤ M`, if `|Gⁿ(b) − Gⁿ(a)| ≤ M(b−a)` for all `a ≤ b` in `s`, then `G` is continuous on `s`.  The
bound makes `Gⁿ` `LipschitzOnWith M.toNNReal` on `s` (hence continuous), then peel the power.
Stated abstractly so the heavy `globalPseudoMassDist` term is never `whnf`-unfolded. -/
theorem continuousOn_of_subpair_pow_bound {G : ℝ → ℝ} {s : Set ℝ} {n : ℕ} {M : ℝ}
    (hn : n ≠ 0) (hM : 0 ≤ M) (hG_nn : ∀ x ∈ s, 0 ≤ G x)
    (hsub : ∀ a ∈ s, ∀ b ∈ s, a ≤ b → |(G b) ^ n - (G a) ^ n| ≤ M * (b - a)) :
    ContinuousOn G s := by
  have hlip : LipschitzOnWith M.toNNReal (fun x => (G x) ^ n) s := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal M hM]
    rcases le_total y x with hyx | hxy
    · have h := hsub y hy x hx hyx
      calc |(G x) ^ n - (G y) ^ n| ≤ M * (x - y) := h
        _ = M * |x - y| := by rw [abs_of_nonneg (by linarith)]
    · have h := hsub x hx y hy hxy
      calc |(G x) ^ n - (G y) ^ n| = |(G y) ^ n - (G x) ^ n| := abs_sub_comm _ _
        _ ≤ M * (y - x) := h
        _ = M * |x - y| := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  exact continuousOn_of_pow_continuousOn hn hG_nn hlip.continuousOn

/-- **Per-stage endpoint bound from a fixed slope `M`** (GJ p.312): given the σ/A-uniform per-pair
slope bound `hMbd` (PR-FV4b's `∀`-form) over `[β₁,β₂]`, every sub-interval `[a,b] ⊆ [β₁,β₂]` and
every cubic stage `n` satisfy `|m⁻_FV(σ_b,volume n)^{2α+1} − m⁻_FV(σ_a,volume n)^{2α+1}| ≤ M(b−a)`,
with the **same** `M`.  The inf-envelope fencing `abs_sub_le_of_isInf_binding_deriv` on `[a,b]`. -/
theorem finiteRegionPseudoMassDistFV_pow_succ_abs_sub_le_of_slope {α d : ℕ} (hα : 1 ≤ α)
    {J β₁ β₂ M : ℝ} (hJ : 0 < J) (hβ₁ : 0 < β₁)
    (hMbd : ∀ (n : ℕ) (β : ℝ), β ∈ Set.Icc β₁ β₂ →
      ∀ (hA : (finiteRegionDistinctPairs ((cubicExhaustion d).volume n)).Nonempty)
        (x z : Fin d → ℤ), x ≠ z →
        x ∈ (cubicExhaustion d).volume n → z ∈ (cubicExhaustion d).volume n →
        pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z
          = finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA →
        ∃ dv : ℝ,
          HasDerivAt (fun β' => (pseudoMassFromParamsAtPairFV hα (⟨J, 0, β'⟩ : IsingParams ℝ) n x z)
              ^ (2 * α + 1)) dv β ∧ |dv| ≤ M)
    {a b : ℝ} (ha : a ∈ Set.Icc β₁ β₂) (hb : b ∈ Set.Icc β₁ β₂) (hab : a ≤ b)
    (n : cubicMassIndex d) :
    |(finiteRegionPseudoMassDistFV hα (⟨J, 0, b⟩ : IsingParams ℝ) n.1 n.2) ^ (2 * α + 1)
        - (finiteRegionPseudoMassDistFV hα (⟨J, 0, a⟩ : IsingParams ℝ) n.1 n.2) ^ (2 * α + 1)|
      ≤ M * (b - a) := by
  classical
  set hA := n.2 with hA_def
  set g : ℝ → ℝ := fun β =>
    (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n.1 hA) ^ (2 * α + 1) with hg_def
  set f : {q : (Fin d → ℤ) × (Fin d → ℤ) //
      q ∈ finiteRegionDistinctPairs ((cubicExhaustion d).volume n.1)} → ℝ → ℝ := fun q β =>
    (pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n.1 q.1.1 q.1.2) ^ (2 * α + 1)
    with hf_def
  have hmono : Monotone (fun t : ℝ => t ^ (2 * α + 1)) :=
    (Odd.strictMono_pow ⟨α, by ring⟩).monotone
  have hsub_ab : Set.Icc a b ⊆ Set.Icc β₁ β₂ := Set.Icc_subset_Icc ha.1 hb.2
  have hg_cont : ContinuousOn g (Set.Icc a b) := by
    refine ContinuousOn.pow ?_ (2 * α + 1)
    intro β hβ
    exact (finiteRegionPseudoMassDistFV_beta_continuousAt hα hJ
      (lt_of_lt_of_le hβ₁ (hsub_ab hβ).1) hA).continuousWithinAt
  have hle : ∀ q, ∀ β ∈ Set.Icc a b, g β ≤ f q β := by
    intro q β _
    simp only [hg_def, hf_def]
    refine hmono ?_
    unfold finiteRegionPseudoMassDistFV
    exact Finset.inf'_le _ q.2
  have hbind : ∀ β ∈ Set.Icc a b, ∃ q, g β = f q β ∧
      ∃ dv : ℝ, HasDerivAt (f q) dv β ∧ |dv| ≤ M := by
    intro β hβmem
    obtain ⟨q₀, hq₀_mem, hq₀_eq⟩ := Finset.exists_mem_eq_inf' hA
      (fun q => pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n.1 q.1 q.2)
    obtain ⟨hq1, hq2, hq_ne⟩ := mem_finiteRegionDistinctPairs.mp hq₀_mem
    have hbind' : pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n.1 q₀.1 q₀.2
        = finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n.1 hA := by
      unfold finiteRegionPseudoMassDistFV; exact hq₀_eq.symm
    refine ⟨⟨q₀, hq₀_mem⟩, ?_, ?_⟩
    · simp only [hg_def, hf_def]; rw [hbind']
    · obtain ⟨dv, hdv_deriv, hdv_bd⟩ :=
        hMbd n.1 β (hsub_ab hβmem) hA q₀.1 q₀.2 hq_ne hq1 hq2 hbind'
      exact ⟨dv, hdv_deriv, hdv_bd⟩
  exact abs_sub_le_of_isInf_binding_deriv hab hg_cont hle hbind

/-- **System pseudo-mass power increment over any sub-interval** (GJ p.312): for the
high-temperature window `[β₁,β₂]` (`0<β₁≤β₂`, `β₂·J·2d<1/2`) and `α≥d−1` (`d/2<α<d`), there is
**one** `M>0` such that for *every* sub-interval `[a,b] ⊆ [β₁,β₂]`,
`|globalPseudoMassDist(σ_b)^{2α+1} − globalPseudoMassDist(σ_a)^{2α+1}| ≤ M(b−a)`.  The σ/A-uniform
slope bound `M` (PR-FV4b) is uniform over the whole window, so the *same* `M` works for every
sub-interval: apply the FV capstone (`globalPseudoMassDist_pow_succ_lipschitz_of_uniform_finite
RegionFV`) on `[a,b]` with the per-stage bound
`finiteRegionPseudoMassDistFV_pow_succ_abs_sub_le_of_slope`. -/
theorem globalPseudoMassDist_pow_succ_abs_sub_le_subpair {α d : ℕ} (hα : 1 ≤ α)
    (hd : 1 ≤ d) (hαd : d < 2 * α) (hαd2 : α < d) (hαd1 : d ≤ α + 1)
    {J β₁ β₂ : ℝ} (hJ : 0 < J) (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hβ₂_half : β₂ * J * (2 * d) < 1 / 2) :
    ∃ M : ℝ, 0 < M ∧ ∀ a ∈ Set.Icc β₁ β₂, ∀ b ∈ Set.Icc β₁ β₂, a ≤ b →
      |(globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, b⟩ : IsingParams ℝ)) ^ (2 * α + 1)
          - (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, a⟩ : IsingParams ℝ)) ^ (2 * α + 1)|
        ≤ M * (b - a) := by
  obtain ⟨M, hM, hMbd⟩ := pseudoMassFromParamsAtPairFV_pow_succ_hasDeriv_abs_le_uniform hα hd hαd
    hαd2 hαd1 hJ hβ₁ hβ₁₂ hβ₂_half
  refine ⟨M, hM, fun a ha b hb hab => ?_⟩
  refine globalPseudoMassDist_pow_succ_lipschitz_of_uniform_finiteRegionFV hα hd hJ
    (lt_of_lt_of_le hβ₁ ha.1) hab (fun n => ?_)
  exact finiteRegionPseudoMassDistFV_pow_succ_abs_sub_le_of_slope hα hJ hβ₁ hMbd ha hb hab n

/-- **GJ §17.5 Theorem 17.5.1 — the system pseudo-mass is continuous on the high-temperature
window** (pp.~311--312): for `0<β₁≤β₂`, `β₂·J·2d<1/2`, `α≥d−1` (`d/2<α<d`),
`ContinuousOn (fun β => globalPseudoMassDist hα (cubicExhaustion d) ⟨J,0,β⟩) (Icc β₁ β₂)`.

The σ/A-uniform slope bound `M` (PR-FV4b) fences every sub-interval with the same `M`
(`globalPseudoMassDist_pow_succ_abs_sub_le_subpair`), so `globalPseudoMassDist(·)^{2α+1}` is
`LipschitzOnWith M.toNNReal` on `[β₁,β₂]`, hence continuous; peeling the `(2α+1)`-power by the
continuous rpow inverse `(·)^{(2α+1)⁻¹}` on `[0,∞)` (`globalPseudoMassDist ≥ 0`,
`continuousOn_of_subpair_pow_bound`) gives continuity of `globalPseudoMassDist`.  With Lemma 17.5.2
(#4278/#4297) this is GJ Theorem 17.5.1. -/
theorem globalPseudoMassDist_continuousOn_window {α d : ℕ} (hα : 1 ≤ α)
    (hd : 1 ≤ d) (hαd : d < 2 * α) (hαd2 : α < d) (hαd1 : d ≤ α + 1)
    {J β₁ β₂ : ℝ} (hJ : 0 < J) (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hβ₂_half : β₂ * J * (2 * d) < 1 / 2) :
    ContinuousOn (fun β => globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ))
      (Set.Icc β₁ β₂) := by
  obtain ⟨M, hM, hglob_sub⟩ := globalPseudoMassDist_pow_succ_abs_sub_le_subpair hα hd hαd hαd2 hαd1
    hJ hβ₁ hβ₁₂ hβ₂_half
  exact continuousOn_of_subpair_pow_bound (by omega) hM.le
    (fun β _ => globalPseudoMassDist_nonneg hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ))
    hglob_sub

end Ambient
end IsingModel
