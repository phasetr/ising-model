import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.SharpHLSDenominatorComparison
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.FiniteRegionPseudoMassDistContinuity

/-!
# GJ §17.5 Lemma 17.5.2(a) — Lipschitz strengthening of the finite-region pseudo-mass `m⁻(σ, A)`

Upgrades the continuity (`FiniteRegionPseudoMassDistContinuity.lean`) of the distance-parametrized
finite-region system pseudo-mass `m⁻(σ, A)` to a Lipschitz estimate of its `(2α+1)`-power, on the
convergence window, for each *fixed* bounded region `A`, conditionally on the faithful per-pair
(distance-radius) profile lower bound.

Reuses the merged fixed-radius window interval Lipschitz
`lemma_17_5_2_pseudoMass_pow_succ_lipschitz_on_window_of_profile_lower` (#4331) at the per-pair
profile radius `ρ := latticeDistance d x z`, via the cubic-exhaustion bridge
`pseudoMassFromParamsAtPairDist_eq_atPair_cubic`.  The finite-region object is a `Finset.inf'`; the
`(2α+1)`-power commutes with the infimum and the infimum of finitely many Lipschitz functions is
Lipschitz (constant = the finite `Finset.sup'` of per-pair constants, via the achieved infimum).

**Conditional / Partial.** `hprofile` is the faithful per-pair distance form (the fixed-radius
`∀`-displacement analogue is provably false, #4270).  The constant is **per-`A`** — *uniform*-in-`A`
continuity of the infinite envelope `globalPseudoMassDist` does **not** follow (the per-pair
Lipschitz constant `(2α+1)K/dist` is not controlled as `diam A → ∞`); see #4320.  The unconditional
headline sandwich is `globalPseudoMassDist_fullSandwich` (#4317).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Lemma 17.5.2 and Theorem 17.5.1 proof,
  pp.~311--312.
-/

namespace IsingModel
namespace Ambient

open Set

/-- **Distance-parametrized per-pair pseudo-mass = fixed-radius pseudo-mass at `r = dist`
(cubic exhaustion).**  For a distinct pair `x ≠ z`, `pseudoMassFromParamsAtPairDist` (profile radius
`latticeDistance d x z`) coincides with `pseudoMassFromParamsAtPair` at that radius.  Both unfold to
`pseudoMassExt hα hpos (correlationInfinite … {x, z})`; specializing to the cubic exhaustion makes
the `Fintype (… edgeSet)` instances canonical on both sides, so the equality is `rfl` after the two
defining rewrites (for a general `Λ` the synthesized vs.\ passed instances differ and the
`pseudoMassExt` `dite` defeq diverges; see #4320).

References: Glimm--Jaffe §17.5, p.~311. -/
theorem pseudoMassFromParamsAtPairDist_eq_atPair_cubic {α d : ℕ} (hα : 1 ≤ α)
    (p : IsingParams ℝ) {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hpos : (0 : ℝ) < (IsingModel.latticeDistance d x z : ℝ)) :
    pseudoMassFromParamsAtPairDist hα (Ambient.cubicExhaustion d) p x z
      = pseudoMassFromParamsAtPair hα hpos d (Ambient.cubicExhaustion d) p x z := by
  rw [pseudoMassFromParamsAtPairDist_of_ne hα (Ambient.cubicExhaustion d) p hxz hpos,
    pseudoMassFromParamsAtPair.eq_def]

/-- **GJ §17.5 conditional per-pair faithful (distance-radius) interval Lipschitz of
`(m⁻(x, z, ·))^{2α+1}`.**  Instantiates the fixed-radius window interval Lipschitz (#4331) at the
per-pair profile radius `ρ := latticeDistance d x z` and rewrites through the bridge.  The Lipschitz
constant `(2α+1)·K/dist(x,z)` carries the faithful `1/dist` normalization of the inverse correlation
length.

References: Glimm--Jaffe §17.5, Theorem 17.5.1 proof, pp.~311--312. -/
theorem pseudoMassFromParamsAtPairDist_pow_succ_lipschitz_on_window_of_profile_lower
    {d α : ℕ} (hα : 1 ≤ α) (hd : 1 ≤ d)
    {J β₁ β₂ : ℝ} (hJ_pos : 0 < J) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ ConvergenceRegion.window d J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hprofile : ∀ β ∈ Set.Icc β₁ β₂,
      pseudoMassG α (IsingModel.latticeDistance d x z : ℝ) (-Real.log (β * J * ↑(2 * d))) ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
    ∃ K : ℝ, 0 < K ∧
      |(pseudoMassFromParamsAtPairDist hα (Ambient.cubicExhaustion d)
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) ^ (2 * α + 1) -
          (pseudoMassFromParamsAtPairDist hα (Ambient.cubicExhaustion d)
            (⟨J, 0, β₁⟩ : IsingParams ℝ) x z) ^ (2 * α + 1)| ≤
        ↑(2 * α + 1) * K / (IsingModel.latticeDistance d x z : ℝ) * (β₂ - β₁) := by
  have hpos : (0 : ℝ) < (IsingModel.latticeDistance d x z : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (fun h => hxz ((IsingModel.latticeDistance_eq_zero_iff d x z).mp h))
  obtain ⟨K, hK, hbound⟩ :=
    lemma_17_5_2_pseudoMass_pow_succ_lipschitz_on_window_of_profile_lower
      hα hd hpos hJ_pos hβ₁₂ hIcc hxz hprofile
  refine ⟨K, hK, ?_⟩
  rw [pseudoMassFromParamsAtPairDist_eq_atPair_cubic hα _ hxz hpos,
    pseudoMassFromParamsAtPairDist_eq_atPair_cubic hα _ hxz hpos]
  exact hbound

/-- **GJ §17.5 Lemma 17.5.2(a) conditional finite-region Lipschitz of `m⁻(σ, A)^{2α+1}`.**

For a *fixed* bounded region `A` (with at least one distinct pair) and `Icc β₁ β₂` inside the
convergence window, the faithful per-pair profile lower bounds (one per pair of `A`) yield a single
constant `C > 0` with
`|m⁻(σ₂, A)^{2α+1} − m⁻(σ₁, A)^{2α+1}| ≤ C·(β₂ − β₁)`,
where `m⁻(σ, A) = finiteRegionPseudoMassDist`.  This upgrades the finite-region continuity
(`finiteRegionPseudoMassDist_beta_continuousOn_high_temp`) to Lipschitz, the genuine GJ §17.5
Theorem 17.5.1 intermediate claim restricted to a finite region.

Proof: the `(2α+1)`-power commutes with the defining `Finset.inf'` (odd power is monotone, via
`comp_inf'_eq_inf'_comp`); each per-pair power is interval-Lipschitz with constant `(2α+1)K_q/dist`
(`pseudoMassFromParamsAtPairDist_pow_succ_lipschitz_on_window_of_profile_lower`); the finite
`Finset.sup'` of these constants bounds the infimum's increment via the achieved infimum
(`Finset.exists_mem_eq_inf'` + `Finset.inf'_le`).

**Conditional / Partial.** Per-pair `hprofile` (faithful distance form; `∀`-displacement false,
#4270); the constant is per-`A` (uniform-in-`A` / infinite-envelope continuity does not follow,
#4320).

References: Glimm--Jaffe §17.5, Theorem 17.5.1 proof and Lemma 17.5.2, pp.~311--312. -/
theorem finiteRegionPseudoMassDist_pow_succ_lipschitz_on_window_of_profile_lower
    {d α : ℕ} (hα : 1 ≤ α) (hd : 1 ≤ d)
    {J β₁ β₂ : ℝ} (hJ_pos : 0 < J) (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ ConvergenceRegion.window d J)
    {A : Finset (Fin d → ℤ)} (hA : (finiteRegionDistinctPairs A).Nonempty)
    (hprofile : ∀ q ∈ finiteRegionDistinctPairs A, ∀ β ∈ Set.Icc β₁ β₂,
      pseudoMassG α (IsingModel.latticeDistance d q.1 q.2 : ℝ) (-Real.log (β * J * ↑(2 * d))) ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {q.1, q.2}) :
    ∃ C : ℝ, 0 < C ∧
      |(finiteRegionPseudoMassDist hα (Ambient.cubicExhaustion d)
            (⟨J, 0, β₂⟩ : IsingParams ℝ) A hA) ^ (2 * α + 1) -
          (finiteRegionPseudoMassDist hα (Ambient.cubicExhaustion d)
            (⟨J, 0, β₁⟩ : IsingParams ℝ) A hA) ^ (2 * α + 1)| ≤ C * (β₂ - β₁) := by
  classical
  set pairs := finiteRegionDistinctPairs A with hpairs_def
  -- per-pair power profile.
  set hpow : ℝ → (Fin d → ℤ) × (Fin d → ℤ) → ℝ := fun β q =>
    (pseudoMassFromParamsAtPairDist hα (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) q.1 q.2) ^ (2 * α + 1) with hhpow_def
  -- odd power is monotone, so it commutes with `Finset.inf'`.
  have hmono : Monotone (fun t : ℝ => t ^ (2 * α + 1)) :=
    (Odd.strictMono_pow ⟨α, by ring⟩).monotone
  have hginf : ∀ a b : ℝ, (a ⊓ b) ^ (2 * α + 1) = a ^ (2 * α + 1) ⊓ b ^ (2 * α + 1) := by
    intro a b
    rcases le_total a b with h | h
    · rw [inf_eq_left.mpr h, inf_eq_left.mpr (hmono h)]
    · rw [inf_eq_right.mpr h, inf_eq_right.mpr (hmono h)]
  have hpow_eq : ∀ β,
      (finiteRegionPseudoMassDist hα (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) A hA) ^ (2 * α + 1)
        = pairs.inf' hA (hpow β) := by
    intro β
    unfold finiteRegionPseudoMassDist
    rw [Finset.comp_inf'_eq_inf'_comp hA (fun t => t ^ (2 * α + 1)) hginf]
    rfl
  -- per-pair interval Lipschitz constants (existential, extracted by `choose!`).
  have hper : ∀ q ∈ pairs, ∃ Cq : ℝ, 0 < Cq ∧
      |hpow β₂ q - hpow β₁ q| ≤ Cq * (β₂ - β₁) := by
    intro q hq
    obtain ⟨_hq1, _hq2, hxz⟩ := mem_finiteRegionDistinctPairs.mp hq
    have hpos : (0 : ℝ) < (IsingModel.latticeDistance d q.1 q.2 : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero
        (fun h => hxz ((IsingModel.latticeDistance_eq_zero_iff d q.1 q.2).mp h))
    obtain ⟨K, hK, hb⟩ :=
      pseudoMassFromParamsAtPairDist_pow_succ_lipschitz_on_window_of_profile_lower
        hα hd hJ_pos hβ₁₂ hIcc hxz (hprofile q hq)
    exact ⟨↑(2 * α + 1) * K / (IsingModel.latticeDistance d q.1 q.2 : ℝ),
      by positivity, hb⟩
  choose! Cq hCqpos hCqbd using hper
  -- the single constant `C := sup' over the finitely many pairs`.
  refine ⟨pairs.sup' hA Cq, ?_, ?_⟩
  · obtain ⟨q₀, hq₀⟩ := hA
    exact lt_of_lt_of_le (hCqpos q₀ hq₀) (Finset.le_sup' Cq hq₀)
  · set C := pairs.sup' hA Cq with hC_def
    have hβsub_nn : 0 ≤ β₂ - β₁ := by linarith
    -- per-pair bound by the uniform `C`.
    have hperC : ∀ q ∈ pairs, |hpow β₂ q - hpow β₁ q| ≤ C * (β₂ - β₁) := by
      intro q hq
      refine le_trans (hCqbd q hq) ?_
      exact mul_le_mul_of_nonneg_right (Finset.le_sup' Cq hq) hβsub_nn
    rw [hpow_eq β₂, hpow_eq β₁]
    -- infimum increment bounded by the worst per-pair increment.
    rw [abs_le]
    constructor
    · -- -(C·Δ) ≤ inf'(hpow β₂) - inf'(hpow β₁)
      obtain ⟨q₂, hq₂_mem, hq₂_eq⟩ := Finset.exists_mem_eq_inf' hA (hpow β₂)
      have h1 : pairs.inf' hA (hpow β₁) ≤ hpow β₁ q₂ := Finset.inf'_le _ hq₂_mem
      have h2 : |hpow β₂ q₂ - hpow β₁ q₂| ≤ C * (β₂ - β₁) := hperC q₂ hq₂_mem
      rw [hq₂_eq]
      have := (abs_le.mp h2).1
      linarith
    · -- inf'(hpow β₂) - inf'(hpow β₁) ≤ C·Δ
      obtain ⟨q₁, hq₁_mem, hq₁_eq⟩ := Finset.exists_mem_eq_inf' hA (hpow β₁)
      have h1 : pairs.inf' hA (hpow β₂) ≤ hpow β₂ q₁ := Finset.inf'_le _ hq₁_mem
      have h2 : |hpow β₂ q₁ - hpow β₁ q₁| ≤ C * (β₂ - β₁) := hperC q₁ hq₁_mem
      rw [hq₁_eq]
      have := (abs_le.mp h2).2
      linarith

end Ambient
end IsingModel
