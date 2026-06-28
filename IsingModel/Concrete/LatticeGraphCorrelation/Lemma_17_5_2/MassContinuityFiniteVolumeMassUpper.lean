import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityFiniteVolumeMassLower
import IsingModel.Concrete.LatticeGraphCorrelation.BaseCorrelationAlongExSubsetMono
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationExhaustionLimitsCubicMonotone

/-!
# GJ §17.5 Theorem 17.5.1 — PR-FV4b-prep: upper bound on the finite-volume finite-region mass

The finite-volume finite-region pseudo-mass is bounded **above by a single constant uniform in `n`
and in `β ∈ [β₁,β₂]`**: `finiteRegionPseudoMassDistFV(σ, volume n) ≤ Mwitness`, where
`Mwitness = m_FV((0, e₀), stage 1, β₁)` is the per-pair FV mass of the fixed stage-1 adjacent
witness pair `(0, e₀)` at `β₁`.

Chain: `m⁻_FV(σ,n) ≤ m_FV(witness, n, β)` (`finiteRegionPseudoMassDistFV_le_of_mem`, witness in the
box for `n ≥ 1`) `≤ m_FV(witness, 1, β)` (`correlationAlongExhaustion` monotone in `n`,
`pseudoMassExt` antitone) `≤ m_FV(witness, 1, β₁)` (monotone in `β`, antitone).  The naive
`tanh(βJ)/2^edges` edge bound does NOT give a uniform `Mmax` (the `2^edges` grows with `n`); the
monotone-decreasing-in-`n`/`β` route does.  With the lower bound (#4380) this provides the two-sided
`mmin ≤ m⁻_FV(σ,n) ≤ Mwitness` needed for the GJ p.312 uniform-in-`A` Lipschitz constant.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Upper bound: `finiteRegionPseudoMassDistFV(volume n) ≤ m_FV(witness, 1, β₁)`** (GJ p.312),
uniform in `n ≥ 1` and `β ∈ [β₁,β₂]`.  The fixed adjacent witness pair `(0, e₀)` lies in every box
`n ≥ 1`, so `m⁻_FV(σ,n) ≤ m_FV(witness,n,β)`; the FV correlation increases in `n` and `β`, so the
per-pair FV mass decreases, giving `m_FV(witness,n,β) ≤ m_FV(witness,1,β) ≤ m_FV(witness,1,β₁)`. -/
theorem finiteRegionPseudoMassDistFV_le_witness {α d : ℕ} (hα : 1 ≤ α) (hd : 1 ≤ d)
    {J β₁ β₂ : ℝ} (hJ : 0 < J) (hβ₁ : 0 < β₁) {n : ℕ} (hn : 1 ≤ n)
    {β : ℝ} (hβmem : β ∈ Set.Icc β₁ β₂)
    (hA : (finiteRegionDistinctPairs ((cubicExhaustion d).volume n)).Nonempty) :
    finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA
      ≤ pseudoMassFromParamsAtPairFV hα (⟨J, 0, β₁⟩ : IsingParams ℝ) 1
          (0 : Fin d → ℤ) (Pi.single (⟨0, hd⟩ : Fin d) (1 : ℤ)) := by
  classical
  set w₂ : Fin d → ℤ := Pi.single (⟨0, hd⟩ : Fin d) (1 : ℤ) with hw₂_def
  have hβ : 0 < β := lt_of_lt_of_le hβ₁ hβmem.1
  -- witness facts.
  have hne : (0 : Fin d → ℤ) ≠ w₂ := by
    intro h
    have h0 := congrFun h ⟨0, hd⟩
    rw [hw₂_def] at h0
    simp at h0
  have hpos : (0 : ℝ) < (IsingModel.latticeDistance d 0 w₂ : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (fun h => hne ((IsingModel.latticeDistance_eq_zero_iff d 0 w₂).mp h))
  have hw1m1 : (0 : Fin d → ℤ) ∈ (cubicExhaustion d).volume 1 := by
    change (0 : Fin d → ℤ) ∈ cubicBox d 1; rw [mem_cubicBox]; intro i; norm_num
  have hw2m1 : w₂ ∈ (cubicExhaustion d).volume 1 := by
    change w₂ ∈ cubicBox d 1; rw [mem_cubicBox]; intro i; rw [hw₂_def]
    by_cases hi : i = ⟨0, hd⟩
    · subst hi; simp
    · rw [Pi.single_eq_of_ne hi]; norm_num
  have hmono_vol : (cubicExhaustion d).volume 1 ⊆ (cubicExhaustion d).volume n :=
    (cubicExhaustion d).mono hn
  have hw1mn : (0 : Fin d → ℤ) ∈ (cubicExhaustion d).volume n := hmono_vol hw1m1
  have hw2mn : w₂ ∈ (cubicExhaustion d).volume n := hmono_vol hw2m1
  have hsub_n : ({0, w₂} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n := by
    intro y hy; rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact hw1mn
    · exact hw2mn
  have hsub_1 : ({0, w₂} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume 1 := by
    intro y hy; rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact hw1m1
    · exact hw2m1
  have hpair_n : ((0 : Fin d → ℤ), w₂) ∈ finiteRegionDistinctPairs ((cubicExhaustion d).volume n) :=
    mem_finiteRegionDistinctPairs.mpr ⟨hw1mn, hw2mn, hne⟩
  -- active ranges.
  have hact_nβ : Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {0, w₂} n ∈ Set.Ioo (0 : ℝ) 2 :=
    correlationAlongExhaustion_cubicExhaustion_pair_active hJ hβ hne hsub_n
  have hact_1β : Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {0, w₂} 1 ∈ Set.Ioo (0 : ℝ) 2 :=
    correlationAlongExhaustion_cubicExhaustion_pair_active hJ hβ hne hsub_1
  have hact_1β₁ : Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β₁⟩ : IsingParams ℝ) {0, w₂} 1 ∈ Set.Ioo (0 : ℝ) 2 :=
    correlationAlongExhaustion_cubicExhaustion_pair_active hJ hβ₁ hne hsub_1
  -- monotonicity of the correlation in `n` and `β`.
  have hferro : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ.le, le_refl 0, hβ⟩
  have hmono_n : Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {0, w₂} 1
      ≤ Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {0, w₂} n :=
    correlationAlongExhaustion_latticeGraph_cubicExhaustion_monotone d (⟨J, 0, β⟩ : IsingParams ℝ)
      hferro {0, w₂} hn
  have hmono_β : Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β₁⟩ : IsingParams ℝ) {0, w₂} 1
      ≤ Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {0, w₂} 1 :=
    correlationAlongExhaustion_latticeGraph_cubicExhaustion_monotone_beta d hJ.le (le_refl 0)
      {0, w₂} hβ₁ hβmem.1 1
  -- step 1: `m⁻_FV(σ,n) ≤ m_FV(witness, n, β)`.
  have hstep1 : finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA
      ≤ pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n 0 w₂ :=
    finiteRegionPseudoMassDistFV_le_of_mem hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA hpair_n
  -- step 2: `m_FV(witness, n, β) ≤ m_FV(witness, 1, β)`.
  have hstep2 : pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n 0 w₂
      ≤ pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) 1 0 w₂ := by
    rw [pseudoMassFromParamsAtPairFV_of_ne hα (⟨J, 0, β⟩ : IsingParams ℝ) n hne hpos,
      pseudoMassFromParamsAtPairFV_of_ne hα (⟨J, 0, β⟩ : IsingParams ℝ) 1 hne hpos]
    exact pseudoMassExt_antitoneOn hα hpos hact_1β hact_nβ hmono_n
  -- step 3: `m_FV(witness, 1, β) ≤ m_FV(witness, 1, β₁)`.
  have hstep3 : pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) 1 0 w₂
      ≤ pseudoMassFromParamsAtPairFV hα (⟨J, 0, β₁⟩ : IsingParams ℝ) 1 0 w₂ := by
    rw [pseudoMassFromParamsAtPairFV_of_ne hα (⟨J, 0, β⟩ : IsingParams ℝ) 1 hne hpos,
      pseudoMassFromParamsAtPairFV_of_ne hα (⟨J, 0, β₁⟩ : IsingParams ℝ) 1 hne hpos]
    exact pseudoMassExt_antitoneOn hα hpos hact_1β₁ hact_1β hmono_β
  exact hstep1.trans (hstep2.trans hstep3)

end Ambient
end IsingModel
