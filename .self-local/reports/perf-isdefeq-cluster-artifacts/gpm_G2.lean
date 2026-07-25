import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.FiniteRegionPseudoMassDistContinuity
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.GlobalPseudoMassDist

/-!
# GJ §17.5 Theorem 17.5.1 — bridge: `globalPseudoMassDist = inf over the cubic exhaustion`

GJ p.312: `m⁻(σ) = inf_A m⁻(σ,A) = lim_{A↑ℝ^d} m⁻(σ,A)`.  This file proves the Lean form of that
identity for the cubic exhaustion: the system pseudo-mass `globalPseudoMassDist` (an `sInf` over
*all* active distinct pairs) equals the infimum, over the cubic stages `n`, of the finite-region
pseudo-masses `finiteRegionPseudoMassDist (volume n)` (each a *finite, attained* `Finset.inf'` over
the pairs inside the box).

This is the bridge that lets the `A↑` step
(`abs_csInf_range_sub_csInf_range_le`, the inf-of-uniformly-Lipschitz-is-Lipschitz lemma) act on
the genuine `globalPseudoMassDist`: once `finiteRegionPseudoMassDist(σ, volume n)^{2α+1}` is
Lipschitz with a constant uniform in `n`, the bridge + that lemma give Lipschitz of
`globalPseudoMassDist^{2α+1}`.

The index is the subtype of stages that already contain a distinct pair (`cubicMassIndex`); stage
`0` is a single point and has none, so the raw `ℕ` index is wrong.  Nonemptiness holds from `d ≥ 1`
(`cubicBox d 1` contains the distinct pair `(0, Pi.single ⟨0,_⟩ 1)`).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Cubic mass index**: the cubic-exhaustion stages `n` whose box `volume n` already contains a
distinct pair (so `finiteRegionPseudoMassDist` is defined there).  The nonemptiness predicate is
`β`-independent, so the same index type serves both endpoints in the `A↑` Lipschitz step. -/
abbrev cubicMassIndex (d : ℕ) : Type :=
  {n : ℕ // (finiteRegionDistinctPairs ((cubicExhaustion d).volume n)).Nonempty}

/-- **Stage 1 of the cubic exhaustion contains a distinct pair** (for `d ≥ 1`): `0` and
`Pi.single ⟨0,_⟩ 1` both lie in `cubicBox d 1` and differ at coordinate `0`. -/
theorem finiteRegionDistinctPairs_cubicVolume_one_nonempty {d : ℕ} (hd : 1 ≤ d) :
    (finiteRegionDistinctPairs ((cubicExhaustion d).volume 1)).Nonempty := by
  classical
  refine ⟨(0, Pi.single ⟨0, hd⟩ 1), ?_⟩
  rw [mem_finiteRegionDistinctPairs]
  refine ⟨?_, ?_, ?_⟩
  · change (0 : Fin d → ℤ) ∈ cubicBox d 1
    rw [mem_cubicBox]; intro i; norm_num
  · change (Pi.single ⟨0, hd⟩ (1 : ℤ)) ∈ cubicBox d 1
    rw [mem_cubicBox]; intro i
    by_cases hi : i = ⟨0, hd⟩
    · subst hi; simp
    · rw [Pi.single_eq_of_ne hi]; norm_num
  · intro h
    have h0 := congrFun h ⟨0, hd⟩
    simp at h0

/-- The cubic mass index is nonempty for `d ≥ 1`. -/
theorem cubicMassIndex_nonempty {d : ℕ} (hd : 1 ≤ d) : Nonempty (cubicMassIndex d) :=
  ⟨⟨1, finiteRegionDistinctPairs_cubicVolume_one_nonempty hd⟩⟩

/-- **GJ p.312 bridge — `globalPseudoMassDist` is the cubic-exhaustion infimum of the finite-region
pseudo-masses**: for `0 < J`, `0 < β`,
`globalPseudoMassDist hα (cubicExhaustion d) ⟨J,0,β⟩
  = sInf (range (n ↦ finiteRegionPseudoMassDist hα (cubicExhaustion d) ⟨J,0,β⟩ (volume n) n.2))`
over the cubic mass index.

`≤`: each finite-region inf' is attained at an in-box pair, which is active at `β > 0`, so
`globalPseudoMassDist ≤` it (`globalPseudoMassDist_le_of_active`); `le_csInf` over the range.
`≥`: any active pair `(x,z)` lies in `volume N` for large `N` (`Exhaustion.exhaust`), so
`finiteRegion(volume N) ≤ pseudoMass(x,z)` (`Finset.inf'_le_of_le`), making
`sInf (range …)` a lower bound of `globalPseudoMassDistSet`; `le_csInf`. -/
theorem globalPseudoMassDist_eq_csInf_finiteRegion_cubic {α d : ℕ} (hα : 1 ≤ α) (hd : 1 ≤ d)
    {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) :
    globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      = sInf (Set.range (fun n : cubicMassIndex d =>
          finiteRegionPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
            ((cubicExhaustion d).volume n.1) n.2)) := by
  classical
  haveI : Nonempty (cubicMassIndex d) := cubicMassIndex_nonempty hd
  set Λ := cubicExhaustion d with hΛ
  set p : IsingParams ℝ := ⟨J, 0, β⟩ with hp
  set f : cubicMassIndex d → ℝ := fun n =>
    finiteRegionPseudoMassDist hα Λ p (Λ.volume n.1) n.2 with hf
  have hβJ_pos : 0 < β * J := mul_pos hβ hJ
  -- `range f` is bounded below by `0`.
  have hbdd : BddBelow (Set.range f) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (finiteRegionPseudoMassDist_pos_of_betaJ_pos hα Λ (Λ.volume n.1) n.2 hJ hβ).le
  have hrange_ne : (Set.range f).Nonempty := Set.range_nonempty f
  refine le_antisymm ?_ ?_
  · -- `globalPseudoMassDist ≤ sInf (range f)`.
    refine le_csInf hrange_ne ?_
    rintro _ ⟨n, rfl⟩
    obtain ⟨q, hq_mem, hq_eq⟩ :=
      Finset.exists_mem_eq_inf' n.2 (fun q => pseudoMassFromParamsAtPairDist hα Λ p q.1 q.2)
    have hq_ne : q.1 ≠ q.2 := (mem_finiteRegionDistinctPairs.mp hq_mem).2.2
    have hmem : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {q.1, q.2}
        ∈ Set.Ioo (0 : ℝ) 2 :=
      correlationInfinite_pair_active_of_betaJ_pos_exhaustion Λ hβ hβJ_pos q.1 q.2 hq_ne
    have hact : ActivePseudoMassPair Λ p q.1 q.2 := ⟨hq_ne, hmem⟩
    change globalPseudoMassDist hα Λ p ≤ f n
    rw [hf]
    change globalPseudoMassDist hα Λ p ≤ finiteRegionPseudoMassDist hα Λ p (Λ.volume n.1) n.2
    rw [finiteRegionPseudoMassDist, hq_eq]
    exact globalPseudoMassDist_le_of_active hα Λ p hact
  · -- `sInf (range f) ≤ globalPseudoMassDist`.
    -- `globalPseudoMassDistSet` is nonempty (the stage-1 witness pair is active).
    have hset_ne : (globalPseudoMassDistSet hα Λ p).Nonempty := by
      obtain ⟨q, hq_mem⟩ := finiteRegionDistinctPairs_cubicVolume_one_nonempty hd
      have hq_ne : q.1 ≠ q.2 := (mem_finiteRegionDistinctPairs.mp hq_mem).2.2
      have hmem : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {q.1, q.2}
          ∈ Set.Ioo (0 : ℝ) 2 :=
        correlationInfinite_pair_active_of_betaJ_pos_exhaustion Λ hβ hβJ_pos q.1 q.2 hq_ne
      exact ⟨pseudoMassFromParamsAtPairDist hα Λ p q.1 q.2, q.1, q.2, ⟨hq_ne, hmem⟩, rfl⟩
    rw [globalPseudoMassDist]
    refine le_csInf hset_ne ?_
    rintro m ⟨x, z, hact, rfl⟩
    -- the active pair lies in `volume N` for large `N`.
    obtain ⟨N, hN⟩ := Λ.exhaust ({x, z} : Finset (Fin d → ℤ))
    have hsub : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume N := hN N le_rfl
    have hx : x ∈ Λ.volume N := hsub (Finset.mem_insert_self x {z})
    have hz : z ∈ Λ.volume N := hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self z))
    have hpair_mem : (x, z) ∈ finiteRegionDistinctPairs (Λ.volume N) :=
      mem_finiteRegionDistinctPairs.mpr ⟨hx, hz, hact.1⟩
    have hne : (finiteRegionDistinctPairs (Λ.volume N)).Nonempty := ⟨(x, z), hpair_mem⟩
    have h1 : f ⟨N, hne⟩ ≤ pseudoMassFromParamsAtPairDist hα Λ p x z := by
      rw [hf]
      change finiteRegionPseudoMassDist hα Λ p (Λ.volume N) hne
        ≤ pseudoMassFromParamsAtPairDist hα Λ p x z
      rw [finiteRegionPseudoMassDist]
      exact Finset.inf'_le _ hpair_mem
    exact (csInf_le hbdd ⟨⟨N, hne⟩, rfl⟩).trans h1

end Ambient
end IsingModel
