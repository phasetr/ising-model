import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.FiniteRegionPseudoMassDistFV
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.GlobalPseudoMassDistCubicInf
import IsingModel.Concrete.LatticeGraphCorrelation.UniformMagAlongExConvergenceCiSup
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationExhaustionLimitsAlongExhaustion

/-!
# GJ §17.5 Theorem 17.5.1 — PR-FV2: `globalPseudoMassDist = inf over the cubic exhaustion` (FV form)

The finite-volume analogue of `globalPseudoMassDist_eq_csInf_finiteRegion_cubic`: the system
pseudo-mass equals the cubic-exhaustion infimum of the **finite-volume** finite-region
pseudo-masses `finiteRegionPseudoMassDistFV (volume n)`.  This is the bridge that lets the capstone
act on `globalPseudoMassDist` once the FV finite-region power is uniformly Lipschitz (FV Step-1).

`≥`: the FV correlation is `≤` the infinite-volume one (GKS volume monotonicity), and
`pseudoMassExt` is antitone, so `m⁻_FV(x,z,n) ≥ m⁻∞(x,z) ≥ globalPseudoMassDist`; `inf'`/`sInf`
inherit it.
`≤`: for any active pair `(x,z)`, `m⁻_FV(x,z,n) → m⁻∞(x,z)` (FV correlation `→` infinite,
`pseudoMassExt` continuous), and `finiteRegion_FV(volume n) ≤ m⁻_FV(x,z,n)` eventually, so
`sInf ≤ m⁻∞(x,z)` for every pair, hence `≤ globalPseudoMassDist`.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real Filter Topology

/-- **Finite-volume finite-region pseudo-mass is `≤` any contributing in-box pair's FV pseudo-mass**
(`Finset.inf'_le`).  Isolated as a lemma so the heavy `pseudoMassExt`/`correlationAlongExhaustion`
defeq check happens once, outside the bridge's `set`-folded context. -/
private theorem finiteRegionPseudoMassDistFV_le_pair {α d : ℕ} (hα : 1 ≤ α) (p : IsingParams ℝ)
    (n : ℕ) (hA : (finiteRegionDistinctPairs ((cubicExhaustion d).volume n)).Nonempty)
    {x z : Fin d → ℤ}
    (hmem : (x, z) ∈ finiteRegionDistinctPairs ((cubicExhaustion d).volume n)) :
    finiteRegionPseudoMassDistFV hα p n hA ≤ pseudoMassFromParamsAtPairFV hα p n x z := by
  unfold finiteRegionPseudoMassDistFV
  exact Finset.inf'_le (fun q => pseudoMassFromParamsAtPairFV hα p n q.1 q.2) hmem

/-- **GJ p.312 bridge, finite-volume form**: `globalPseudoMassDist` is the cubic-exhaustion infimum
of the finite-volume finite-region pseudo-masses.  See the module docstring for the two
directions. -/
theorem globalPseudoMassDist_eq_csInf_finiteRegionFV_cubic {α d : ℕ} (hα : 1 ≤ α) (hd : 1 ≤ d)
    {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) :
    globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      = sInf (Set.range (fun n : cubicMassIndex d =>
          finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n.1 n.2)) := by
  classical
  haveI : Nonempty (cubicMassIndex d) := cubicMassIndex_nonempty hd
  set Λ := cubicExhaustion d with hΛ
  set p : IsingParams ℝ := ⟨J, 0, β⟩ with hp
  set f : cubicMassIndex d → ℝ := fun n => finiteRegionPseudoMassDistFV hα p n.1 n.2 with hf
  have hβJ_pos : 0 < β * J := mul_pos hβ hJ
  have hf_distpos : ∀ {x z : Fin d → ℤ}, x ≠ z → (0 : ℝ) < (latticeDistance d x z : ℝ) :=
    fun {x z} hxz => by
      exact_mod_cast Nat.pos_of_ne_zero
        (fun h => hxz ((IsingModel.latticeDistance_eq_zero_iff d x z).mp h))
  -- per-pair: FV mass ≥ infinite-volume mass (antitone in the correlation, FV correlation ≤ ∞).
  have hFV_ge_inf : ∀ {x z : Fin d → ℤ} (hxz : x ≠ z) {n : ℕ},
      ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume n →
      pseudoMassFromParamsAtPairDist hα Λ p x z ≤ pseudoMassFromParamsAtPairFV hα p n x z := by
    intro x z hxz n hsub
    have hpos := hf_distpos hxz
    have hcFV : Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {x, z} n
        ∈ Set.Ioo (0 : ℝ) 2 :=
      correlationAlongExhaustion_cubicExhaustion_pair_active hJ hβ hxz hsub
    have hcInf : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
        ∈ Set.Ioo (0 : ℝ) 2 :=
      correlationInfinite_pair_active_of_betaJ_pos_exhaustion Λ hβ hβJ_pos x z hxz
    have hle : Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {x, z} n
        ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} :=
      correlationAlongExhaustion_le_correlationInfinite_latticeGraph d Λ p {x, z} n
    rw [pseudoMassFromParamsAtPairDist_of_ne hα Λ p hxz hpos,
      pseudoMassFromParamsAtPairFV_of_ne hα p n hxz hpos]
    exact pseudoMassExt_antitoneOn hα hpos hcFV hcInf hle
  -- `range f` is bounded below by `0`.
  have hbdd : BddBelow (Set.range f) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (finiteRegionPseudoMassDistFV_pos hα hJ hβ n.2).le
  have hrange_ne : (Set.range f).Nonempty := Set.range_nonempty f
  refine le_antisymm ?_ ?_
  · -- `globalPseudoMassDist ≤ sInf (range f)`.
    refine le_csInf hrange_ne ?_
    rintro _ ⟨n, rfl⟩
    change globalPseudoMassDist hα Λ p ≤ f n
    rw [hf]
    change globalPseudoMassDist hα Λ p ≤ finiteRegionPseudoMassDistFV hα p n.1 n.2
    unfold finiteRegionPseudoMassDistFV
    rw [Finset.le_inf'_iff]
    intro q hq
    obtain ⟨hq1, hq2, hq_ne⟩ := mem_finiteRegionDistinctPairs.mp hq
    have hsub : ({q.1, q.2} : Finset (Fin d → ℤ)) ⊆ Λ.volume n.1 := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hq1
      · exact hq2
    have hmem : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {q.1, q.2}
        ∈ Set.Ioo (0 : ℝ) 2 :=
      correlationInfinite_pair_active_of_betaJ_pos_exhaustion Λ hβ hβJ_pos q.1 q.2 hq_ne
    have hact : ActivePseudoMassPair Λ p q.1 q.2 := ⟨hq_ne, hmem⟩
    exact (globalPseudoMassDist_le_of_active hα Λ p hact).trans (hFV_ge_inf hq_ne hsub)
  · -- `sInf (range f) ≤ globalPseudoMassDist`.
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
    have hxz : x ≠ z := hact.1
    have hpos := hf_distpos hxz
    -- `m⁻_FV(x,z,n) → m⁻∞(x,z)` as `n → ∞`.
    have hcInf : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
        ∈ Set.Ioo (0 : ℝ) 2 :=
      correlationInfinite_pair_active_of_betaJ_pos_exhaustion Λ hβ hβJ_pos x z hxz
    have htend_corr : Tendsto
        (fun n => Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {x, z} n)
        atTop (nhds (Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z})) := by
      have hferro : Ferromagnetic p := ⟨hJ.le, le_refl 0, hβ⟩
      exact tendsto_correlationAlongExhaustion_correlationInfinite_latticeGraph d p hferro {x, z}
    have hmtend : Tendsto (fun n => pseudoMassFromParamsAtPairFV hα p n x z)
        atTop (nhds (pseudoMassFromParamsAtPairDist hα Λ p x z)) := by
      have hfun : (fun n => pseudoMassFromParamsAtPairFV hα p n x z)
          = (fun n => pseudoMassExt hα hpos
            (Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {x, z} n)) := by
        funext n; exact pseudoMassFromParamsAtPairFV_of_ne hα p n hxz hpos
      rw [hfun, pseudoMassFromParamsAtPairDist_of_ne hα Λ p hxz hpos]
      exact ((pseudoMassExt_continuousAt hα hpos hcInf).tendsto).comp htend_corr
    -- eventually `sInf (range f) ≤ m⁻_FV(x,z,n)`.
    have hev : ∀ᶠ n in atTop, sInf (Set.range f) ≤ pseudoMassFromParamsAtPairFV hα p n x z := by
      obtain ⟨N, hN⟩ := Λ.exhaust ({x, z} : Finset (Fin d → ℤ))
      filter_upwards [eventually_ge_atTop N] with n hn
      have hsub : ({x, z} : Finset (Fin d → ℤ)) ⊆ Λ.volume n := hN n hn
      have hx : x ∈ Λ.volume n := hsub (Finset.mem_insert_self x {z})
      have hz : z ∈ Λ.volume n := hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self z))
      have hpair_mem : (x, z) ∈ finiteRegionDistinctPairs (Λ.volume n) :=
        mem_finiteRegionDistinctPairs.mpr ⟨hx, hz, hxz⟩
      have hne_n : (finiteRegionDistinctPairs (Λ.volume n)).Nonempty := ⟨(x, z), hpair_mem⟩
      have h1 : finiteRegionPseudoMassDistFV hα p n hne_n
          ≤ pseudoMassFromParamsAtPairFV hα p n x z :=
        finiteRegionPseudoMassDistFV_le_pair hα p n hne_n hpair_mem
      exact (csInf_le hbdd ⟨⟨n, hne_n⟩, rfl⟩).trans h1
    exact ge_of_tendsto hmtend hev

end Ambient
end IsingModel
