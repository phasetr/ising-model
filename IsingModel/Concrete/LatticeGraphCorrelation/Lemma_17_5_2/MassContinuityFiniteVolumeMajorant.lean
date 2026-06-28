import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.FiniteRegionPseudoMassDistFV

/-!
# GJ §17.5 Theorem 17.5.1 — PR-FV3a: finite-volume correlation majorant (p.312)

The finite-volume correlation profile identity and the GJ p.312 *majorant*: the finite-volume
two-point function `⟨φ(x)φ(z)⟩_{σ,A=volume n}` equals `pseudoMassG` at the per-pair FV mass, and is
therefore bounded above by `pseudoMassG` at the **finite-region** mass `m⁻_FV(σ,A)` — the smallest
mass over the box, so the largest `pseudoMassG` profile.  This is the brick that makes the FV sharp
β-derivative ratio work at the single scale `m⁻_FV(σ,A)`:  every in-box correlation decays at rate
`≥ m⁻_FV(σ,A)`, so the cross-sum is bounded by the `m⁻_FV(σ,A)`-scaled HLS convolution with **no**
`exp` blow-up (the attained-inf hypothesis `hbind` of the infinite-volume route is automatic here).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Finite-volume correlation profile identity** (GJ p.312): for a distinct in-box pair `x ≠ z`
(`{x,z} ⊆ volume n`) at `0 < J`, `0 < β`, the finite-volume two-point function equals `pseudoMassG`
at the per-pair FV mass:
`⟨φ(x)φ(z)⟩_{σ,A} = pseudoMassG α (d(x,z)) (pseudoMassFromParamsAtPairFV …)`.
Direct from `pseudoMass_spec` (the defining equation of `pseudoMass`) through the FV per-pair
definition (`pseudoMassFromParamsAtPairFV_of_ne` + `pseudoMassExt_of_mem`) and the active range
(`correlationAlongExhaustion_cubicExhaustion_pair_active`). -/
theorem correlationAlongExhaustion_eq_pseudoMassG_finiteVolume {α d : ℕ} (hα : 1 ≤ α) {J β : ℝ}
    (hJ : 0 < J) (hβ : 0 < β) {n : ℕ} {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hsub : ({x, z} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n) :
    Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n
      = pseudoMassG α (IsingModel.latticeDistance d x z : ℝ)
          (pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z) := by
  have hpos : (0 : ℝ) < (IsingModel.latticeDistance d x z : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (fun h => hxz ((IsingModel.latticeDistance_eq_zero_iff d x z).mp h))
  have hc : Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n ∈ Set.Ioo (0 : ℝ) 2 :=
    correlationAlongExhaustion_cubicExhaustion_pair_active hJ hβ hxz hsub
  rw [pseudoMassFromParamsAtPairFV_of_ne hα (⟨J, 0, β⟩ : IsingParams ℝ) n hxz hpos,
    pseudoMassExt_of_mem hα hpos hc]
  exact (pseudoMass_spec hα hpos hc).symm

/-- **Finite-volume correlation majorant** (GJ p.312): the finite-volume two-point function of a
distinct in-box pair is bounded above by `pseudoMassG` at the finite-region mass `m⁻_FV(σ,A)`:
`⟨φ(x)φ(z)⟩_{σ,A} ≤ pseudoMassG α (d(x,z)) (m⁻_FV(σ,A))`.
The per-pair FV mass dominates the finite-region infimum (`finiteRegionPseudoMassDistFV_le_of_mem`),
and `pseudoMassG` is antitone in the mass (`pseudoMassG_antitoneOn`), so the profile at the smaller
`m⁻_FV(σ,A)` dominates; combined with the profile identity. -/
theorem correlationAlongExhaustion_le_pseudoMassG_finiteRegionFV {α d : ℕ} (hα : 1 ≤ α) {J β : ℝ}
    (hJ : 0 < J) (hβ : 0 < β) {n : ℕ}
    (hA : (finiteRegionDistinctPairs ((cubicExhaustion d).volume n)).Nonempty)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hsub : ({x, z} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n) :
    Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n
      ≤ pseudoMassG α (IsingModel.latticeDistance d x z : ℝ)
          (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA) := by
  have hpos : (0 : ℝ) < (IsingModel.latticeDistance d x z : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (fun h => hxz ((IsingModel.latticeDistance_eq_zero_iff d x z).mp h))
  have hx : x ∈ (cubicExhaustion d).volume n := hsub (Finset.mem_insert_self x {z})
  have hz : z ∈ (cubicExhaustion d).volume n :=
    hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self z))
  have hpair_mem : (x, z) ∈ finiteRegionDistinctPairs ((cubicExhaustion d).volume n) :=
    mem_finiteRegionDistinctPairs.mpr ⟨hx, hz, hxz⟩
  rw [correlationAlongExhaustion_eq_pseudoMassG_finiteVolume hα hJ hβ hxz hsub]
  have hle : finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA
      ≤ pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z :=
    finiteRegionPseudoMassDistFV_le_of_mem hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA hpair_mem
  exact pseudoMassG_antitoneOn hα hpos
    (Set.mem_Ici.mpr (finiteRegionPseudoMassDistFV_pos hα hJ hβ hA).le)
    (Set.mem_Ici.mpr (pseudoMassFromParamsAtPairFV_nonneg hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z))
    hle

end Ambient
end IsingModel
