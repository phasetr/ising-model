import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.FiniteRegionPseudoMassDistFV
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.GlobalPseudoMassDistCubicInf
import IsingModel.Concrete.LatticeGraphCorrelation.UniformMagAlongExConvergenceCiSup

/-!
# GJ §17.5 Theorem 17.5.1 — PR-FV4b-prep: lower bound on the finite-volume finite-region mass

The finite-volume finite-region pseudo-mass dominates the infinite-volume system pseudo-mass:
`globalPseudoMassDist(σ) ≤ finiteRegionPseudoMassDistFV(σ, volume n)`, for `0 < J`, `0 < β`.

The per-pair FV mass dominates the infinite-volume per-pair mass (`correlationΛ ≤
correlationInfinite` + `pseudoMassExt` antitone), and the infinite-volume per-pair mass dominates the
system inf (`globalPseudoMassDist_le_of_active`); the finite `inf'` inherits it.  With the strict
lower bound `globalPseudoMassDist ≥ globalPseudoMassDistRestrictedRate` (#4360), this gives the
interval-uniform lower bound `mmin ≤ m⁻_FV(σ, volume n)` needed for the mass-uniform convolution
constant of the GJ p.312 uniform Lipschitz estimate.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Per-pair: the finite-volume mass dominates the infinite-volume mass**: for a distinct in-box
pair `x ≠ z` (`{x,z} ⊆ volume n`) at `0 < J`, `0 < β`,
`pseudoMassFromParamsAtPairDist ≤ pseudoMassFromParamsAtPairFV`.  The FV correlation is `≤` the
infinite one (`correlationAlongExhaustion_le_correlationInfinite_latticeGraph`) and `pseudoMassExt`
is antitone, so the smaller (FV) correlation gives the larger pseudo-mass. -/
theorem pseudoMassFromParamsAtPairDist_le_pseudoMassFromParamsAtPairFV {α d : ℕ} (hα : 1 ≤ α)
    {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) {n : ℕ} {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hsub : ({x, z} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n) :
    pseudoMassFromParamsAtPairDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) x z
      ≤ pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z := by
  have hβJ_pos : 0 < β * J := mul_pos hβ hJ
  have hpos : (0 : ℝ) < (IsingModel.latticeDistance d x z : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (fun h => hxz ((IsingModel.latticeDistance_eq_zero_iff d x z).mp h))
  have hcFV : Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n ∈ Set.Ioo (0 : ℝ) 2 :=
    correlationAlongExhaustion_cubicExhaustion_pair_active hJ hβ hxz hsub
  have hcInf : Ambient.correlationInfinite (IsingModel.latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} ∈ Set.Ioo (0 : ℝ) 2 :=
    correlationInfinite_pair_active_of_betaJ_pos_exhaustion (cubicExhaustion d) hβ hβJ_pos x z hxz
  have hle : Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n
      ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} :=
    correlationAlongExhaustion_le_correlationInfinite_latticeGraph d (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n
  rw [pseudoMassFromParamsAtPairDist_of_ne hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      hxz hpos, pseudoMassFromParamsAtPairFV_of_ne hα (⟨J, 0, β⟩ : IsingParams ℝ) n hxz hpos]
  exact pseudoMassExt_antitoneOn hα hpos hcFV hcInf hle

/-- **Lower bound: `globalPseudoMassDist ≤ finiteRegionPseudoMassDistFV(volume n)`** (GJ p.312):
for `0 < J`, `0 < β`, the finite-volume finite-region mass dominates the system pseudo-mass.  Each
contributing in-box pair is active (`β > 0`), so `globalPseudoMassDist ≤ m⁻∞(pair) ≤ m_FV(pair)`
(`globalPseudoMassDist_le_of_active` + the per-pair domination above); `Finset.le_inf'_iff`. -/
theorem globalPseudoMassDist_le_finiteRegionPseudoMassDistFV {α d : ℕ} (hα : 1 ≤ α)
    {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) {n : ℕ}
    (hA : (finiteRegionDistinctPairs ((cubicExhaustion d).volume n)).Nonempty) :
    globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA := by
  have hβJ_pos : 0 < β * J := mul_pos hβ hJ
  unfold finiteRegionPseudoMassDistFV
  rw [Finset.le_inf'_iff]
  intro q hq
  obtain ⟨hq1, hq2, hq_ne⟩ := mem_finiteRegionDistinctPairs.mp hq
  have hsub : ({q.1, q.2} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n := by
    intro w hw; rw [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hq1
    · exact hq2
  have hmem : Ambient.correlationInfinite (IsingModel.latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {q.1, q.2} ∈ Set.Ioo (0 : ℝ) 2 :=
    correlationInfinite_pair_active_of_betaJ_pos_exhaustion (cubicExhaustion d) hβ hβJ_pos
      q.1 q.2 hq_ne
  have hact : ActivePseudoMassPair (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) q.1 q.2 :=
    ⟨hq_ne, hmem⟩
  exact (globalPseudoMassDist_le_of_active hα (cubicExhaustion d) _ hact).trans
    (pseudoMassFromParamsAtPairDist_le_pseudoMassFromParamsAtPairFV hα hJ hβ hq_ne hsub)

end Ambient
end IsingModel
