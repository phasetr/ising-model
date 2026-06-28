import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityFiniteVolumeUniformLipschitz
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.GlobalPseudoMassDistCubicInfFV
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityGlobalPowLipschitz
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityUniformInfLipschitz

/-!
# GJ §17.5 Theorem 17.5.1 — PR-FV5: the system-mass Lipschitz capstone (p.311–312)

The finite-volume capstone.  Combining the uniform-in-`A` finite-region Lipschitz estimate (PR-FV4c,
the same constant `L` for every cubic stage `n`) with the `A ↑ ℤ^d` bridge
`globalPseudoMassDist = inf_n m⁻_FV(σ,volume n)` (FV form, #4369), the **system** pseudo-mass power
`globalPseudoMassDist(σ)^{2α+1}` is Lipschitz on the high-temperature window — the rigorous
Lipschitz-envelope core of GJ Theorem 17.5.1.

The FV form of the conditional capstone `globalPseudoMassDist_pow_succ_lipschitz_of_uniform_finite
Region` (#4366), restated against the FV bridge #4369 (`globalPseudoMassDist_eq_csInf_finiteRegionFV
_cubic`) and the FV finite-region mass.  The `(2α+1)`-power commutes with the `sInf` over stages
(monotone, `sInf_range_pow_of_nonneg`); the increment of the `sInf` is bounded by the uniform
per-stage increment (`abs_csInf_range_sub_csInf_range_le`).

With Lemma 17.5.2 (the sandwich `m⁻ ≤ m ≤ const·m⁻`, already formalized in #4278/#4297) this is GJ's
"from this [the uniform Lipschitz of `m⁻(σ,A)^{2α+1}`] the theorem follows".

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

/-- **GJ §17.5 conditional system-mass Lipschitz, FV form** (p.312): given a region-uniform
finite-region (FV) Lipschitz bound `hunif` (the same `L` for every cubic stage `n`), the system
pseudo-mass power `globalPseudoMassDist(σ)^{2α+1}` is Lipschitz with the same `L`.  FV analogue of
`globalPseudoMassDist_pow_succ_lipschitz_of_uniform_finiteRegion` (#4366), via the FV `A↑` bridge
#4369. -/
theorem globalPseudoMassDist_pow_succ_lipschitz_of_uniform_finiteRegionFV {α d : ℕ} (hα : 1 ≤ α)
    (hd : 1 ≤ d) {J β₁ β₂ L : ℝ} (hJ : 0 < J) (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hunif : ∀ n : cubicMassIndex d,
      |(finiteRegionPseudoMassDistFV hα (⟨J, 0, β₂⟩ : IsingParams ℝ) n.1 n.2) ^ (2 * α + 1)
          - (finiteRegionPseudoMassDistFV hα (⟨J, 0, β₁⟩ : IsingParams ℝ) n.1 n.2) ^ (2 * α + 1)|
        ≤ L * (β₂ - β₁)) :
    |(globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β₂⟩ : IsingParams ℝ)) ^ (2 * α + 1)
        - (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β₁⟩ : IsingParams ℝ)) ^ (2 * α + 1)|
      ≤ L * (β₂ - β₁) := by
  classical
  haveI : Nonempty (cubicMassIndex d) := cubicMassIndex_nonempty hd
  have hβ₂ : 0 < β₂ := lt_of_lt_of_le hβ₁ hβ₁₂
  set fr : ℝ → cubicMassIndex d → ℝ := fun β n =>
    finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n.1 n.2 with hfr
  have hfr_nn : ∀ (β : ℝ), 0 < β → ∀ n : cubicMassIndex d, 0 ≤ fr β n := by
    intro β hβ n
    exact (finiteRegionPseudoMassDistFV_pos hα hJ hβ n.2).le
  have hfr_bdd : ∀ (β : ℝ), 0 < β → BddBelow (Set.range (fr β)) := by
    intro β hβ
    exact ⟨0, by rintro _ ⟨n, rfl⟩; exact hfr_nn β hβ n⟩
  have hrw : ∀ (β : ℝ), 0 < β →
      (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)) ^ (2 * α + 1)
        = sInf (Set.range (fun n : cubicMassIndex d => (fr β n) ^ (2 * α + 1))) := by
    intro β hβ
    rw [globalPseudoMassDist_eq_csInf_finiteRegionFV_cubic hα hd hJ hβ,
      ← sInf_range_pow_of_nonneg (hfr_nn β hβ) (hfr_bdd β hβ) (2 * α + 1)]
  rw [hrw β₂ hβ₂, hrw β₁ hβ₁]
  exact abs_csInf_range_sub_csInf_range_le
    ⟨0, by rintro _ ⟨n, rfl⟩; exact pow_nonneg (hfr_nn β₁ hβ₁ n) _⟩
    ⟨0, by rintro _ ⟨n, rfl⟩; exact pow_nonneg (hfr_nn β₂ hβ₂ n) _⟩
    hunif

/-- **GJ §17.5 Theorem 17.5.1 — system pseudo-mass power endpoint Lipschitz bound on the
high-temperature window** (pp.~311--312): for chosen endpoints `[β₁,β₂]` (`0<β₁≤β₂`, `β₂·J·2d<1/2`)
and `α≥d−1` (`d/2<α<d`), `∃ L>0, |globalPseudoMassDist(σ_{β₂})^{2α+1} −
globalPseudoMassDist(σ_{β₁})^{2α+1}| ≤ L·(β₂−β₁)` (the constant `L` may depend on the endpoints via
the witness mass).
This is the rigorous Lipschitz-envelope core of GJ Theorem 17.5.1: the σ/A-uniform finite-region
Lipschitz (PR-FV4c) passes through the `A↑ℤ^d` bridge (#4369) to the infinite-volume system mass
`m⁻(σ) = globalPseudoMassDist(σ)`.  Combined with Lemma 17.5.2 (the sandwich, #4278/#4297) this is
GJ's "from this the theorem follows by Lemma 17.5.2". -/
theorem globalPseudoMassDist_pow_succ_lipschitz_window {α d : ℕ} (hα : 1 ≤ α)
    (hd : 1 ≤ d) (hαd : d < 2 * α) (hαd2 : α < d) (hαd1 : d ≤ α + 1)
    {J β₁ β₂ : ℝ} (hJ : 0 < J) (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hβ₂_half : β₂ * J * (2 * d) < 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      |(globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β₂⟩ : IsingParams ℝ)) ^ (2 * α + 1)
          - (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β₁⟩ : IsingParams ℝ))
              ^ (2 * α + 1)|
        ≤ L * (β₂ - β₁) := by
  obtain ⟨L, hL, hunif⟩ := finiteRegionPseudoMassDistFV_pow_succ_lipschitz_uniform hα hd hαd hαd2
    hαd1 hJ hβ₁ hβ₁₂ hβ₂_half
  exact ⟨L, hL, globalPseudoMassDist_pow_succ_lipschitz_of_uniform_finiteRegionFV hα hd hJ hβ₁ hβ₁₂
    hunif⟩

end Ambient
end IsingModel
