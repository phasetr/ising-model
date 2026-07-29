import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature
import IsingModel.Concrete.LatticeGraphCorrelation.InfiniteVolumeCorrelationInequalities
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationSymmetry
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationDecay
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.Inequalities.HighTemp
import IsingModel.LatticeExpSum
import IsingModel.PseudoMass
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferSummability
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferSummabilityCharacterization
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferExpDecay
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferBasic
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferExhaustion
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferReference
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferReferencePos
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferTanhPowDist

/-!
# Lattice-mass pseudo-mass transfer bridges at ℤ^d

This module contains the concrete §17.1 / §17.5 bridge layer split from the
original `Inequalities` module: Step 127 product summability bounds, critical
inverse temperature wrappers, high-temperature decay transfer to arbitrary
exhaustions, pseudo-mass comparison bridges, and below-critical cluster /
summability consequences.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient


/-! ## Moved: Step 127 summability + criticalInverseTemp foundations

The §17.5 Step 127 Lebowitz-exponential product summability bounds and
§17.1 / §17.5 criticalInverseTemp foundations now live in
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferSummability`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: HasExponentialDecay transfer + high-temp exhaustion

The 5 `HasExponentialDecay_*_transfer*` and
`latticeMass_*_high_temp_exhaustion` wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferExpDecay`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: pseudoMassFromParamsAtPair basic comparison wrappers

The 7 basic §17.5 pseudoMassFromParamsAtPair comparison +
latticeMass_ge / latticeMass_pos wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferBasic`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: pseudoMassFromParamsAtPair exhaustion variants

The 6 exhaustion-variant pseudoMassFromParamsAtPair wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferExhaustion`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: reference pseudoMassFromParamsAtPair variants

The 6 reference-variant pseudoMassFromParamsAtPair wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferReference`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: cubic_pseudoMassFromParamsAtPair variants

The 3 surviving cubic_pseudoMassFromParamsAtPair `_pseudoMassG_le_corr`
variant wrappers live in
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferCubicPseudoMassCorr`,
which this module does not import; import that child directly.

The `LatticeMassPseudoMassTransferReferencePos` import above carries no
declaration used here: it re-exports the transitive surface that the
former `LatticeMassPseudoMassTransferCubicPseudoMass` import provided to
downstream modules, so it must not be removed as unused.
-/



/-! ## Moved: tanh-power profile + twoPointFunction bridges

The 13 tanh-power profile + twoPointFunction bridge wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferTanhPowDist`.
The earlier import path is preserved by re-importing the new child.
-/

/-- **Cluster property holds below the critical inverse temperature** (GJ §17.1):
for `J ≥ 0`, `β ≥ 0`, and `ENNReal.ofReal β < criticalInverseTemp d J`, the
cluster property holds for any exhaustion `Λ`:
`clusterProperty (latticeGraph d) Λ ⟨J, 0, β⟩`.

**Physics**: the hypothesis `β < β_c` is the **high-temperature** regime
(equivalently, above the critical temperature `T_c = 1/β_c`). In this regime,
the connected 2-point function decays exponentially: for all `i, j`,
`|⟨σᵢ σⱼ⟩ - ⟨σᵢ⟩⟨σⱼ⟩|` decays to zero as `|i - j| → ∞`. This is the
GJ §17.1 high-temperature clustering consequence for the Ising model analog.

**Proof strategy**:
* `β = 0`: `clusterProperty_latticeGraph_beta_zero` (trivial slice).
* `β > 0`: use `latticeMass_pos_of_lt_criticalInverseTemp` to get `m > 0`,
  extract a positive rate `α` via `HasExponentialDecay_of_latticeMass_pos`,
  transfer the decay from `cubicExhaustion d` to `Λ` via
  `HasExponentialDecay_transfer_exhaustion` (uses `Ferromagnetic`), and
  conclude by `clusterProperty_latticeGraph_of_HasExponentialDecay`. -/
theorem clusterProperty_latticeGraph_of_lt_criticalInverseTemp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h : ENNReal.ofReal β < criticalInverseTemp d J) :
    clusterProperty (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) := by
  rcases eq_or_lt_of_le hβ with rfl | hβ_pos
  · exact clusterProperty_beta_zero (IsingModel.latticeGraph d) Λ J 0
  · have hm_pos : 0 < latticeMass d (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) :=
      latticeMass_pos_of_lt_criticalInverseTemp hβ_pos.le hJ h
    obtain ⟨α, hα_pos, hα_decay⟩ := HasExponentialDecay_of_latticeMass_pos hm_pos
    have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
      ⟨hJ, le_refl _, hβ_pos⟩
    have hα_decay' : HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) (α : ℝ) :=
      HasExponentialDecay_transfer_exhaustion (cubicExhaustion d) Λ hf hα_decay
    exact clusterProperty_latticeGraph_of_HasExponentialDecay d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) hα_pos hα_decay'

/-- **Summability of truncated 2-point below critical inverse temperature** (GJ §17.1/§17.5):
for `J ≥ 0`, `β ≥ 0`, and `ENNReal.ofReal β < criticalInverseTemp d J`, the truncated
2-point function is summable:
`Summable (fun j => truncated2Infinite (latticeGraph d) Λ ⟨J, 0, β⟩ i j)`.

This extends `truncated2Infinite_summable_of_high_temp` (βJD < 1 case, PR #903) to the
full below-β_c regime, giving a per-site finite-susceptibility result for all high-temperature
couplings (not just the Simon-Lieb high-temperature range).

**Proof**: β = 0 gives `U_2 = 0` (summable trivially). For β > 0: `latticeMass > 0`
(via `latticeMass_pos_of_lt_criticalInverseTemp`) → extract `α > 0` and
`HasExponentialDecay` (via `HasExponentialDecay_of_latticeMass_pos`) → transfer to `Λ`
(via `HasExponentialDecay_transfer_exhaustion`) → `|U_2(i,j)| ≤ C·exp(-α·d(i,j))` for
`i ≠ j` and `U_2(i,i) = 0` (Z₂ symmetry) → `summable_exp_neg_dist` + nonneg bound
→ `Summable.of_nonneg_of_le`. -/
theorem truncated2Infinite_summable_of_lt_criticalInverseTemp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h : ENNReal.ofReal β < criticalInverseTemp d J)
    (i : Fin d → ℤ) :
    Summable (fun j : Fin d → ℤ =>
      truncated2Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) i j) := by
  rcases eq_or_lt_of_le hβ with rfl | hβ_pos
  · simp only [truncated2Infinite_beta_zero (IsingModel.latticeGraph d) Λ J 0]
    exact summable_zero
  · have hm_pos : 0 < latticeMass d (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) :=
      latticeMass_pos_of_lt_criticalInverseTemp hβ_pos.le hJ h
    obtain ⟨α, hα_pos, hα_decay⟩ := HasExponentialDecay_of_latticeMass_pos hm_pos
    have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl _, hβ_pos⟩
    obtain ⟨C, hC, hbound⟩ :=
      HasExponentialDecay_transfer_exhaustion (cubicExhaustion d) Λ hf hα_decay
    apply Summable.of_nonneg_of_le
        (fun j => truncated2Infinite_nonneg (IsingModel.latticeGraph d) Λ _ hf i j)
        (fun j => ?_)
        ((summable_exp_neg_dist hα_pos d i).mul_left C)
    by_cases hij : i = j
    · subst hij
      rw [truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β i i]
      simp only [Finset.pair_eq_singleton]
      rw [Ambient.correlationInfinite_h_zero (IsingModel.latticeGraph d) Λ J β {i} (by simp)]
      exact mul_nonneg hC (Real.exp_nonneg _)
    · exact le_trans (le_abs_self _) (hbound i j hij)

end Ambient
end IsingModel
