import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundation
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundationTrivialSliceAndIndep
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferSummabilityCharacterization
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
import IsingModel.BetaDerivative
import IsingModel.PseudoMass

/-!
# Inequalities and §17 lattice mass at ℤ^d

ℤ^d wrappers for:
1. GHS inequality (truncated3 ≤ 0) and Lebowitz inequality (truncated4 ≤ 0)
2. §17.1/§17.5 lattice mass / correlation length

This module also imports
`IsingModel.Concrete.LatticeGraphCorrelation.CorrelationDecay` to preserve the
original `Inequalities` import path for §5.1 conditional and distance-based
cluster-decay wrappers, and
`IsingModel.Concrete.LatticeGraphCorrelation.PointwiseRegularity` /
`IsingModel.Concrete.LatticeGraphCorrelation.SusceptibilityPointwiseRegularity`
to preserve the import path for finite-stage correlation and susceptibility
regularity compatibility names. New code should import the narrower child
modules directly for those declarations.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ## §17.1 / §17.5 lattice mass / correlation length foundation

The foundational `HasExponentialDecay` and `latticeMass` API now lives in
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundation`. This
module imports it to preserve the original `Inequalities` import path.
-/

/-! ## §5.1 / §17.5 high-temperature lattice-mass bounds

The concrete high-temperature `HasExponentialDecay`, lattice-mass bounds,
antitonicity, and tanh lower-bound API now lives in
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature`. This
module imports it to preserve the original `Inequalities` import path.
-/

/-! ## §17.1 / §17.5 pseudo-mass transfer and critical-temperature bridges

The concrete product-summability, critical inverse temperature, pseudo-mass
transfer, and below-critical cluster / summability bridge API now lives in
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransfer`.
This module imports it to preserve the original `Inequalities` import path.
-/

/-! ## §17.1 d = 0 special case -/

/-- **Vacuous HasExponentialDecay in dimension zero**: for `d = 0`, the lattice
`Fin 0 → ℤ` is a singleton, so there are no distinct pairs `(i, j)`, and
`HasExponentialDecay 0 Λ p α` holds for every `Λ`, `p`, and `α`. -/
private lemma HasExponentialDecay_dim_zero
    (Λ : Ambient.Exhaustion (Fin 0 → ℤ)) (p : IsingParams ℝ) (α : ℝ) :
    HasExponentialDecay 0 Λ p α :=
  ⟨0, le_refl _, fun _i _j hij =>
    absurd (funext (fun x => Fin.elim0 x)) hij⟩

/-- **Lattice mass is `⊤` in dimension zero**: the set of valid decay rates is all of
`NNReal` (vacuous condition), so `latticeMass = sSup (NNReal → ENNReal) = ⊤`. -/
private lemma latticeMass_eq_top_of_dim_zero
    (Λ : Ambient.Exhaustion (Fin 0 → ℤ)) (p : IsingParams ℝ) :
    latticeMass 0 Λ p = ⊤ := by
  refine eq_top_iff.mpr ?_
  refine le_sSup_iff.mpr ?_
  intro b hb
  by_contra hb_ne
  rw [not_le] at hb_ne
  set α : NNReal := b.toNNReal + 1
  have hαmem : (α : ENNReal) ∈ (fun α : NNReal => (α : ENNReal)) ''
      {α : NNReal | HasExponentialDecay 0 Λ p (α : ℝ)} :=
    ⟨α, HasExponentialDecay_dim_zero Λ p (α : ℝ), rfl⟩
  have hα_le_b : (α : ENNReal) ≤ b := hb hαmem
  have hb_ne_top : b ≠ ⊤ := ne_of_lt hb_ne
  have hb_toNN : ((b.toNNReal : ENNReal) : ENNReal) = b := ENNReal.coe_toNNReal hb_ne_top
  have hα_eq : (α : ENNReal) = b + 1 := by
    simp only [α, ENNReal.coe_add, ENNReal.coe_one, hb_toNN]
  rw [hα_eq] at hα_le_b
  exact absurd hα_le_b (not_le.mpr (ENNReal.lt_add_right hb_ne_top one_ne_zero))

/-- **Critical inverse temperature is `⊤` in dimension zero** (GJ §17.1):
for `d = 0` (single-site model, no neighbors), the lattice mass is always `⊤ > 0`,
so all `β ≥ 0` are in the high-temperature set and `criticalInverseTemp 0 J = ⊤`.

Physics: a zero-dimensional Ising model has no ferromagnetic interactions and no
phase transition at any temperature; the "critical temperature" is infinite (β_c = ⊤). -/
theorem criticalInverseTemp_eq_top_of_dim_zero (J : ℝ) :
    criticalInverseTemp 0 J = ⊤ := by
  unfold criticalInverseTemp
  refine eq_top_iff.mpr ?_
  refine le_sSup_iff.mpr ?_
  intro b hb
  by_contra hb_ne
  rw [not_le] at hb_ne
  have hb_ne_top : b ≠ ⊤ := ne_of_lt hb_ne
  set β₀ : NNReal := b.toNNReal + 1
  have hmass_pos : 0 < latticeMass 0 (cubicExhaustion 0)
      (⟨J, 0, (β₀ : ℝ)⟩ : IsingParams ℝ) := by
    rw [latticeMass_eq_top_of_dim_zero]
    simp
  have hmem : ENNReal.ofReal (β₀ : ℝ) ∈ ENNReal.ofReal ''
      { β : ℝ | 0 ≤ β ∧ 0 < latticeMass 0 (cubicExhaustion 0)
          (⟨J, 0, β⟩ : IsingParams ℝ) } :=
    ⟨(β₀ : ℝ), ⟨NNReal.coe_nonneg _, hmass_pos⟩, rfl⟩
  have hle : ENNReal.ofReal (β₀ : ℝ) ≤ b := hb hmem
  have hb_toNN : ((b.toNNReal : ENNReal) : ENNReal) = b := ENNReal.coe_toNNReal hb_ne_top
  have hβ₀_eq : ENNReal.ofReal (β₀ : ℝ) = b + 1 := by
    simp only [β₀, ENNReal.ofReal_coe_nnreal, ENNReal.coe_add, ENNReal.coe_one, hb_toNN]
  rw [hβ₀_eq] at hle
  exact absurd hle (not_le.mpr (ENNReal.lt_add_right hb_ne_top one_ne_zero))

/-! ## §17.1 J = 0 special case -/

/-- **Critical inverse temperature is `⊤` when `J = 0`** (GJ §17.1):
for zero coupling constant, `latticeMass = ⊤` for every `β ≥ 0` (either from
`latticeMass_top_of_beta_zero` at `β = 0`, or from `latticeMass_top_of_J_zero` at `β > 0`),
so the defining set is all of `[0,∞)` and `criticalInverseTemp d 0 = ⊤`.

Physics: with no coupling between sites, no phase transition occurs at any finite inverse
temperature (β_c = ⊤ means T_c = 0). This is the J = 0 companion of
`criticalInverseTemp_eq_top_of_dim_zero`. -/
theorem criticalInverseTemp_eq_top_of_J_zero (d : ℕ) :
    criticalInverseTemp d 0 = ⊤ := by
  apply le_antisymm le_top
  rw [← ENNReal.iSup_natCast]
  apply iSup_le
  intro n
  rw [← ENNReal.ofReal_natCast n]
  apply criticalInverseTemp_ge_ofReal_of_latticeMass_pos (Nat.cast_nonneg n)
  rcases n with _ | n
  · rw [Nat.cast_zero, latticeMass_top_of_beta_zero]; exact ENNReal.zero_lt_top
  · have hf : Ferromagnetic (⟨(0 : ℝ), (0 : ℝ), (↑(n + 1) : ℝ)⟩ : IsingParams ℝ) :=
      ⟨le_refl _, le_refl _, by positivity⟩
    rw [latticeMass_top_of_J_zero d (cubicExhaustion d) 0 _ hf]
    exact ENNReal.zero_lt_top

/-! ## §17.1 / §17.5 finite susceptibility and Lebowitz derivative bounds

The concrete finite-susceptibility wrapper and Lebowitz derivative bound API
now lives in
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassLebowitzDerivative`.
This module imports it to preserve the original `Inequalities` import path.
-/

/-! ## §17.5 high-temperature Lipschitz and uniform convergence wrappers

The concrete high-temperature Lipschitz, continuity, uniform convergence,
a.e. differentiability, locally bounded variation, locally uniform convergence,
and interior-continuity API now lives in
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempLipschitz`.
This module imports it to preserve the original `Inequalities` import path.
-/

/-! ## §17.5 high-temperature zero-boundary and half-open wrappers

The concrete high-temperature zero-boundary linear bounds, closed-interval
continuity and uniform convergence wrappers, zero-included Lipschitz bounds,
half-line a.e. differentiability wrappers, and half-open locally uniform
convergence API now lives in
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempZeroBoundary`.
This module imports it to preserve the original `Inequalities` import path.
-/

/-! ## §17.5 truncated2Infinite high-temperature wrappers

The concrete high-temperature regularity wrappers for the infinite-volume
Ursell two-point function `truncated2Infinite` at `h = 0` (Step 185--187 in
the β-direction, Step 239--240 in the J-direction, and Step 241 interior
`ContinuousAt` wrappers) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassTruncated2HighTemp`.
This module imports it to preserve the original `Inequalities` import path.
-/

end Ambient

end IsingModel
