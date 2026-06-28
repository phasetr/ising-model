import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempContinuousAt
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeFromSimonLieb
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundation
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# GJ §17.5/§18 Theorem 17.5.1 — per-pair exponential-rate continuity (true-mass route foundation)

Toward the **true-mass `latticeMass` continuity** (issue #4386, route 2): the foundational brick
that the per-pair exponential decay **rate** `β ↦ −log⟨φ_i φ_j⟩_∞ / d(i,j)` is continuous on the
high-temperature window.  This is the base of the abscissa / semicontinuity analysis of the true
mass `latticeMass = sSup {α : ∀ pairs |trunc| ≤ C e^{−α·dist}}`: each pair contributes a continuous
rate,
and the true mass is a `liminf`/`inf`-type envelope of these.

The infinite-volume two-point correlation is continuous in `β` on the window and strictly positive,
so `−log` of it is continuous; dividing by the fixed
positive distance keeps continuity.  At `h = 0` the truncated 2-point function equals the bare
correlation (`truncated2Infinite_h_zero`), so the same rate continuity holds for the object
`latticeMass` is actually built from.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5 Theorem 17.5.1 / Lemma 17.5.2, §18, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

open Set

/-- **Per-pair exponential-rate continuity** (true-mass route foundation): for a distinct pair
`i ≠ j` and `0 < J`, the rate `β ↦ −log⟨φ_i φ_j⟩_∞ / d(i,j)` is continuous at every high-temperature
`β₀ ∈ Ioo 0 (1/(J·2d))`.  Continuity of the correlation (`…_continuousAt_beta_of_high_temp`) +
strict positivity (`correlationInfinite_pos_of_betaJ_pos_pair`) make `−log` continuous; `÷ d(i,j)`
preserves it. -/
theorem perPairRate_continuousAt_high_temp {d : ℕ} (hd : 1 ≤ d) {J : ℝ} (hJ : 0 < J)
    {i j : Fin d → ℤ} (hij : i ≠ j) {β₀ : ℝ}
    (hβ₀ : β₀ ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) :
    ContinuousAt (fun β => (-Real.log (Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}))
      / (IsingModel.latticeDistance d i j : ℝ)) β₀ := by
  have hβ₀pos : 0 < β₀ := hβ₀.1
  have hcorr_cont : ContinuousAt (fun β => Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}) β₀ :=
    correlationInfinite_continuousAt_beta_of_high_temp hd (cubicExhaustion d) i j hij J hJ β₀ hβ₀
  have hcorr_pos : 0 < Ambient.correlationInfinite (IsingModel.latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β₀⟩ : IsingParams ℝ) {i, j} :=
    correlationInfinite_pos_of_betaJ_pos_pair hβ₀pos (mul_pos hβ₀pos hJ) hij
  exact ((hcorr_cont.log (ne_of_gt hcorr_pos)).neg).div_const _

/-- **Per-pair exponential-rate continuity (truncated form)** (true-mass route foundation): at `h=0`
the truncated 2-point function equals the bare correlation, so the rate
`β ↦ −log|trunc₂(i,j)| / d(i,j)` (the object `latticeMass` is built from) is continuous at every
high-temperature `β₀`.  Since the correlation is positive, `|trunc₂| = trunc₂ = ⟨φ_iφ_j⟩`, reducing
to `perPairRate_continuousAt_high_temp`. -/
theorem perPairTruncRate_continuousAt_high_temp {d : ℕ} (hd : 1 ≤ d) {J : ℝ} (hJ : 0 < J)
    {i j : Fin d → ℤ} (hij : i ≠ j) {β₀ : ℝ}
    (hβ₀ : β₀ ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) :
    ContinuousAt (fun β => (-Real.log |truncated2Infinite (IsingModel.latticeGraph d)
        (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) i j|)
      / (IsingModel.latticeDistance d i j : ℝ)) β₀ := by
  have hcorr_cont : ContinuousAt (fun β => Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}) β₀ :=
    correlationInfinite_continuousAt_beta_of_high_temp hd (cubicExhaustion d) i j hij J hJ β₀ hβ₀
  have hcorr_pos : 0 < Ambient.correlationInfinite (IsingModel.latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β₀⟩ : IsingParams ℝ) {i, j} :=
    correlationInfinite_pos_of_betaJ_pos_pair hβ₀.1 (mul_pos hβ₀.1 hJ) hij
  have hev : ∀ᶠ β in nhds β₀, 0 < Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} :=
    hcorr_cont.eventually_mem (Ioi_mem_nhds hcorr_pos)
  refine (perPairRate_continuousAt_high_temp hd hJ hij hβ₀).congr ?_
  filter_upwards [hev] with β hβpos
  rw [truncated2Infinite_h_zero (IsingModel.latticeGraph d) (cubicExhaustion d) J β i j,
    abs_of_pos hβpos]

/-- **Per-pair exponential-rate continuity on the window** (`ContinuousOn` form): the per-pair rate
`β ↦ −log⟨φ_i φ_j⟩_∞ / d(i,j)` is `ContinuousOn` the open high-temperature window
`Ioo 0 (1/(J·2d))`.  Pointwise `ContinuousAt` (`perPairRate_continuousAt_high_temp`) at each
interior point (the window is open, so it is a neighbourhood). -/
theorem perPairRate_continuousOn_window {d : ℕ} (hd : 1 ≤ d) {J : ℝ} (hJ : 0 < J)
    {i j : Fin d → ℤ} (hij : i ≠ j) :
    ContinuousOn (fun β => (-Real.log (Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}))
      / (IsingModel.latticeDistance d i j : ℝ)) (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) :=
  fun _ hβ => (perPairRate_continuousAt_high_temp hd hJ hij hβ).continuousWithinAt

/-- **Per-pair exponential-rate continuity on the window (truncated form)** (`ContinuousOn`): the
rate `β ↦ −log|trunc₂(i,j)| / d(i,j)` (the object `latticeMass` is built from) is `ContinuousOn` the
open high-temperature window. -/
theorem perPairTruncRate_continuousOn_window {d : ℕ} (hd : 1 ≤ d) {J : ℝ} (hJ : 0 < J)
    {i j : Fin d → ℤ} (hij : i ≠ j) :
    ContinuousOn (fun β => (-Real.log |truncated2Infinite (IsingModel.latticeGraph d)
        (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) i j|)
      / (IsingModel.latticeDistance d i j : ℝ)) (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) :=
  fun _ hβ => (perPairTruncRate_continuousAt_high_temp hd hJ hij hβ).continuousWithinAt

end Ambient
end IsingModel
