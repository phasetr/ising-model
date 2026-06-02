import IsingModel.Concrete.LatticeGraphCorrelation.Truncated2GeneralFieldDecay
import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1.HighTempMassGap

/-!
# General external-field cluster property of the connected 2-point function (GJ §18.7)

The Glimm--Jaffe §18.7 cluster property — the connected (truncated) two-point
function tends to `0` as the sites separate — extended to a general external
field `h ≥ 0` for the ferromagnetic Ising model on `ℤ^d` in the high-temperature
regime `β J · 2d < 1`.

The bound is obtained by lifting the existing `h = 0` exponential-decay witness
`hasExponentialDecay_latticeGraph_of_betaJ_two_d_lt_one` to general `h` through
GHS field-monotonicity (`truncated2Infinite_antitoneOn_h_of_ne`): for `h ≥ 0`
and distinct sites,
`0 ≤ truncated2Infinite ⟨J,h,β⟩ i j ≤ truncated2Infinite ⟨J,0,β⟩ i j`, so the
same `(C, rate)` witness controls the general-`h` connected correlation. Feeding
this `HasExponentialDecay` into `clusterProperty_latticeGraph_of_HasExponentialDecay`
yields the cluster property at general `h`.

Finite-volume → exhaustion lattice Ising (no continuum limit).
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-- **General-`h` exponential decay of the connected 2-point function from GHS
lift (GJ §18.7)**: for `0 < J`, `0 ≤ h`, `0 < β`, and `β J · 2d < 1` on `ℤ^d`,
`truncated2Infinite ⟨J,h,β⟩` has exponential decay with rate `−log(β J·2d) > 0`.

Same `(C, rate)` witness as the `h = 0` decay
`hasExponentialDecay_latticeGraph_of_betaJ_two_d_lt_one`, lifted via GHS
field-monotonicity `truncated2Infinite_antitoneOn_h_of_ne`
(`0 ≤ truncated2Infinite(h) ≤ truncated2Infinite(0)` for `h ≥ 0`, distinct sites).

References: GJ §18.7, pp. 319–322; §4.3 Cor. 4.3.4 (GHS). -/
theorem HasExponentialDecay_of_field_nonneg_high_temp
    (d : ℕ) (hd : 1 ≤ d) {J h β : ℝ}
    (hJ_pos : 0 < J) (hh : 0 ≤ h) (hβ_pos : 0 < β)
    (hht : β * J * (2 * d) < 1) :
    HasExponentialDecay d (cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ)
      (-Real.log (β * J * (2 * d))) := by
  obtain ⟨_, C, hC, hbound0⟩ :=
    hasExponentialDecay_latticeGraph_of_betaJ_two_d_lt_one d hd hJ_pos hβ_pos hht
  refine ⟨C, hC, fun i j hij => ?_⟩
  have hnonneg : 0 ≤ truncated2Infinite (latticeGraph d) (cubicExhaustion d)
      (⟨J, h, β⟩ : IsingParams ℝ) i j :=
    truncated2Infinite_nonneg_of_ne (latticeGraph d) (cubicExhaustion d)
      (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ_pos.le, hh, hβ_pos⟩ hij
  have hanti := truncated2Infinite_antitoneOn_h_of_ne (latticeGraph d)
    (cubicExhaustion d) J hJ_pos.le β hβ_pos hij
  have h_le : truncated2Infinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, h, β⟩ : IsingParams ℝ) i j
      ≤ truncated2Infinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) i j :=
    hanti Set.self_mem_Ici (Set.mem_Ici.mpr hh) hh
  rw [abs_of_nonneg hnonneg]
  exact h_le.trans ((le_abs_self _).trans (hbound0 i j hij))

/-- **General-`h` cluster property of the connected 2-point function (GJ §18.7)**:
for `0 < J`, `0 ≤ h`, `0 < β`, and `β J · 2d < 1` on `ℤ^d`, the connected
(truncated) two-point function `j ↦ truncated2Infinite ⟨J,h,β⟩ i j` tends to `0`
along the cofinite filter for every basepoint `i` (equivalently, as the lattice
distance `d_{ℤ^d}(i,j) → ∞`).

Combines `HasExponentialDecay_of_field_nonneg_high_temp` (GHS lift of the `h = 0`
decay) with `clusterProperty_latticeGraph_of_HasExponentialDecay`. Finite-volume
→ exhaustion lattice Ising (no continuum limit).

References: GJ §18.7, pp. 319–322; §4.3 Cor. 4.3.4 (GHS). -/
theorem clusterProperty_latticeGraph_of_field_nonneg_high_temp
    (d : ℕ) (hd : 1 ≤ d) {J h β : ℝ}
    (hJ_pos : 0 < J) (hh : 0 ≤ h) (hβ_pos : 0 < β)
    (hht : β * J * (2 * d) < 1) :
    clusterProperty (latticeGraph d) (cubicExhaustion d)
      (⟨J, h, β⟩ : IsingParams ℝ) := by
  have hB_pos : 0 < β * J * (2 * d) :=
    mul_pos (mul_pos hβ_pos hJ_pos) (by positivity)
  exact clusterProperty_latticeGraph_of_HasExponentialDecay d (cubicExhaustion d)
    (⟨J, h, β⟩ : IsingParams ℝ) (neg_pos.mpr (Real.log_neg hB_pos hht))
    (HasExponentialDecay_of_field_nonneg_high_temp d hd hJ_pos hh hβ_pos hht)

end Ambient

end IsingModel
