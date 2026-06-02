import IsingModel.Concrete.LatticeGraphCorrelation.SimonLiebDistanceDecay
import IsingModel.AmbientLattice.TruncatedFunctions.Cluster

/-!
# General external-field exponential decay of the connected 2-point function (GJ §18.7)

The Glimm--Jaffe §18.7 decay of correlations, extended to a general external
field `h ≥ 0` for the ferromagnetic Ising model on `ℤ^d`. The full two-point
function does not decay at `h ≠ 0` (it tends to `⟨σ_i⟩⟨σ_j⟩ ≠ 0`), but the
**connected (truncated) two-point function** `⟨σ_i; σ_j⟩ = truncated2Infinite`
does. The bound is obtained by combining

1. the GHS field-monotonicity `truncated2Infinite_antitoneOn_h_of_ne`
   (`⟨σ_i;σ_j⟩` antitone in `h` on `[0,∞)`), giving
   `truncated2Infinite ⟨J,h,β⟩ ≤ truncated2Infinite ⟨J,0,β⟩` for `h ≥ 0`;
2. the `h = 0` collapse `truncated2Infinite_h_zero`
   (`truncated2Infinite ⟨J,0,β⟩ = correlationInfinite ⟨J,0,β⟩ {i,j}`, since
   `⟨σ_i⟩ = 0` by `Z₂` symmetry at `h = 0`);
3. the existing `h = 0` Simon--Lieb exponential decay of the full two-point
   function.

This is a finite-volume → exhaustion lattice Ising result (no continuum limit).
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-- **General-`h` Simon--Lieb power decay of the connected 2-point function
(GJ §18.7)**: for a ferromagnetic field `⟨J, h, β⟩` with `h ≥ 0`, distinct sites
`i ≠ j` on `ℤ^d`, and `n + 1 ≤ d_{ℤ^d}(i,j)`,
`⟨σ_i; σ_j⟩_{⟨J,h,β⟩} ≤ (β J · 2d)^n`.

`h ≥ 0` field-monotonicity (GHS, `truncated2Infinite_antitoneOn_h_of_ne`) +
`h = 0` collapse (`truncated2Infinite_h_zero`) + `h = 0` Simon--Lieb power decay.

References: GJ §18.7, pp. 319–322; §4.3 Cor. 4.3.4 (GHS). -/
theorem truncated2Infinite_latticeGraph_le_betaJ_two_d_pow_of_ferromagnetic_field_nonneg
    {d : ℕ} {β J h : ℝ}
    (hf : Ferromagnetic (⟨J, h, β⟩ : IsingParams ℝ))
    (n : ℕ) {i j : Fin d → ℤ} (hij : i ≠ j)
    (hdist : n + 1 ≤ latticeDistance d i j) :
    truncated2Infinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, h, β⟩ : IsingParams ℝ) i j
      ≤ (β * J * (2 * d)) ^ n := by
  have hf0 : Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ) :=
    ⟨hf.hJ, le_refl 0, hf.hβ⟩
  have hanti := truncated2Infinite_antitoneOn_h_of_ne (latticeGraph d)
    (cubicExhaustion d) J hf.hJ β hf.hβ hij
  have h_le : truncated2Infinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, h, β⟩ : IsingParams ℝ) i j
      ≤ truncated2Infinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) i j :=
    hanti (Set.self_mem_Ici) (Set.mem_Ici.mpr hf.hh) hf.hh
  rw [truncated2Infinite_h_zero] at h_le
  exact h_le.trans
    (correlationInfinite_latticeGraph_le_betaJ_two_d_pow_of_ferromagnetic_dist_gt
      hf0 n i j hdist)

/-- **General-`h` Simon--Lieb exponential decay of the connected 2-point
function (GJ §18.7)**: for a ferromagnetic field `⟨J, h, β⟩` with `h ≥ 0`,
distinct sites `i ≠ j`, high temperature `0 < β J · 2d`, and
`n + 1 ≤ d_{ℤ^d}(i,j)`,
`⟨σ_i; σ_j⟩_{⟨J,h,β⟩} ≤ exp(-(−log(β J·2d)) · n)`.

References: GJ §18.7, pp. 319–322; §4.3 Cor. 4.3.4 (GHS). -/
theorem truncated2Infinite_latticeGraph_le_exp_neg_simonLiebRate_pow_of_ferromagnetic_field_nonneg
    {d : ℕ} {β J h : ℝ}
    (hf : Ferromagnetic (⟨J, h, β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d))
    (n : ℕ) {i j : Fin d → ℤ} (hij : i ≠ j)
    (hdist : n + 1 ≤ latticeDistance d i j) :
    truncated2Infinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, h, β⟩ : IsingParams ℝ) i j
      ≤ Real.exp (-(simonLiebRate β J d) * (n : ℝ)) := by
  have hf0 : Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ) :=
    ⟨hf.hJ, le_refl 0, hf.hβ⟩
  have hanti := truncated2Infinite_antitoneOn_h_of_ne (latticeGraph d)
    (cubicExhaustion d) J hf.hJ β hf.hβ hij
  have h_le : truncated2Infinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, h, β⟩ : IsingParams ℝ) i j
      ≤ truncated2Infinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) i j :=
    hanti (Set.self_mem_Ici) (Set.mem_Ici.mpr hf.hh) hf.hh
  rw [truncated2Infinite_h_zero] at h_le
  exact h_le.trans
    (correlationInfinite_latticeGraph_le_exp_neg_simonLiebRate_pow_of_ferromagnetic_dist_gt
      hf0 hβJd_pos n i j hdist)

/-- **General-`h` Simon--Lieb half-rate decay of the connected 2-point function
(GJ §18.7)**: for a ferromagnetic field `⟨J, h, β⟩` with `h ≥ 0`, distinct sites,
`0 < β J·2d ≤ 1`, and `d_{ℤ^d}(i,j) ≥ 2`,
`⟨σ_i; σ_j⟩_{⟨J,h,β⟩} ≤ exp(-(−log(β J·2d)/2) · d_{ℤ^d}(i,j))`.

The off-by-one-free form: the rate is halved but the exponent carries the full
lattice distance.

References: GJ §18.7, pp. 319–322; §4.3 Cor. 4.3.4 (GHS). -/
theorem truncated2Infinite_latticeGraph_le_exp_neg_half_simonLiebRate_of_ferromagnetic_field_nonneg
    {d : ℕ} {β J h : ℝ}
    (hf : Ferromagnetic (⟨J, h, β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {i j : Fin d → ℤ} (hij : i ≠ j)
    (hdist : 2 ≤ latticeDistance d i j) :
    truncated2Infinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, h, β⟩ : IsingParams ℝ) i j
      ≤ Real.exp (-(simonLiebRate β J d / 2) * (latticeDistance d i j : ℝ)) := by
  have hf0 : Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ) :=
    ⟨hf.hJ, le_refl 0, hf.hβ⟩
  have hanti := truncated2Infinite_antitoneOn_h_of_ne (latticeGraph d)
    (cubicExhaustion d) J hf.hJ β hf.hβ hij
  have h_le : truncated2Infinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, h, β⟩ : IsingParams ℝ) i j
      ≤ truncated2Infinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) i j :=
    hanti (Set.self_mem_Ici) (Set.mem_Ici.mpr hf.hh) hf.hh
  rw [truncated2Infinite_h_zero] at h_le
  apply h_le.trans
  exact
   correlationInfinite_latticeGraph_le_exp_neg_half_simonLiebRate_dist_of_ferromagnetic_dist_ge_two
    hf0 hβJd_pos hβJd_le hdist

end Ambient

end IsingModel
