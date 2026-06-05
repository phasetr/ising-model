import IsingModel.Conditioning.CubicBoxMagnetizationDecay
import IsingModel.Conditioning.GeometricTail
import IsingModel.Concrete.LatticeGraphCorrelation.MagnetizationBetaMonotone
import IsingModel.Concrete.LatticeGraphCorrelation.SpontaneousMagnetization

/-!
# High-temperature vanishing of the spontaneous magnetization (FV §3.7.3)

The high-temperature half of the phase transition: the `+`-state spontaneous magnetization
vanishes, `m*(β) = 0`, for `4d²·tanh βJ < 1`. The infinite-volume limit of the box decay
bound (FV (3.49)): `⟨σ₀⟩⁺_{B(n)} ≤ (4d²·tanh βJ)^n/(1-4d²·tanh βJ) → 0`, combined with
`m* ≥ 0`. This completes the FV §3.7.3 high-temperature argument (Issue #3613).

* `plusStateSpontaneousMagnetization_eq_zero_of_high_temp` — `m*(β) = 0`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.3, eq. (3.49), p. 118.
-/

namespace IsingModel

open Finset Ambient Filter Topology

/-- **High-temperature vanishing of the spontaneous magnetization** (FV §3.7.3): for
`0 < d`, `0 < β`, `0 < J` and `4d²·tanh βJ < 1`, the `+`-state spontaneous magnetization is
zero, `m*(β) = 0`. The infinite-volume limit of the box decay bound (FV (3.49)),
`⟨σ₀⟩⁺_{B(n)} → 0`, together with `m* ≥ 0`. -/
theorem plusStateSpontaneousMagnetization_eq_zero_of_high_temp {d : ℕ} (hd : 0 < d)
    {J β : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    (htanh1 : 4 * (d : ℝ) ^ 2 * Real.tanh (β * J) < 1) :
    plusStateSpontaneousMagnetization d J β = 0 := by
  classical
  have htanh_pos : 0 < Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by positivity)) (Real.cosh_pos _)
  have hq0 : (0 : ℝ) ≤ 4 * (d : ℝ) ^ 2 * Real.tanh (β * J) := by positivity
  refine le_antisymm ?_ (plusStateSpontaneousMagnetization_nonneg hβ.le hJ.le)
  -- the screened box magnetizations converge to `m*`
  have hseq := tendsto_plusMagnetization (h := 0) hβ.le hJ.le (0 : Fin d → ℤ)
  -- the geometric bound vanishes
  have hgeom : Tendsto (fun k => (4 * (d : ℝ) ^ 2 * Real.tanh (β * J)) ^
        (latticeRadius (0 : Fin d → ℤ) + k) / (1 - 4 * (d : ℝ) ^ 2 * Real.tanh (β * J)))
      atTop (𝓝 0) := by
    have hcomp := (tendsto_geometric_tail hq0 htanh1).comp
      (tendsto_add_atTop_nat (latticeRadius (0 : Fin d → ℤ)))
    simp only [Function.comp_def, div_eq_mul_inv] at hcomp ⊢
    refine hcomp.congr (fun k => ?_)
    rw [Nat.add_comm]
  refine le_of_tendsto_of_tendsto' hseq hgeom (fun k => ?_)
  -- pointwise: `⟨σ₀⟩⁺ ≤ (4d²tanh)^n/(1-4d²tanh)` via the bridge and the box bound
  rw [plusBoxObsExpectation_singleSpin_eq (latticeRadius (0 : Fin d → ℤ) + k)
    (latticeRadius (0 : Fin d → ℤ) + k + 1) (0 : Fin d → ℤ)]
  refine gibbsExpectationBC_box_singleSpin_le hd J β rfl ?_ htanh_pos htanh1
  rw [mem_plusBoxInterior, mem_cubicBox]
  intro i
  simp only [Pi.zero_apply]
  omega

end IsingModel
