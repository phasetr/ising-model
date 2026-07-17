import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d truncated2TwoPoint bounds + correlation/magnetizationInfinite monotonicity wrappers

Narrow child module for 23 ℤ^d wrappers covering:

- `truncated2TwoPoint_*` bounds: `le_one`, `neg_one_le`, `abs_le_one`,
  `sq_le_one`, `le_twoPointFunction`, `h_zero_eq`, `J_zero_of_ne_zero`;
- `spontaneousMagnetization_latticeGraph_indep_exhaustion`;
- `correlationInfinite_latticeGraph_*` trivial slices (`J_zero`,
  `beta_zero_vanish`, `zero_params_vanish`) and J / h / β monotone;
- `magnetizationInfinite_latticeGraph_*` bounds (`le_one`, `nonneg`)
  and J / h / β monotone;
- `correlationAlongExhaustion_latticeGraph_*` J / h / β monotone.

Theorem names are unchanged from the former `UniformMag`
declarations.
-/

namespace IsingModel
namespace Ambient


/-! ## Moved: truncated2TwoPoint bound wrappers

The seven wrappers `truncated2TwoPoint_le_one`,
`neg_one_le_truncated2TwoPoint`, `abs_truncated2TwoPoint_le_one`,
`truncated2TwoPoint_sq_le_one`,
`truncated2TwoPoint_le_twoPointFunction`,
`truncated2TwoPoint_h_zero_eq`, and
`truncated2TwoPoint_J_zero_of_ne_zero`
now live in `UniformMagBoundsTruncated2TwoPoint.lean`. -/

/-- **ℤ^d spontaneousMagnetization exhaustion-independence**:
any two exhaustions yield the same `spontaneousMagnetization`. -/
theorem spontaneousMagnetization_latticeGraph_indep_exhaustion
    (d : ℕ) (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i
      = spontaneousMagnetization (IsingModel.latticeGraph d) Λ' J β i :=
  spontaneousMagnetization_indep_exhaustion (IsingModel.latticeGraph d)
    Λ Λ' hJ hβ i

/-! ## Moved: correlationInfinite trivial-slice wrappers

The three wrappers
`correlationInfinite_latticeGraph_J_zero`,
`correlationInfinite_latticeGraph_beta_zero_vanish`,
`correlationInfinite_latticeGraph_zero_params_vanish` now live in
`UniformMagBoundsCorrInfTrivialSlices.lean`. -/


/-- **ℤ^d magnetizationInfinite ≤ 1** site-wise (any Exhaustion). -/
theorem magnetizationInfinite_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ p i ≤ 1 :=
  magnetizationInfinite_le_one (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d magnetizationInfinite ≥ 0** site-wise (any Exhaustion, ferromagnetic). -/
theorem magnetizationInfinite_latticeGraph_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    0 ≤ magnetizationInfinite (IsingModel.latticeGraph d) Λ p i :=
  magnetizationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf i

/-! ## Moved: magnetizationInfinite monotonicity wrappers

The three wrappers
`magnetizationInfinite_latticeGraph_monotone_{J,h,beta}` now live in
`UniformMagBoundsMagInfMonotone.lean`. -/


/-! ## Moved: correlationInfinite monotonicity wrappers

The three wrappers
`correlationInfinite_latticeGraph_monotone_{J,h,beta}` now live in
`UniformMagBoundsCorrInfMonotone.lean`. -/

/-! ## Moved: correlationAlongExhaustion monotonicity wrappers

The three wrappers
`correlationAlongExhaustion_latticeGraph_monotone_{J,h,beta}`
now live in `UniformMagBoundsCorrAlongExMonotone.lean`. -/


/-- **ℤ^d `|magnetizationInfinite| ≤ 1`** site-wise (any Exhaustion, ferromagnetic):
combines `magnetizationInfinite_latticeGraph_nonneg` (so `0 ≤ M`, hence
`-1 ≤ M`) with `magnetizationInfinite_latticeGraph_le_one`. -/
theorem abs_magnetizationInfinite_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    |magnetizationInfinite (IsingModel.latticeGraph d) Λ p i| ≤ 1 := by
  have hl := magnetizationInfinite_latticeGraph_nonneg d Λ p hf i
  have hu := magnetizationInfinite_latticeGraph_le_one d Λ p i
  exact abs_le.mpr ⟨by linarith, hu⟩

end Ambient

end IsingModel
