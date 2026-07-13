import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMagTwoPointNonnegAndGe
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPointZeroCollapse
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPointTruncated2EqSubMagSq
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG

/-!
# ℤ^d uniformMagnetization recasts + truncated zero_params + magnetization basic wrappers

Narrow parent module covering the residual ℤ^d wrappers:

- `uniformMagnetization` recasts: `twoPointFunction_zero_eq_*`,
  `truncated2TwoPoint_eq_twoPointFunction_sub_*_sq`,
  `twoPointFunction_ge_*_sq`.
- truncated zero_params: `truncated2/3/4TwoPoint_zero_params`,
  `truncated2TwoPoint_beta_zero`.

The `magnetizationΛ_/AlongExhaustion_/Infinite_latticeGraph_*` and
`freeEnergyInfinite_latticeGraph_apply` apply/bound/unfolding wrappers
were further carved out into `UniformMagRecastsMagnetization.lean` in
PR #2142. Theorem names are unchanged from the former `UniformMag`
declarations.
-/

namespace IsingModel
namespace Ambient

/-! ## `uniformMagnetization` recasts -/

/-- **`twoPointFunction` at `r = 0` equals `uniformMagnetization`**
(convenience recast). Combines `twoPointFunction_zero` with the
definition of `uniformMagnetization`. -/
theorem twoPointFunction_zero_eq_uniformMagnetization
    (d : ℕ) (p : IsingParams ℝ) :
    twoPointFunction d p 0 = uniformMagnetization d p :=
  twoPointFunction_zero d p

/-- **`truncated2TwoPoint = twoPointFunction − (uniformMagnetization)²`**
(convenience recast). -/
theorem truncated2TwoPoint_eq_twoPointFunction_sub_uniformMagnetization_sq
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    truncated2TwoPoint d p r
      = twoPointFunction d p r - (uniformMagnetization d p)^2 :=
  truncated2TwoPoint_eq_twoPointFunction_sub_magnetization_sq d p hf r

/-- **`twoPointFunction ≥ (uniformMagnetization)²`** (convenience recast). -/
theorem twoPointFunction_ge_uniformMagnetization_sq
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    (uniformMagnetization d p)^2 ≤ twoPointFunction d p r :=
  twoPointFunction_ge_magnetization_sq d p hf r

/-! ## Moved: truncatedN_zero_params wrappers

The three wrappers
`truncated2TwoPoint_zero_params`,
`truncated3TwoPoint_zero_params`,
`truncated4TwoPoint_zero_params` now live in
`UniformMagRecastsTruncatedZeroParams.lean`. -/


/-- **`truncated2TwoPoint` at `β = 0` vanishes**:
`truncated2TwoPoint d ⟨J, h, 0⟩ r = 0`.

At infinite temperature `β = 0` all correlations vanish:
`correlationInfinite ... {0, r} = 0` (PR #278) and the magnetization
term is `0 · 0 = 0` (PR #276). Direct computation. -/
theorem truncated2TwoPoint_beta_zero
    (d : ℕ) (J h : ℝ) (r : Fin d → ℤ) :
    truncated2TwoPoint d (⟨J, h, 0⟩ : IsingParams ℝ) r = 0 := by
  unfold truncated2TwoPoint truncated2Infinite
  -- `correlationInfinite ... {0, r} = 0`, `correlationInfinite ... {0} = 0`,
  -- `correlationInfinite ... {r} = 0`.
  rw [show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), r} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ)} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {r} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp)]
  ring
/-! ## Moved: truncated2TwoPoint bounds + correlation/magnetizationInfinite monotonicity

The 23 ℤ^d `truncated2TwoPoint_*` bounds + trivial slices,
`spontaneousMagnetization_latticeGraph_indep_exhaustion`,
`correlationInfinite_latticeGraph_*` trivial-slice + J/h/β monotone,
`magnetizationInfinite_latticeGraph_*` bound + J/h/β monotone,
and `correlationAlongExhaustion_latticeGraph_*` J/h/β monotone
wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.UniformMagBoundsMonotonicity`.
The earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: magnetization apply / bound wrappers

The nine `magnetizationΛ_latticeGraph_{apply,le_one,abs_le_one,nonneg}`,
`magnetizationAlongExhaustion_latticeGraph_{apply,of_mem,of_not_mem}`,
`magnetizationInfinite_latticeGraph_apply`, and
`freeEnergyInfinite_latticeGraph_apply` wrappers now live in
`UniformMagRecastsMagnetization.lean`. -/

end Ambient

end IsingModel
