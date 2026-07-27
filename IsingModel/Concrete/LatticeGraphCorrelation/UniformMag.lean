import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# `uniformMagnetization` recasts at ℤ^d
Thin wrappers that express ∞-vol observables (magnetizationInfinite,
truncated2Infinite, susceptibilityInfinite, correlationInfinite, etc.)
in terms of `uniformMagnetization` using translation invariance.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ## Moved: uniformMagnetization recasts + truncated zero_params + magnetization basic wrappers

The 16 ℤ^d wrappers covering `uniformMagnetization` recasts,
`truncated{2,3,4}TwoPoint_zero_params` + `truncated2TwoPoint_beta_zero`,
`magnetizationΛ_latticeGraph_{apply, le_one, abs_le_one, nonneg}`,
`magnetizationAlongExhaustion_latticeGraph_{apply, of_mem,
of_not_mem}`, `magnetizationInfinite_latticeGraph_apply`, and
`freeEnergyInfinite_latticeGraph_apply` now live in
`IsingModel.Concrete.LatticeGraphCorrelation.UniformMagRecasts`.
The earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: magnetizationAlongExhaustion / correlationAlongExhaustion
bounds + convergence wrappers

The 14 remaining ℤ^d `magnetizationAlongExhaustion_latticeGraph_*`,
`correlationAlongExhaustion_latticeGraph_*` and `*_eq_ciSup` bound /
monotone / convergent / bddAbove / bddBelow / `_le_*Infinite` wrappers
live in four child modules:

* `UniformMagAlongExConvergenceBasicBounds` (3 wrappers),
* `UniformMagAlongExConvergenceCiSup` (4 wrappers),
* `UniformMagAlongExConvergenceMain` (3 wrappers),
* `UniformMagAlongExConvergenceCorrAlongEx` (4 wrappers).

The `magnetizationAlongExhaustion_latticeGraph_{bddAbove, bddBelow,
tendsto_ciSup}` wrappers were deleted; no consumer of them was found in
this repository.
-/


/-! ## Moved: magnetizationΛ + AlongExhaustion monotone + trivial-slice wrappers

The 15 ℤ^d `magnetizationΛ_latticeGraph_*` and
`magnetizationAlongExhaustion_latticeGraph_*` J/h/β monotonicity +
trivial-slice (h_zero, beta_zero, zero_params, J_zero variants)
wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.UniformMagMagnetizationTrivial`.
The earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: abs / neg bounds wrappers

The 10 ℤ^d `abs_*_latticeGraph_le_one` /
`neg_one_le_*_latticeGraph` wrappers
(for `correlationΛ`, `correlationAlongExhaustion`,
`correlationInfinite`, `magnetizationΛ`,
`magnetizationAlongExhaustion`, `magnetizationInfinite`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.UniformMagAbsBounds`.
The three `correlation*_latticeGraph_sq_le_one` wrappers of the same
family were deleted; no consumer of them was found in this repository.
The earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: correlation trivial / GKS-II / FKG / h_zero / cor 4.3.5 wrappers

The 15 ℤ^d wrappers covering `magnetizationInfinite_latticeGraph_*`
trivial slices, `correlationInfinite_latticeGraph_*` empty / GKS-II
/ FKG / h_zero / cor_4_3_5_h0, and
`correlationΛ_latticeGraph_odd_vanish_h_zero` /
`correlationAlongExhaustion_latticeGraph_*_h_zero` wrappers now live
in
`IsingModel.Concrete.LatticeGraphCorrelation.UniformMagCorrelationTrivial`.
The earlier import path is preserved by re-importing the new child.
-/


/-- **ℤ^d spontaneousMagnetization at J = 0 vanishes** (Step 269). -/
theorem spontaneousMagnetization_latticeGraph_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) {β : ℝ} (hβ : 0 < β)
    (i : Fin d → ℤ) :
    spontaneousMagnetization (IsingModel.latticeGraph d) Λ 0 β i = 0 :=
  spontaneousMagnetization_J_zero (IsingModel.latticeGraph d) Λ hβ i

/-- **ℤ^d spontaneousMagnetization at β = 0 vanishes** (Step 269). -/
theorem spontaneousMagnetization_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J : ℝ) (i : Fin d → ℤ) :
    spontaneousMagnetization (IsingModel.latticeGraph d) Λ J 0 i = 0 :=
  spontaneousMagnetization_beta_zero (IsingModel.latticeGraph d) Λ J i

/-! ## Moved: spontaneousCorrelation_latticeGraph wrappers

The three wrappers
`spontaneousCorrelation_latticeGraph_J_zero`,
`spontaneousCorrelation_latticeGraph_beta_zero`,
`spontaneousCorrelation_latticeGraph_empty` now live in
`UniformMagSpontaneousCorrelation.lean`. -/


/-- **ℤ^d correlationInfinite at J = h = 0 vanishes for nonempty A** (Step 280). -/
theorem correlationInfinite_latticeGraph_zero_params_vanish_of_nonempty_A
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) {β : ℝ} (hβ : 0 < β)
    {A : Finset (Fin d → ℤ)} (hA : A.Nonempty) :
    correlationInfinite (IsingModel.latticeGraph d) Λ ⟨0, 0, β⟩ A = 0 :=
  correlationInfinite_zero_params_vanish_of_nonempty_A
    (IsingModel.latticeGraph d) Λ hβ hA

end Ambient
end IsingModel
