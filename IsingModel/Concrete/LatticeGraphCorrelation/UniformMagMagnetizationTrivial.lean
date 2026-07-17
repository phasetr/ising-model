import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d magnetizationΛ + magnetizationAlongExhaustion monotone + trivial-slice wrappers

Narrow child module for 15 ℤ^d wrappers covering
`magnetizationΛ_latticeGraph_*` and
`magnetizationAlongExhaustion_latticeGraph_*` J / h / β monotonicity
on `[0, ∞)` / `(0, ∞)` and trivial slices `h_zero`, `beta_zero`,
`zero_params`, `J_zero` / `J_zero_of_mem` / `J_zero_eventually_eq`.
Theorem names are unchanged from the former `UniformMag`
declarations.
-/

namespace IsingModel
namespace Ambient
/-! ## Moved: magnetization monotone wrappers

The six wrappers `magnetization*_latticeGraph_monotone_{h,beta,J}` now
live in `UniformMagMagnetizationTrivialMonotone.lean`. -/

/-! ## Moved: magnetizationΛ_latticeGraph_h_zero

The Λ-direct h=0 wrapper now lives in
`UniformMagMagnetizationTrivialLambdaTrivial.lean`. -/


/-- **ℤ^d magnetizationAlongExhaustion at h = 0 vanishes (Z₂)** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) i n = 0 :=
  magnetizationAlongExhaustion_h_zero (IsingModel.latticeGraph d) Λ J β i n

/-! ## Moved: magnetizationΛ_latticeGraph_beta_zero

The Λ-direct β=0 wrapper now lives in
`UniformMagMagnetizationTrivialLambdaTrivial.lean`. -/


/-- **ℤ^d magnetizationAlongExhaustion vanishes at β=0** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ)
    (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) i n = 0 :=
  magnetizationAlongExhaustion_beta_zero (IsingModel.latticeGraph d) Λ J h i n

/-! ## Moved: magnetizationΛ_latticeGraph_zero_params

The Λ-direct J=h=0 wrapper now lives in
`UniformMagMagnetizationTrivialLambdaTrivial.lean`. -/


/-- **ℤ^d magnetizationAlongExhaustion vanishes at J=h=0** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_zero_params
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ)
    (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) i n = 0 :=
  magnetizationAlongExhaustion_zero_params (IsingModel.latticeGraph d) Λ β i n

/-! ## Moved: magnetization J_zero wrappers

The three wrappers
`magnetizationΛ_latticeGraph_J_zero`,
`magnetizationAlongExhaustion_latticeGraph_J_zero_of_mem`,
`magnetizationAlongExhaustion_latticeGraph_J_zero_eventually_eq` now
live in `UniformMagMagnetizationTrivialJZero.lean`. -/



end Ambient

end IsingModel
