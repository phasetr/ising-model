import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMagTwoPoint
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.Concrete.LatticeGraphCorrelation.UniformMag

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

/-- **ℤ^d magnetizationΛ at J=0 closed form**: `= tanh(β·h)`. -/
theorem magnetizationΛ_latticeGraph_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) (i : ↑Λ) :
    magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i = Real.tanh (β * h) :=
  magnetizationΛ_J_zero (IsingModel.latticeGraph d) Λ h β i

/-- **ℤ^d magnetizationAlongExhaustion at J=0** per stage (on-stage):
`i ∈ Λ.volume n ⇒ = tanh(β·h)`. -/
theorem magnetizationAlongExhaustion_latticeGraph_J_zero_of_mem
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    {i : Fin d → ℤ} {n : ℕ} (hi : i ∈ Λ.volume n) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i n = Real.tanh (β * h) :=
  magnetizationAlongExhaustion_J_zero_of_mem (IsingModel.latticeGraph d) Λ h β hi

/-- **ℤ^d magnetizationAlongExhaustion at J=0 is eventually `tanh(β·h)`**. -/
theorem magnetizationAlongExhaustion_latticeGraph_J_zero_eventually_eq
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (i : Fin d → ℤ) :
    ∀ᶠ n in Filter.atTop,
      magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨0, h, β⟩ : IsingParams ℝ) i n = Real.tanh (β * h) :=
  magnetizationAlongExhaustion_J_zero_eventually_eq
    (IsingModel.latticeGraph d) Λ h β i


end Ambient

end IsingModel
