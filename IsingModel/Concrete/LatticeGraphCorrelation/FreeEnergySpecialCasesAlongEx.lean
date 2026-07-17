import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete ℤ^d `freeEnergyAlongExhaustion` special-case wrappers

Narrow child module for the 12 ℤ^d `freeEnergyAlongExhaustion_latticeGraph_*`
wrappers (h-symmetry, |h|-monotonicity, and trivial-slice closed forms at
both the generic Exhaustion and the cubicExhaustion d) extracted from
`FreeEnergySpecialCases.lean` in PR #2041. Each is a thin pass-through to
the corresponding abstract `freeEnergyAlongExhaustion_*` lemma at
`latticeGraph d`. The theorem names are unchanged from the former
`FreeEnergySpecialCases` declarations.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d `freeEnergyAlongExhaustion` wrappers -/

/-! ## Moved: cubicExhaustion h-symmetry wrappers

The three `freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_{neg_h,eq_abs_h,monotone_abs_h}`
h-symmetry wrappers now live in
`FreeEnergySpecialCasesAlongExCubicHSymmetry.lean`. -/


/-- **ℤ^d freeEnergyAlongExhaustion h-evenness** per stage (any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_neg_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, -h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_neg_h (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d freeEnergyAlongExhaustion `|h|`-rewrite** per stage (any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_eq_abs_h (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d freeEnergyAlongExhaustion ferromagnetic `|h|`-monotonicity**
per stage (any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_monotone_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ) n
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_monotone_abs_h (IsingModel.latticeGraph d) Λ
    J β hJ hβ hh n

/-! ## Moved: any-Λ trivial-slice freeEnergyAlongEx wrappers

The three wrappers
`freeEnergyAlongExhaustion_latticeGraph_beta_zero`,
`freeEnergyAlongExhaustion_latticeGraph_zero_params`,
`freeEnergyAlongExhaustion_latticeGraph_J_zero` now live in
`FreeEnergySpecialCasesAlongExTrivialSlice.lean`. -/


/-! ## Moved: cubicExhaustion trivial-slice wrappers

The three `freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_*`
trivial-slice wrappers (`beta_zero`, `zero_params`, `J_zero`) now live in
`FreeEnergySpecialCasesAlongExCubicTrivialSlice.lean`. -/




end Ambient

end IsingModel
