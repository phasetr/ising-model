import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion` h-symmetry wrappers

Narrow child module for 3 ℤ^d `freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_*`
h-symmetry wrappers extracted from `FreeEnergySpecialCasesAlongEx.lean`:

* `freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_neg_h`,
* `freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_eq_abs_h`,
* `freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_monotone_abs_h`.

Each result is a thin pass-through of the corresponding ambient
`freeEnergyAlongExhaustion_{neg_h,eq_abs_h,monotone_abs_h}` lemma at
`(G, Λ) := (IsingModel.latticeGraph d, Ambient.cubicExhaustion d)`.
The theorem names are unchanged from the former
`FreeEnergySpecialCasesAlongEx` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d freeEnergyAlongExhaustion h-evenness** per stage:
`f(Λ_n; J,-h,β) = f(Λ_n; J,h,β)`. Concrete specialization of
`freeEnergyAlongExhaustion_neg_h`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_neg_h
    (d : ℕ) (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, -h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_neg_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h β n

/-- **ℤ^d freeEnergyAlongExhaustion `|h|`-rewrite** per stage. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_eq_abs_h
    (d : ℕ) (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, |h|, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_eq_abs_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h β n

/-- **ℤ^d freeEnergyAlongExhaustion ferromagnetic `|h|`-monotonicity**
per stage. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_monotone_abs_h
    (d : ℕ) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h₁, β⟩ : IsingParams ℝ) n
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h₂, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_monotone_abs_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β hJ hβ hh n

end Ambient

end IsingModel
