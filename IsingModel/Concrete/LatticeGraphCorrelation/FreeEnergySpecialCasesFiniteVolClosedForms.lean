import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d finite-volume `freeEnergy_*_latticeGraph` closed-form wrappers

Narrow child module for 3 ℤ^d Λ-induced `freeEnergy` trivial-slice
closed-form wrappers extracted from `FreeEnergySpecialCasesFiniteVol.lean`:

* `freeEnergy_zero_params_latticeGraph`,
* `freeEnergy_beta_zero_latticeGraph`,
* `freeEnergy_J_zero_latticeGraph`.

Each result is a thin pass-through of the corresponding abstract
`IsingModel.freeEnergy_{zero_params,beta_zero,J_zero}` lemma at
`Ambient.inducedGraph (IsingModel.latticeGraph d) Λ`. The theorem
names are unchanged from the former `FreeEnergySpecialCasesFiniteVol`
declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d freeEnergy_zero_params at Λ-induced**:
`freeEnergy ⟨0, 0, β⟩ = log 2` for nonempty Λ. -/
theorem freeEnergy_zero_params_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 :=
  IsingModel.freeEnergy_zero_params
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β hne

/-- **ℤ^d freeEnergy_beta_zero at Λ-induced**:
`freeEnergy ⟨J, h, 0⟩ = log 2` for nonempty Λ. -/
theorem freeEnergy_beta_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, 0⟩ : IsingParams ℝ) = Real.log 2 :=
  IsingModel.freeEnergy_beta_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h hne

/-- **ℤ^d freeEnergy_J_zero at Λ-induced**:
`freeEnergy ⟨0, h, β⟩ = log(2·cosh(β·h))` for nonempty Λ. -/
theorem freeEnergy_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ)
      = Real.log (2 * Real.cosh (β * h)) :=
  IsingModel.freeEnergy_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β hne

end Ambient

end IsingModel
