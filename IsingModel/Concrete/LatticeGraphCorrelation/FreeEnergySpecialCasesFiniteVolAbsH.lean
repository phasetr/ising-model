import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete ℤ^d finite-volume `freeEnergy` h-symmetry wrappers

Narrow child module for three ℤ^d
`freeEnergy_{neg_h,eq_abs_h,monotone_abs_h}_latticeGraph` h-symmetry
/ absolute-field wrappers. Each wrapper is a thin pass-through to the
corresponding ambient `IsingModel.freeEnergy_*` lemma at the induced
graph.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d freeEnergy_neg_h at Λ-induced**. -/
theorem freeEnergy_neg_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, -h, β⟩ : IsingParams ℝ)
      = IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) :=
  IsingModel.freeEnergy_neg_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β

/-- **ℤ^d freeEnergy_eq_abs_h at Λ-induced**. -/
theorem freeEnergy_eq_abs_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, β⟩ : IsingParams ℝ)
      = IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, |h|, β⟩ : IsingParams ℝ) :=
  IsingModel.freeEnergy_eq_abs_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β

/-- **ℤ^d freeEnergy_monotone_abs_h at Λ-induced** (ferromagnetic). -/
theorem freeEnergy_monotone_abs_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h₂, β⟩ : IsingParams ℝ) :=
  IsingModel.freeEnergy_monotone_abs_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β hJ hβ hh


end Ambient
end IsingModel
