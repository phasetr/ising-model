import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d freeEnergy monotonicity wrappers (h, J, β)

Narrow child module for three ℤ^d
`freeEnergy_monotone_{h,J,beta}_latticeGraph` wrappers extracted from
`FreeEnergySpecialCasesFiniteVol.lean`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d freeEnergy_monotone_h direct** (Λ-induced, ferromagnetic). -/
theorem freeEnergy_monotone_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    MonotoneOn (IsingModel.freeEnergyH
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β) (Set.Ici 0) :=
  IsingModel.freeEnergy_monotone_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β hJ hβ

/-- **ℤ^d freeEnergy_monotone_J direct** (Λ-induced, ferromagnetic). -/
theorem freeEnergy_monotone_J_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) :
    MonotoneOn (IsingModel.freeEnergyJ
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β) (Set.Ici 0) :=
  IsingModel.freeEnergy_monotone_J
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β hh hβ

/-- **ℤ^d freeEnergy_monotone_beta direct** (Λ-induced, ferromagnetic). -/
theorem freeEnergy_monotone_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) :
    MonotoneOn
      (fun β : ℝ => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) ⟨J, h, β⟩)
      (Set.Ioi 0) :=
  IsingModel.freeEnergy_monotone_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ h hh

end Ambient
end IsingModel
