import IsingModel.PhaseTransition.MagnetizationSusceptibility
import IsingModel.PhaseTransition.CriticalGrowth
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d Λ-induced magnetization monotonicity wrappers

Instantiates monotonicity of the Λ-induced magnetization in the external field and in the
inverse temperature at `IsingModel.latticeGraph d`, the ℤ^d form of the GKS-II consequences
used by the phase-transition arguments.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d magnetization_monotone_h direct** (Λ-induced, ferromagnetic):
`h ↦ M_i(J, h, β)` is `MonotoneOn (Set.Ici 0)` for `J ≥ 0`, `β > 0`. -/
theorem magnetization_monotone_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (i : (↑Λ : Type _)) :
    MonotoneOn
      (fun h : ℝ => IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) ⟨J, h, β⟩ i)
      (Set.Ici 0) :=
  IsingModel.magnetization_monotone_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β hJ hβ i

/-- **ℤ^d magnetization_monotone_beta direct** (Λ-induced, ferromagnetic):
`β ↦ M_i(J, h, β)` is `MonotoneOn (Set.Ioi 0)` for `J, h ≥ 0`. -/
theorem magnetization_monotone_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h)
    (i : (↑Λ : Type _)) :
    MonotoneOn
      (fun β : ℝ => IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) ⟨J, h, β⟩ i)
      (Set.Ioi 0) :=
  IsingModel.magnetization_monotone_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ h hh i

end Ambient
end IsingModel
