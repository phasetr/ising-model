import IsingModel.PhaseTransition.MagnetizationSusceptibility
import IsingModel.PhaseTransition.CriticalGrowth
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d Λ-induced magnetization trivial-slice / monotone wrappers

Narrow child module for five ℤ^d Λ-induced `magnetization_*_latticeGraph`
wrappers extracted from `MagnetizationSiteLevel.lean`:

* `magnetization_zero_at_h_zero_latticeGraph`,
* `magnetization_beta_zero_latticeGraph`,
* `magnetization_J_zero_latticeGraph`,
* `magnetization_monotone_h_latticeGraph`,
* `magnetization_monotone_beta_latticeGraph`.
-/

namespace IsingModel
namespace Ambient

/-! ## Moved: magnetization Λ-induced trivial-slice wrappers

The three wrappers
`magnetization_zero_at_h_zero_latticeGraph`,
`magnetization_beta_zero_latticeGraph`,
`magnetization_J_zero_latticeGraph` now live in
`MagnetizationSiteLevelTrivialSlice.lean`. -/


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
