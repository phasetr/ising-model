import IsingModel.PhaseTransition.MagnetizationSusceptibility
import IsingModel.PhaseTransition.CriticalGrowth
import IsingModel.PhaseTransition.BetaRegularity
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d finite-volume magnetization as a parameter grows without bound

Concrete `latticeGraph d` statements that, at a fixed vertex of the subgraph induced by a
fixed finite volume, the magnetization converges when one parameter of the record is sampled
along the natural numbers and the others are held fixed. Growth of the coupling assumes
`0 ≤ h` and `0 < β`; growth of the external field assumes `0 ≤ J` and `0 < β`; growth of the
inverse temperature, taken shifted by one, assumes `0 ≤ J` and `0 ≤ h`. No instance argument
is taken.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d magnetization_convergent_J direct** (Λ-induced, ferromagnetic):
`n ↦ M_i(J = n, h, β)` converges for `h ≥ 0`, `β > 0`. Thin pass-through
of `IsingModel.magnetization_convergent_J`. -/
theorem magnetization_convergent_J_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β)
    (i : (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        ⟨(n : ℝ), h, β⟩ i)
      Filter.atTop (nhds L) :=
  IsingModel.magnetization_convergent_J
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h hh β hβ i

/-- **ℤ^d magnetization_convergent_h direct** (Λ-induced, ferromagnetic):
`n ↦ M_i(J, h = n, β)` converges for `J ≥ 0`, `β > 0`. Thin pass-through
of `IsingModel.magnetization_convergent_h`. -/
theorem magnetization_convergent_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β)
    (i : (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        ⟨J, (n : ℝ), β⟩ i)
      Filter.atTop (nhds L) :=
  IsingModel.magnetization_convergent_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ β hβ i

/-- **ℤ^d magnetization_convergent_beta direct** (Λ-induced, ferromagnetic):
`n ↦ M_i(J, h, β = n+1)` converges for `J ≥ 0`, `h ≥ 0`. Thin
pass-through of `IsingModel.magnetization_convergent_beta`. -/
theorem magnetization_convergent_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h)
    (i : (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        ⟨J, h, (n + 1 : ℝ)⟩ i)
      Filter.atTop (nhds L) :=
  IsingModel.magnetization_convergent_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ h hh i

end Ambient

end IsingModel
