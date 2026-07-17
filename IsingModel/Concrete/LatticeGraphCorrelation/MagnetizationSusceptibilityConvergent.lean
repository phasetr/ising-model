import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d susceptibility_convergent wrappers

Narrow child module for three ℤ^d Λ-induced ferromagnetic susceptibility
convergence wrappers extracted from `MagnetizationSusceptibility.lean`:

* `susceptibility_convergent_J_latticeGraph`,
* `susceptibility_convergent_h_latticeGraph`,
* `susceptibility_convergent_beta_latticeGraph`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d susceptibility_convergent_J direct** (Λ-induced, ferromagnetic):
`n ↦ χ_i(n, h, β)` converges for `h ≥ 0`, `β > 0`. Thin pass-through of
`IsingModel.susceptibility_convergent_J`. -/
theorem susceptibility_convergent_J_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β)
    (i : (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.susceptibility
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        ⟨(n : ℝ), h, β⟩ i)
      Filter.atTop (nhds L) :=
  IsingModel.susceptibility_convergent_J
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h hh β hβ i

/-- **ℤ^d susceptibility_convergent_h direct** (Λ-induced, ferromagnetic):
`n ↦ χ_i(J, n, β)` converges for `J ≥ 0`, `β > 0`. Thin pass-through of
`IsingModel.susceptibility_convergent_h`. -/
theorem susceptibility_convergent_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β)
    (i : (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.susceptibility
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        ⟨J, (n : ℝ), β⟩ i)
      Filter.atTop (nhds L) :=
  IsingModel.susceptibility_convergent_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ β hβ i

/-- **ℤ^d susceptibility_convergent_beta direct** (Λ-induced,
ferromagnetic): `n ↦ χ_i(J, h, n+1)` converges for `J ≥ 0`, `h ≥ 0`.
Thin pass-through of `IsingModel.susceptibility_convergent_beta`. -/
theorem susceptibility_convergent_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h)
    (i : (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.susceptibility
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        ⟨J, h, (n + 1 : ℝ)⟩ i)
      Filter.atTop (nhds L) :=
  IsingModel.susceptibility_convergent_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ h hh i

end Ambient
end IsingModel
