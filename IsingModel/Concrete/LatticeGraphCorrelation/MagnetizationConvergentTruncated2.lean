import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `truncated2_convergent_*_latticeGraph` wrappers

Narrow child module for three ℤ^d `truncated2_convergent_*_latticeGraph`
wrappers extracted from `MagnetizationConvergent.lean`:

* `truncated2_convergent_J_latticeGraph`,
* `truncated2_convergent_h_latticeGraph`,
* `truncated2_convergent_beta_latticeGraph`.

Each result is a thin pass-through of the abstract
`IsingModel.truncated2_convergent_*` lemma on the Λ-induced graph at
`IsingModel.latticeGraph d`. The theorem names are unchanged from
the former `MagnetizationConvergent` declarations.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d truncated2_convergent_J direct** (Λ-induced, ferromagnetic):
`n ↦ ⟨σ_i; σ_j⟩_{(n, h, β)}` converges for `h ≥ 0`, `β > 0`. Thin
pass-through of `IsingModel.truncated2_convergent_J`. -/
theorem truncated2_convergent_J_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β)
    (i j : (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.truncated2
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        ⟨(n : ℝ), h, β⟩ i j)
      Filter.atTop (nhds L) :=
  IsingModel.truncated2_convergent_J
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h hh β hβ i j

/-- **ℤ^d truncated2_convergent_h direct** (Λ-induced, ferromagnetic):
`n ↦ ⟨σ_i; σ_j⟩_{(J, n, β)}` converges for `J ≥ 0`, `β > 0`. Thin
pass-through of `IsingModel.truncated2_convergent_h`. -/
theorem truncated2_convergent_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β)
    (i j : (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.truncated2
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        ⟨J, (n : ℝ), β⟩ i j)
      Filter.atTop (nhds L) :=
  IsingModel.truncated2_convergent_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ β hβ i j

/-- **ℤ^d truncated2_convergent_beta direct** (Λ-induced, ferromagnetic):
`n ↦ ⟨σ_i; σ_j⟩_{(J, h, n+1)}` converges for `J ≥ 0`, `h ≥ 0`. Thin
pass-through of `IsingModel.truncated2_convergent_beta`. -/
theorem truncated2_convergent_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h)
    (i j : (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.truncated2
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        ⟨J, h, (n + 1 : ℝ)⟩ i j)
      Filter.atTop (nhds L) :=
  IsingModel.truncated2_convergent_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ h hh i j

end Ambient

end IsingModel
