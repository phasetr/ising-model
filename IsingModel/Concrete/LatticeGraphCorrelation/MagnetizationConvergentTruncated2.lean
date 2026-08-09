import IsingModel.PhaseTransition.BetaRegularity
import IsingModel.Inequalities.GHS.TruncatedDefs
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d truncated two-point function as a parameter grows without bound

Concrete `latticeGraph d` statements that, at a pair of vertices of the subgraph induced by a
fixed finite volume, the truncated two-point function converges when one parameter of the
record is sampled along the natural numbers and the others are held fixed. Growth of the
coupling assumes `0 ≤ h` and `0 < β`; growth of the external field assumes `0 ≤ J` and
`0 < β`; growth of the inverse temperature, taken shifted by one, assumes `0 ≤ J` and
`0 ≤ h`. The vertices are not assumed distinct, and no instance argument is taken.
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
