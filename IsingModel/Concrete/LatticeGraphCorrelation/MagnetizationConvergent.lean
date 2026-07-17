/- MagnetizationConvergent.lean
Narrow child module for the 9 ℤ^d `magnetization_convergent_*`,
`truncated2_convergent_*`, `susceptibility_convergent_subgraph`, and
`magnetization_total_convergent_subgraph` wrappers extracted from
`Magnetization.lean` in PR #2030. The theorem names are unchanged
from the former `Magnetization` declarations.
-/
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ### Magnetization / truncated-2 / susceptibility convergence wrappers

Direct ℤ^d forwarders for `magnetization_convergent_{J,h,beta}`,
`truncated2_convergent_{J,h,beta,subgraph}`, and
`susceptibility_convergent_subgraph` /
`magnetization_total_convergent_subgraph` (`IsingModel/PhaseTransition.lean`). -/

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

/-! ## Moved: truncated2_convergent wrappers

The three wrappers
`truncated2_convergent_J_latticeGraph`,
`truncated2_convergent_h_latticeGraph`,
`truncated2_convergent_beta_latticeGraph` now live in
`MagnetizationConvergentTruncated2.lean`. -/


/-! ## Moved: ℤ^d *_convergent_subgraph_latticeGraph wrappers

The three wrappers
`truncated2_convergent_subgraph_latticeGraph`,
`susceptibility_convergent_subgraph_latticeGraph`,
`magnetization_total_convergent_subgraph_latticeGraph`
now live in `MagnetizationConvergentSubgraph.lean`. -/


end Ambient

end IsingModel
