/- MagnetizationConvergent.lean
Narrow child module for the 9 ℤ^d `magnetization_convergent_*`,
`truncated2_convergent_*`, `susceptibility_convergent_subgraph`, and
`magnetization_total_convergent_subgraph` wrappers extracted from
`Magnetization.lean` in PR #2030. The theorem names are unchanged
from the former `Magnetization` declarations.
-/
import IsingModel.Concrete.LatticeGraphBED
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG

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

/-- **ℤ^d truncated2_convergent_subgraph direct** (Λ-induced,
ferromagnetic): `n ↦ ⟨σ_i; σ_j⟩_{Gₙ}` converges along any increasing
subgraph sequence `Gₙ : ℕ → SimpleGraph (↑Λ)` (note: `Gₙ` is arbitrary
on the Λ-induced vertex type; this wrapper only fixes `ι = ↑Λ`, not the
graph itself). Thin pass-through of
`IsingModel.truncated2_convergent_subgraph`. -/
theorem truncated2_convergent_subgraph_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (Gn : ℕ → SimpleGraph (↑Λ : Type _)) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (i j : (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.truncated2 (Gn n) p i j)
      Filter.atTop (nhds L) :=
  IsingModel.truncated2_convergent_subgraph Gn hmono p hf i j

/-- **ℤ^d susceptibility_convergent_subgraph direct** (Λ-induced,
ferromagnetic): `n ↦ χ_i(Gₙ)` converges along any increasing subgraph
sequence `Gₙ : ℕ → SimpleGraph (↑Λ)` (note: `Gₙ` is arbitrary on the
Λ-induced vertex type; this wrapper only fixes `ι = ↑Λ`, not the graph
itself). Thin pass-through of
`IsingModel.susceptibility_convergent_subgraph`. -/
theorem susceptibility_convergent_subgraph_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (Gn : ℕ → SimpleGraph (↑Λ : Type _)) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (i : (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.susceptibility (Gn n) p i)
      Filter.atTop (nhds L) :=
  IsingModel.susceptibility_convergent_subgraph Gn hmono p hf i

/-- **ℤ^d magnetization_total_convergent_subgraph direct** (Λ-induced,
ferromagnetic): `n ↦ Σ_i M_i(Gₙ)` converges along any increasing
subgraph sequence `Gₙ : ℕ → SimpleGraph (↑Λ)` (note: `Gₙ` is arbitrary on
the Λ-induced vertex type; this wrapper only fixes `ι = ↑Λ`, not the
graph itself). Thin pass-through of
`IsingModel.magnetization_total_convergent_subgraph`. -/
theorem magnetization_total_convergent_subgraph_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (Gn : ℕ → SimpleGraph (↑Λ : Type _)) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => ∑ i : (↑Λ : Type _), IsingModel.magnetization (Gn n) p i)
      Filter.atTop (nhds L) :=
  IsingModel.magnetization_total_convergent_subgraph Gn hmono p hf

end Ambient

end IsingModel
