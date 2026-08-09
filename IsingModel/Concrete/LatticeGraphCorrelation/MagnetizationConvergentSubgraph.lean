import IsingModel.PhaseTransition.CriticalGrowth

/-!
# ℤ^d convergence along an increasing sequence of graphs on a finite volume

Concrete statements at the vertex type of a fixed finite volume of `Fin d → ℤ`: along a
monotone sequence of simple graphs on that vertex type, and for a parameter record satisfying
`Ferromagnetic`, the truncated two-point function at a pair of vertices, the susceptibility
at a vertex, and the sum of the magnetizations over all vertices each converge. Only the
vertex type comes from `latticeGraph d`; the graphs in the sequence are arbitrary.
Monotonicity of the sequence and `Ferromagnetic` are the hypotheses in every case, and every
statement requires a `Fintype` instance on the edge set of each graph in the sequence.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

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
