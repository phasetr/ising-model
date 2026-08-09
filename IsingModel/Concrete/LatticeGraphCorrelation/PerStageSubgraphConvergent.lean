import IsingModel.FreeEnergy.SpecialValues

/-!
# ℤ^d convergence of finite-volume quantities along an increasing graph sequence

Concrete statements at the vertex type of a fixed finite volume of `Fin d → ℤ`: along a
monotone sequence of simple graphs on that vertex type, and for a parameter record satisfying
`Ferromagnetic`, the correlation of a finite set of vertices converges, as do its
specialisations at a singleton and at a pair, and so does the free energy. Only the vertex
type comes from `latticeGraph d`; the graphs in the sequence are arbitrary. Monotonicity of
the sequence and `Ferromagnetic` are the hypotheses in every case, and every statement
requires a `Fintype` instance on the edge set of each graph in the sequence.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d correlation_convergent_subgraph at Λ-induced**: for a monotone
sequence of subgraphs on `↑Λ` and ferromagnetic `p`,
`n ↦ correlation (Gn n) p A` converges. -/
theorem correlation_convergent_subgraph_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (Gn : ℕ → SimpleGraph (↑Λ : Type _)) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.correlation (Gn n) p A)
      Filter.atTop (nhds L) :=
  IsingModel.correlation_convergent_subgraph Gn hmono p hf A

/-- **ℤ^d magnetization_convergent_subgraph at Λ-induced**. -/
theorem magnetization_convergent_subgraph_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (Gn : ℕ → SimpleGraph (↑Λ : Type _)) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (i : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.correlation (Gn n) p {i})
      Filter.atTop (nhds L) :=
  IsingModel.magnetization_convergent_subgraph Gn hmono p hf i

/-- **ℤ^d twoPoint_convergent_subgraph at Λ-induced**. -/
theorem twoPoint_convergent_subgraph_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (Gn : ℕ → SimpleGraph (↑Λ : Type _)) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (i j : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.correlation (Gn n) p {i, j})
      Filter.atTop (nhds L) :=
  IsingModel.twoPoint_convergent_subgraph Gn hmono p hf i j

/-- **ℤ^d `freeEnergy_convergent_subgraph` at Λ-induced subgraph**:
for a monotone sequence of subgraphs `Gn : ℕ → SimpleGraph ↑Λ` and
ferromagnetic `p`, `n ↦ freeEnergy (Gn n) p` converges. -/
theorem freeEnergy_convergent_subgraph_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (Gn : ℕ → SimpleGraph (↑Λ : Type _)) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.freeEnergy (Gn n) p)
      Filter.atTop (nhds L) :=
  IsingModel.freeEnergy_convergent_subgraph Gn hmono p hf


end Ambient

end IsingModel
