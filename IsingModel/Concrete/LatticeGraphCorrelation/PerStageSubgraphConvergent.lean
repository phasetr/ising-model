import IsingModel.FreeEnergy.SpecialValues

/-!
# ℤ^d *_convergent_subgraph_latticeGraph wrappers

Narrow child module for four ℤ^d
`*_convergent_subgraph_latticeGraph` wrappers extracted from
`PerStageSubgraph.lean`:

* `correlation_convergent_subgraph_latticeGraph`,
* `magnetization_convergent_subgraph_latticeGraph`,
* `twoPoint_convergent_subgraph_latticeGraph`,
* `freeEnergy_convergent_subgraph_latticeGraph`.
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
