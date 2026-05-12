import IsingModel.Concrete.LatticeGraphBED
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG

/-!
# Concrete ℤ^d Λ-induced subgraph monotone/convergent wrappers

Narrow child module for the 8 ℤ^d Λ-induced subgraph wrappers
(`partitionFunction_monotone_subgraph_latticeGraph`,
`correlation_monotone_subgraph_latticeGraph`,
`log_partitionFunction_monotone_subgraph_latticeGraph`,
`freeEnergy_monotone_subgraph_latticeGraph`,
`correlation_convergent_subgraph_latticeGraph`,
`magnetization_convergent_subgraph_latticeGraph`,
`twoPoint_convergent_subgraph_latticeGraph`,
`freeEnergy_convergent_subgraph_latticeGraph`) extracted from
`PerStage.lean` in PR #2049. Each is a thin pass-through to the
corresponding abstract `IsingModel.*_{monotone,convergent}_subgraph`
lemma. The theorem names are unchanged from the former `PerStage`
declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d partitionFunction monotone_subgraph** at Λ-induced subgraph:
`G₁ ≤ G₂ ⇒ Z_{G₁} ≤ Z_{G₂}` for ferromagnetic `p`. -/
theorem partitionFunction_monotone_subgraph_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {G₁ G₂ : SimpleGraph (↑Λ : Type _)}
    [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
    (h₁₂ : G₁ ≤ G₂) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    IsingModel.partitionFunction G₁ p ≤ IsingModel.partitionFunction G₂ p :=
  IsingModel.partitionFunction_monotone_subgraph h₁₂ p hf

/-- **ℤ^d correlation monotone_subgraph** at Λ-induced subgraph:
`G₁ ≤ G₂ ⇒ ⟨σ^A⟩_{G₁} ≤ ⟨σ^A⟩_{G₂}` for ferromagnetic `p`. -/
theorem correlation_monotone_subgraph_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {G₁ G₂ : SimpleGraph (↑Λ : Type _)}
    [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
    (h₁₂ : G₁ ≤ G₂) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (↑Λ : Type _)) :
    IsingModel.correlation G₁ p A ≤ IsingModel.correlation G₂ p A :=
  IsingModel.correlation_monotone_subgraph h₁₂ p hf A

/-- **ℤ^d log_partitionFunction monotone_subgraph** at Λ-induced subgraph. -/
theorem log_partitionFunction_monotone_subgraph_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {G₁ G₂ : SimpleGraph (↑Λ : Type _)}
    [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
    (h₁₂ : G₁ ≤ G₂) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Real.log (IsingModel.partitionFunction G₁ p)
      ≤ Real.log (IsingModel.partitionFunction G₂ p) :=
  IsingModel.log_partitionFunction_monotone_subgraph h₁₂ p hf

/-- **ℤ^d freeEnergy monotone_subgraph** at Λ-induced subgraph. -/
theorem freeEnergy_monotone_subgraph_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {G₁ G₂ : SimpleGraph (↑Λ : Type _)}
    [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
    (h₁₂ : G₁ ≤ G₂) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    IsingModel.freeEnergy G₁ p ≤ IsingModel.freeEnergy G₂ p :=
  IsingModel.freeEnergy_monotone_subgraph h₁₂ p hf

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
