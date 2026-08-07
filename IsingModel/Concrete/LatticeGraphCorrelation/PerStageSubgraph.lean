import IsingModel.FreeEnergy.SubgraphBounds

/-!
# Concrete ℤ^d Λ-induced subgraph monotonicity wrappers

Instantiates the abstract subgraph-monotonicity statements at `IsingModel.latticeGraph d` for
the partition function, the correlation, the log partition function and the free energy —
the per-stage comparison that drives the ℤ^d exhaustion limits.
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

end Ambient

end IsingModel
