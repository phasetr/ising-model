import IsingModel.FreeEnergy.SubgraphBounds

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

/-! ## Moved: *_convergent_subgraph_latticeGraph wrappers

The four wrappers
`correlation_convergent_subgraph_latticeGraph`,
`magnetization_convergent_subgraph_latticeGraph`,
`twoPoint_convergent_subgraph_latticeGraph`,
`freeEnergy_convergent_subgraph_latticeGraph` now live in
`PerStageSubgraphConvergent.lean`. -/

end Ambient

end IsingModel
