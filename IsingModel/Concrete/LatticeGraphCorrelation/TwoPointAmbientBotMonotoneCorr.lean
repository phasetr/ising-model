import IsingModel.AmbientLattice.CorrelationInfinite.AmbientSubgraph

/-!
# Ambient-subgraph monotonicity of the correlation on ℤ^d sites

Statements on the vertex type `Fin d → ℤ` comparing two ambient simple graphs `G₁ ≤ G₂` on
it. Despite the declaration names, no statement here mentions `IsingModel.latticeGraph d`:
the dimension only fixes the vertex type, and the graphs are arbitrary.

Under `Ferromagnetic` on the parameter record, adding edges to the ambient graph does not
decrease the correlation of a site set — at a fixed finite volume, at a stage of an
arbitrary `Ambient.Exhaustion`, and in the infinite-volume limit along one. Every statement
takes a pair of instance arguments, one per graph: a `Fintype` on the edge set induced at
the fixed finite volume in the Λ-layer statement, and a stagewise `Fintype` on the edge
sets induced along the exhaustion in the others.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d correlationΛ ambient-subgraph monotonicity** (ferromagnetic). -/
theorem correlationΛ_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (hG : G₁ ≤ G₂)
    (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph G₁ Λ).edgeSet]
    [Fintype (Ambient.inducedGraph G₂ Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (↑Λ : Type _)) :
    correlationΛ G₁ Λ p A ≤ correlationΛ G₂ Λ p A :=
  correlationΛ_monotone_ambient_subgraph hG Λ p hf A

/-- **ℤ^d correlationAlongExhaustion ambient-subgraph monotonicity** per stage. -/
theorem correlationAlongExhaustion_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (hG : G₁ ≤ G₂)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (Fin d → ℤ)) (n : ℕ) :
    correlationAlongExhaustion G₁ Λ p A n
      ≤ correlationAlongExhaustion G₂ Λ p A n :=
  correlationAlongExhaustion_monotone_ambient_subgraph hG Λ p hf A n

/-- **ℤ^d correlationInfinite ambient-subgraph monotonicity**. -/
theorem correlationInfinite_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (hG : G₁ ≤ G₂)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ)) :
    correlationInfinite G₁ Λ p A ≤ correlationInfinite G₂ Λ p A :=
  correlationInfinite_monotone_ambient_subgraph hG Λ p hf A

end Ambient
end IsingModel
