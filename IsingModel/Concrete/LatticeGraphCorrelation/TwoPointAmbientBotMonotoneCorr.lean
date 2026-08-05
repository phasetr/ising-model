import IsingModel.AmbientLattice.CorrelationInfinite.AmbientSubgraph

/-!
# ℤ^d correlation `*_monotone_ambient_subgraph` wrappers

Narrow child module for three ℤ^d
`correlation*_latticeGraph_monotone_ambient_subgraph` wrappers
(Λ + along-exhaustion + Infinite forms) extracted from
`TwoPointAmbientBotMonotone.lean`:

* `correlationΛ_latticeGraph_monotone_ambient_subgraph`,
* `correlationAlongExhaustion_latticeGraph_monotone_ambient_subgraph`,
* `correlationInfinite_latticeGraph_monotone_ambient_subgraph`.

Each result is a thin pass-through of the corresponding ambient
`correlation*_monotone_ambient_subgraph` lemma. The theorem names are
unchanged from the former `TwoPointAmbientBotMonotone` declarations.
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
