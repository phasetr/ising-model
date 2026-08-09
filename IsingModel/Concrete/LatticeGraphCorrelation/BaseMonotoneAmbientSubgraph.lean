import IsingModel.AmbientLattice.SpontaneousMono

/-!
# Ambient-subgraph monotonicity of the magnetization on ℤ^d sites

Statements on the vertex type `Fin d → ℤ` comparing two ambient simple graphs `G₁ ≤ G₂` on
it. Despite the declaration names, no statement here mentions `IsingModel.latticeGraph d`:
the dimension only fixes the vertex type, and the graphs are arbitrary.

Adding edges to the ambient graph does not decrease the magnetization — at a fixed finite
volume, at a stage of an arbitrary `Ambient.Exhaustion`, and in the infinite-volume limit
along one — nor the spontaneous correlation of a fixed finite site set. The magnetization
statements assume `Ferromagnetic` on the parameter record; the spontaneous-correlation one
takes the coupling and the inverse temperature separately rather than as a record, and
assumes instead that the coupling is non-negative and the inverse temperature positive.

Every statement here takes a pair of instance arguments, one per graph: a `Fintype` on the
edge set induced at the fixed finite volume in the Λ-layer statement, and a stagewise
`Fintype` on the edge sets induced along the exhaustion in the others.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d `magnetizationΛ_monotone_ambient_subgraph`**:
`G₁ ≤ G₂ ⇒ M_{Λ,G₁}(i) ≤ M_{Λ,G₂}(i)` (ferromagnetic). -/
theorem magnetizationΛ_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (h : G₁ ≤ G₂)
    (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph G₁ Λ).edgeSet]
    [Fintype (Ambient.inducedGraph G₂ Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : ↑Λ) :
    magnetizationΛ G₁ Λ p i ≤ magnetizationΛ G₂ Λ p i :=
  magnetizationΛ_monotone_ambient_subgraph h Λ p hf i

/-- **ℤ^d `magnetizationAlongExhaustion_monotone_ambient_subgraph`**
per stage (ferromagnetic). -/
theorem magnetizationAlongExhaustion_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (h : G₁ ≤ G₂)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion G₁ Λ p i n
      ≤ magnetizationAlongExhaustion G₂ Λ p i n :=
  magnetizationAlongExhaustion_monotone_ambient_subgraph h Λ p hf i n

/-- **ℤ^d `magnetizationInfinite_monotone_ambient_subgraph`**
(ferromagnetic). -/
theorem magnetizationInfinite_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (h : G₁ ≤ G₂)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    magnetizationInfinite G₁ Λ p i ≤ magnetizationInfinite G₂ Λ p i :=
  magnetizationInfinite_monotone_ambient_subgraph h Λ p hf i

/-- **ℤ^d `spontaneousCorrelation_monotone_ambient_subgraph`**
(ferromagnetic). -/
theorem spontaneousCorrelation_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (hG : G₁ ≤ G₂)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph G₂ (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation G₁ Λ J β A
      ≤ spontaneousCorrelation G₂ Λ J β A :=
  spontaneousCorrelation_monotone_ambient_subgraph hG Λ hJ hβ A

end Ambient

end IsingModel
