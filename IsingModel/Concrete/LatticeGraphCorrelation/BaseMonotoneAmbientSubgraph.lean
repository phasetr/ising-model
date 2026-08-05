/- BaseMonotoneAmbientSubgraph.lean
Narrow child module for the 4 ℤ^d
`magnetization{Λ,AlongExhaustion,Infinite}_latticeGraph_monotone_ambient_subgraph`
and `spontaneousCorrelation_latticeGraph_monotone_ambient_subgraph`
wrappers extracted from `Base.lean` in PR #2033. Each is a thin
pass-through to the abstract `*_monotone_ambient_subgraph` lemma at
`latticeGraph d`. The theorem names are unchanged from the former
`Base` declarations.
-/
import IsingModel.AmbientLattice.SpontaneousMono

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
