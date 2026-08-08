import IsingModel.AmbientLattice.Monotonicity.AmbientSubgraph

/-!
# ℤ^d Λ + alongExhaustion `*_monotone_ambient_subgraph` wrappers

Records monotonicity under enlarging an arbitrary ambient graph on `Fin d → ℤ` at the Λ and
along-exhaustion levels for the free energy and the partition function. Each is a
pass-through of the corresponding ambient `*_monotone_ambient_subgraph` lemma.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d freeEnergyΛ ambient-subgraph monotonicity** (ferromagnetic):
for `G₁ ≤ G₂`, `freeEnergyΛ G₁ Λ p ≤ freeEnergyΛ G₂ Λ p`. -/
theorem freeEnergyΛ_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (hG : G₁ ≤ G₂)
    (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph G₁ Λ).edgeSet]
    [Fintype (Ambient.inducedGraph G₂ Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    freeEnergyΛ G₁ Λ p ≤ freeEnergyΛ G₂ Λ p :=
  freeEnergyΛ_monotone_ambient_subgraph hG Λ p hf

/-- **ℤ^d freeEnergyAlongExhaustion ambient-subgraph monotonicity** per stage. -/
theorem freeEnergyAlongExhaustion_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (hG : G₁ ≤ G₂)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    freeEnergyAlongExhaustion G₁ Λ p n
      ≤ freeEnergyAlongExhaustion G₂ Λ p n :=
  freeEnergyAlongExhaustion_monotone_ambient_subgraph hG Λ p hf n

/-- **ℤ^d partitionFunctionΛ ambient-subgraph monotonicity** (ferromagnetic). -/
theorem partitionFunctionΛ_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (hG : G₁ ≤ G₂)
    (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph G₁ Λ).edgeSet]
    [Fintype (Ambient.inducedGraph G₂ Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    partitionFunctionΛ G₁ Λ p ≤ partitionFunctionΛ G₂ Λ p :=
  partitionFunctionΛ_monotone_ambient_subgraph hG Λ p hf

/-- **ℤ^d partitionFunctionAlongExhaustion ambient-subgraph monotonicity** per stage. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (hG : G₁ ≤ G₂)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    partitionFunctionAlongExhaustion G₁ Λ p n
      ≤ partitionFunctionAlongExhaustion G₂ Λ p n :=
  partitionFunctionAlongExhaustion_monotone_ambient_subgraph hG Λ p hf n

end Ambient
end IsingModel
