import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.Translation
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.AmbientLattice.SpecialCases.InfiniteVolume
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint

/-!
# ℤ^d Λ + alongExhaustion `*_monotone_ambient_subgraph` wrappers

Narrow child module for seven ℤ^d `*_latticeGraph_monotone_ambient_subgraph`
wrappers (Λ + along-exhaustion + correlationInfinite forms) for
`{free,partition}Energy` and `correlation` ambient subgraph monotonicity.
Each wrapper is a thin pass-through to the corresponding ambient
`*_monotone_ambient_subgraph` lemma.
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
