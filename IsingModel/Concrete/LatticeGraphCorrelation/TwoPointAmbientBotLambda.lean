import IsingModel.AmbientLattice.Monotonicity.AmbientSubgraph
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d Λ-level `*_bot_le_latticeGraph` wrappers

Specializes ambient-subgraph monotonicity to the comparison of the empty ambient graph `⊥`
with `IsingModel.latticeGraph d` at the Λ level, for the partition function, the free
energy, the correlation and the log partition function.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d partitionFunctionΛ ambient-subgraph monotonicity** from ⊥. -/
theorem partitionFunctionΛ_bot_le_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ)) Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    partitionFunctionΛ (⊥ : SimpleGraph (Fin d → ℤ)) Λ p
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_monotone_ambient_subgraph bot_le Λ p hf

/-- **ℤ^d freeEnergyΛ ambient-subgraph monotonicity** from ⊥. -/
theorem freeEnergyΛ_bot_le_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ)) Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    freeEnergyΛ (⊥ : SimpleGraph (Fin d → ℤ)) Λ p
      ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ p :=
  freeEnergyΛ_monotone_ambient_subgraph bot_le Λ p hf

/-- **ℤ^d correlationΛ ambient-subgraph monotonicity** from ⊥. -/
theorem correlationΛ_bot_le_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ)) Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (↑Λ : Type _)) :
    correlationΛ (⊥ : SimpleGraph (Fin d → ℤ)) Λ p A
      ≤ correlationΛ (IsingModel.latticeGraph d) Λ p A :=
  correlationΛ_monotone_ambient_subgraph bot_le Λ p hf A

/-- **ℤ^d `log Z_Λ` ambient-subgraph `⊥ ≤ latticeGraph d`** (ferromagnetic):
from `partitionFunctionΛ_bot_le_latticeGraph` via `Real.log_le_log`. -/
theorem log_partitionFunctionΛ_bot_le_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ)) Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Real.log (partitionFunctionΛ (⊥ : SimpleGraph (Fin d → ℤ)) Λ p)
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  Real.log_le_log (partitionFunctionΛ_pos _ Λ p)
    (partitionFunctionΛ_bot_le_latticeGraph d Λ p hf)

end Ambient
end IsingModel
