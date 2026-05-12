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
# ℤ^d Λ + alongExhaustion `*_bot_le_latticeGraph` wrappers

Narrow child module for seven ℤ^d `*_bot_le_latticeGraph` ambient
subgraph monotonicity wrappers (Λ + along-exhaustion forms) for
`{free,partition}Energy`, `correlation`, and `log_partitionFunction`.
Each wrapper is a thin pass-through to the corresponding ambient
`*_monotone_ambient_subgraph` lemma at `IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d freeEnergyAlongExhaustion ambient-subgraph monotonicity** from ⊥. -/
theorem freeEnergyAlongExhaustion_bot_le_latticeGraph
    (d : ℕ)
    [∀ n, Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ))
      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    freeEnergyAlongExhaustion (⊥ : SimpleGraph (Fin d → ℤ))
        (Ambient.cubicExhaustion d) p n
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p n :=
  freeEnergyAlongExhaustion_monotone_ambient_subgraph bot_le
    (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d partitionFunctionAlongExhaustion ambient-subgraph monotonicity** from ⊥. -/
theorem partitionFunctionAlongExhaustion_bot_le_latticeGraph
    (d : ℕ)
    [∀ n, Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ))
      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    partitionFunctionAlongExhaustion (⊥ : SimpleGraph (Fin d → ℤ))
        (Ambient.cubicExhaustion d) p n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p n :=
  partitionFunctionAlongExhaustion_monotone_ambient_subgraph bot_le
    (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d correlationAlongExhaustion ambient-subgraph monotonicity** from ⊥. -/
theorem correlationAlongExhaustion_bot_le_latticeGraph
    (d : ℕ)
    [∀ n, Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ))
      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ))
    (n : ℕ) :
    correlationAlongExhaustion (⊥ : SimpleGraph (Fin d → ℤ))
        (Ambient.cubicExhaustion d) p A n
      ≤ correlationAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p A n :=
  correlationAlongExhaustion_monotone_ambient_subgraph bot_le
    (Ambient.cubicExhaustion d) p hf A n

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
