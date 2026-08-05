import IsingModel.AmbientLattice.Monotonicity.AmbientSubgraph
import IsingModel.AmbientLattice.CorrelationInfinite.AmbientSubgraph
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d AlongExhaustion `*_bot_le_latticeGraph` wrappers

Narrow child module for three ℤ^d `*AlongExhaustion_bot_le_latticeGraph`
ambient-subgraph monotonicity wrappers (from ⊥ to `latticeGraph d`)
extracted from `TwoPointAmbientBotLambda.lean`:

* `freeEnergyAlongExhaustion_bot_le_latticeGraph`,
* `partitionFunctionAlongExhaustion_bot_le_latticeGraph`,
* `correlationAlongExhaustion_bot_le_latticeGraph`.

Each result is a thin pass-through of the corresponding ambient
`*_monotone_ambient_subgraph` lemma at `bot_le`. The theorem names
are unchanged from the former `TwoPointAmbientBotLambda` declarations.
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

end Ambient
end IsingModel
