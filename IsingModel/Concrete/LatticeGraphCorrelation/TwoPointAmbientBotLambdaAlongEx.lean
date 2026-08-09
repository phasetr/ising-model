import IsingModel.AmbientLattice.Monotonicity.AmbientSubgraph
import IsingModel.AmbientLattice.CorrelationInfinite.AmbientSubgraph
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Per-stage comparison of the edgeless ambient graph with ℤ^d

Concrete statements along `Ambient.cubicExhaustion d`, comparing the edgeless graph `⊥` on
`Fin d → ℤ` with `IsingModel.latticeGraph d` at a fixed stage. Under `Ferromagnetic` on the
parameter record, the free energy, the partition function and — at a fixed site set — the
correlation are each no larger at `⊥` than at the lattice; each is the ambient
subgraph-monotonicity statement instantiated at `bot_le`.

Every statement takes one instance argument, a stagewise `Fintype` on the edge set that `⊥`
induces at each stage volume; the lattice side is supplied by instances already in scope.
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
