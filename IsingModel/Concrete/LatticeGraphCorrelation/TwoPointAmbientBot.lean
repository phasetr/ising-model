import IsingModel.AmbientLattice.SpecialCases.InfiniteVolume
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPointAmbientBotLambdaAlongEx

/-!
# ℤ^d ambient-subgraph monotonicity + `⊥ ≤ latticeGraph` wrappers

Compares observables on the empty ambient graph `⊥` with those on `IsingModel.latticeGraph d`
and records monotonicity of the infinite-volume free energy under enlarging the ambient
graph. The `inducedGraph` identity at `⊥` proved here is the base case for that comparison.
-/

namespace IsingModel
namespace Ambient

/-- **`⊥` ≤ `latticeGraph d` freeEnergyInfinite monotonicity** on ℤ^d. -/
theorem freeEnergyInfinite_bot_le_latticeGraph
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    [∀ n, Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ))
      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    freeEnergyInfinite (⊥ : SimpleGraph (Fin d → ℤ))
        (Ambient.cubicExhaustion d) p
      ≤ freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p := by
  refine freeEnergyInfinite_monotone_ambient_subgraph (G₂ := IsingModel.latticeGraph d)
    bot_le (Ambient.cubicExhaustion d) p hf (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **ℤ^d freeEnergyInfinite ambient-subgraph monotonicity** up to
`latticeGraph d` (ferromagnetic, `cubicExhaustion`): for any
`G₁ ≤ latticeGraph d`, `freeEnergyInfinite G₁ Λ p ≤
freeEnergyInfinite (latticeGraph d) Λ p`. BED supplied by
`inducedLatticeGraph_card_edgeFinset_le`. -/
theorem freeEnergyInfinite_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    {G₁ : SimpleGraph (Fin d → ℤ)} (hG : G₁ ≤ IsingModel.latticeGraph d)
    [∀ n, Fintype (Ambient.inducedGraph G₁
      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    freeEnergyInfinite G₁ (Ambient.cubicExhaustion d) p
      ≤ freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p := by
  refine freeEnergyInfinite_monotone_ambient_subgraph (G₂ := IsingModel.latticeGraph d)
    hG (Ambient.cubicExhaustion d) p hf (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **ℤ^d inducedGraph of `⊥` = `⊥`** on any Λ. -/
@[simp]
theorem inducedGraph_latticeGraph_bot (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ)) Λ = ⊥ :=
  Ambient.inducedGraph_bot Λ

/-- **ℤ^d `log Z_{Λ_n}` ambient-subgraph `⊥ ≤ latticeGraph d`** per stage
(ferromagnetic, `cubicExhaustion`). -/
theorem log_partitionFunctionAlongExhaustion_bot_le_latticeGraph
    (d : ℕ)
    [∀ n, Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ))
      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion
        (⊥ : SimpleGraph (Fin d → ℤ)) (Ambient.cubicExhaustion d) p n)
      ≤ Real.log (partitionFunctionAlongExhaustion
          (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p n) :=
  Real.log_le_log
    (partitionFunctionAlongExhaustion_pos _ (Ambient.cubicExhaustion d) p n)
    (partitionFunctionAlongExhaustion_bot_le_latticeGraph d p hf n)

/-- **`⊥` ≤ `latticeGraph d` correlation monotonicity** on ℤ^d:
`correlationInfinite ⊥ Λ p A ≤ correlationInfinite (latticeGraph d) Λ p A`
(ferromagnetic). Any two ambient graphs with `⊥ ≤ G` give ambient-subgraph
monotonicity. Here we instantiate at `⊥ ≤ latticeGraph d`. -/
theorem correlationInfinite_bot_le_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ))
      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ)) :
    correlationInfinite (⊥ : SimpleGraph (Fin d → ℤ)) Λ p A
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p A :=
  correlationInfinite_monotone_ambient_subgraph bot_le Λ p hf A

end Ambient

end IsingModel
