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
# ℤ^d ambient-subgraph monotonicity + `⊥ ≤ latticeGraph` wrappers

Narrow child module for 24 ℤ^d wrappers covering ambient-subgraph
monotonicity from `⊥` to `latticeGraph d`, including:

- `inducedGraph_latticeGraph_bot` identity;
- `*_bot_le_latticeGraph` lower bounds for
  `{free,partition}EnergyAlongExhaustion`,
  `correlationAlongExhaustion`, `partitionFunctionΛ`,
  `freeEnergyΛ`, `correlationΛ`, `log_partitionFunction*`,
  `magnetization{Λ,AlongExhaustion,Infinite}`, and
  `spontaneous{Correlation,Magnetization}`;
- `*_latticeGraph_monotone_ambient_subgraph` for the same families.

Theorem names are unchanged from the former `TwoPoint`
declarations.
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

/-- **`⊥` ≤ `latticeGraph d` magnetizationΛ monotonicity** on ℤ^d. -/
theorem magnetizationΛ_bot_le_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ)) Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : ↑Λ) :
    magnetizationΛ (⊥ : SimpleGraph (Fin d → ℤ)) Λ p i
      ≤ magnetizationΛ (IsingModel.latticeGraph d) Λ p i :=
  magnetizationΛ_monotone_ambient_subgraph bot_le Λ p hf i

/-- **`⊥` ≤ `latticeGraph d` magnetizationAlongExhaustion monotonicity**
per stage on ℤ^d. -/
theorem magnetizationAlongExhaustion_bot_le_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ))
      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (⊥ : SimpleGraph (Fin d → ℤ)) Λ p i n
      ≤ magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n :=
  magnetizationAlongExhaustion_monotone_ambient_subgraph bot_le Λ p hf i n

/-- **`⊥` ≤ `latticeGraph d` magnetizationInfinite monotonicity** on ℤ^d. -/
theorem magnetizationInfinite_bot_le_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ))
      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    magnetizationInfinite (⊥ : SimpleGraph (Fin d → ℤ)) Λ p i
      ≤ magnetizationInfinite (IsingModel.latticeGraph d) Λ p i :=
  magnetizationInfinite_monotone_ambient_subgraph bot_le Λ p hf i

/-- **`⊥` ≤ `latticeGraph d` spontaneousCorrelation monotonicity** on ℤ^d. -/
theorem spontaneousCorrelation_bot_le_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ))
      (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation (⊥ : SimpleGraph (Fin d → ℤ)) Λ J β A
      ≤ spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A :=
  spontaneousCorrelation_monotone_ambient_subgraph bot_le Λ hJ hβ A

/-- **`⊥` ≤ `latticeGraph d` spontaneousMagnetization monotonicity** on ℤ^d. -/
theorem spontaneousMagnetization_bot_le_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ))
      (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    spontaneousMagnetization (⊥ : SimpleGraph (Fin d → ℤ)) Λ J β i
      ≤ spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i :=
  spontaneousMagnetization_monotone_ambient_subgraph bot_le Λ hJ hβ i

end Ambient

end IsingModel
