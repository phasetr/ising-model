import IsingModel.AmbientLattice.Monotonicity.AmbientSubgraph
import IsingModel.AmbientLattice.CorrelationInfinite.AmbientSubgraph
import IsingModel.AmbientLattice.MagnetizationInfinite.Basic
import IsingModel.AmbientLattice.SpontaneousMono
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Comparison of the edgeless ambient graph with ℤ^d for magnetization and spontaneous values

Concrete statements comparing the edgeless graph `⊥` on `Fin d → ℤ` with
`IsingModel.latticeGraph d`: at an arbitrary finite subset for the finite-volume
magnetization, and at an arbitrary `Ambient.Exhaustion` of `Fin d → ℤ` for everything else.
Each value is no larger at `⊥` than at the lattice, and each statement is the ambient
subgraph-monotonicity statement instantiated at `bot_le`.

The magnetization statements assume `Ferromagnetic` on the parameter record. The
spontaneous correlation of a finite site set and the spontaneous magnetization at a site
take the coupling and the inverse temperature separately instead, and assume the coupling
non-negative and the inverse temperature positive. Every statement takes one instance
argument on the `⊥` side — a `Fintype` on the edge set `⊥` induces at the fixed finite
subset, or a stagewise one along the exhaustion — and none on the lattice side.
-/

namespace IsingModel
namespace Ambient

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
