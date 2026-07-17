import IsingModel.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d freeEnergyΛ / partitionFunctionΛ upper / lower bounds

Narrow child module for three ℤ^d Λ-layer free-energy and
partition-function bound wrappers extracted from
`FiniteVolumeEnergyBounds.lean`:

* `freeEnergyΛ_latticeGraph_upper_bound`,
* `partitionFunctionΛ_latticeGraph_upper`,
* `partitionFunctionΛ_latticeGraph_lower`.

Each result is a thin pass-through of the corresponding abstract
`IsingModel.*` lemma on the Λ-induced graph at
`IsingModel.latticeGraph d`. The theorem names are unchanged from
the former `FiniteVolumeEnergyBounds` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `freeEnergyΛ` upper bound** at nonempty Λ-induced subgraph:
`f_Λ ≤ log 2 + |β|·(|J|·|E| + |h|·|Λ|) / |Λ|`. -/
theorem freeEnergyΛ_latticeGraph_upper_bound
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ p
      ≤ Real.log 2 + |p.β| * (|p.J|
          * (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
          + |p.h| * Fintype.card (↑Λ : Type _))
        / Fintype.card (↑Λ : Type _) :=
  IsingModel.freeEnergy_upper_bound
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hne

/-- **ℤ^d `partitionFunctionΛ` upper bound** at Λ-induced subgraph:
`Z ≤ |Config| · exp(|β|·(|J|·|E| + |h|·|Λ|))`. -/
theorem partitionFunctionΛ_latticeGraph_upper
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ p
      ≤ Fintype.card (IsingModel.Config (↑Λ : Type _))
        * Real.exp (|p.β| * (|p.J|
            * (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
          + |p.h| * Fintype.card (↑Λ : Type _))) :=
  IsingModel.partitionFunction_upper
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d `partitionFunctionΛ` lower bound** at Λ-induced subgraph:
`exp(-|β|·(|J|·|E| + |h|·|Λ|)) ≤ Z`. -/
theorem partitionFunctionΛ_latticeGraph_lower
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    Real.exp (-(|p.β| * (|p.J|
          * (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
        + |p.h| * Fintype.card (↑Λ : Type _))))
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  IsingModel.partitionFunction_lower
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

end Ambient
end IsingModel
