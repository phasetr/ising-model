import IsingModel.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Free-energy and partition-function bounds at finite volume in ℤ^d

Records the crude energy bounds for the subgraph induced by the nearest-neighbor lattice
graph on a finite `Λ ⊆ ℤ^d`: the partition function is at least
`exp(-|β|·(|J|·|E| + |h|·|Λ|))` and at most the number of configurations times
`exp(|β|·(|J|·|E| + |h|·|Λ|))`, and the free energy per site is at most
`log 2 + |β|·(|J|·|E| + |h|·|Λ|) / |Λ|`. Only the free-energy statement requires `Λ` to
carry at least one site, since it divides by the site count; the partition-function bounds
hold at an arbitrary parameter record and an arbitrary `Λ`.
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
