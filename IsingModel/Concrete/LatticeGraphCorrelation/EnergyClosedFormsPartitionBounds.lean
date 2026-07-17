import IsingModel.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d partition / freeEnergy bound wrappers

Narrow child module for three ℤ^d
`partitionFunction_{upper,lower}_latticeGraph` and
`freeEnergy_upper_bound_latticeGraph` wrappers extracted from
`EnergyClosedForms.lean`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d partitionFunction_upper direct** (Λ-induced):
`Z ≤ 2^|Λ| · exp(|β|·(|J|·|E|_Λ + |h|·|Λ|))` (GJ §10.3, Cor 10.3.2).
Thin pass-through of `IsingModel.partitionFunction_upper`. -/
theorem partitionFunction_upper_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p
      ≤ Fintype.card (IsingModel.Config (↑Λ : Type _)) *
          Real.exp (|p.β| *
            (|p.J| *
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
              + |p.h| * Fintype.card (↑Λ : Type _))) :=
  IsingModel.partitionFunction_upper
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d partitionFunction_lower direct** (Λ-induced):
`exp(-|β|·(|J|·|E|_Λ + |h|·|Λ|)) ≤ Z`. Thin pass-through of
`IsingModel.partitionFunction_lower`. -/
theorem partitionFunction_lower_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    Real.exp (-(|p.β| *
        (|p.J| *
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
          + |p.h| * Fintype.card (↑Λ : Type _))))
      ≤ IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.partitionFunction_lower
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d freeEnergy_upper_bound direct** (Λ-induced, nonempty `Λ`):
`f ≤ log 2 + |β|·(|J|·|E|_Λ + |h|·|Λ|) / |Λ|` (GJ §10.3). Thin
pass-through of `IsingModel.freeEnergy_upper_bound`. -/
theorem freeEnergy_upper_bound_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hne : 0 < Fintype.card (↑Λ : Type _)) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p
      ≤ Real.log 2 +
          |p.β| *
            (|p.J| *
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
              + |p.h| * Fintype.card (↑Λ : Type _))
          / Fintype.card (↑Λ : Type _) :=
  IsingModel.freeEnergy_upper_bound
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hne

end Ambient
end IsingModel
